"""Regression tests for the saved TM atlas projection and evidence boundaries.

These tests check computational records and local replay admission. They are
not a proof of the Python translation or of a general machine equivalence.
"""
from __future__ import annotations

import copy
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("tm_atlas_under_test", ROOT / "scripts/tm_atlas.py")
tm = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(tm)


def resolve_pointer(value, pointer):
    if pointer == "":
        return value
    if not pointer.startswith("/"):
        raise ValueError("JSON pointer must start with /")
    for part in pointer[1:].split("/"):
        token = part.replace("~1", "/").replace("~0", "~")
        value = value[int(token)] if isinstance(value, list) else value[token]
    return value


def citations(value):
    if isinstance(value, dict):
        for key, child in value.items():
            if key == "citations":
                yield from child
            else:
                yield from citations(child)
    elif isinstance(value, list):
        for child in value:
            yield from citations(child)


class TMAtlasTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # One complete real offline replay, including executable/archive hashes.
        cls.dataset, cls.outputs = tm.expected_outputs(ROOT)
        tm.verify_outputs(ROOT, cls.outputs)
        cls.trace_data = json.loads(cls.outputs[tm.TRACE_PATH])

    def test_four_pair_identities_twelve_claims_and_scope(self):
        shorts = ("tiny-stay", "bb2", "bb3", "bb4")
        self.assertEqual([p["id"] for p in self.dataset["pairs"]],
                         [f"tm-pair:{name}:v1" for name in shorts])
        self.assertEqual({c["id"] for c in self.dataset["claims"]},
                         {f"tm:{name}:{prop}:v1" for name in shorts for prop in tm.PROPERTIES})
        for claim in self.dataset["claims"]:
            self.assertEqual(claim["kind"], "tm_pair_observation")
            self.assertEqual(claim["evidence_status"], "saved_native_execution_cross_checked_with_python")
            self.assertIn("blank input", claim["scope"])
            self.assertIn("not general machine equivalence", " ".join(claim["limits"]))
            self.assertIn("no Lean theorem", " ".join(claim["limits"]))

    def test_known_results_distinguish_three_properties(self):
        # Explicit expected results, independent of the implementation's table
        # simulator: same halting time does not settle either other property.
        expected = {
            "tiny-stay": (1, (0, 0), ([], [[0, 1]])),
            "bb2": (6, (-1, 0), ([[i, 1] for i in range(-2, 2)],) * 2),
            "bb3": (14, (1, 2), ([[i, 1] for i in range(-1, 5)],) * 2),
            "bb4": (107, (-10, -9), ([[i, 1] for i in range(-8, 4)],
                                    [[-10, 1]] + [[i, 1] for i in range(-8, 4)])),
        }
        for short, (halt, heads, tapes) in expected.items():
            claims = {c["property"]: c for c in tm.query(self.dataset, f"tm-pair:{short}:v1")}
            for prop, left, right in (("halting_time", halt, halt),
                                      ("head_position", *heads), ("tape", *tapes)):
                with self.subTest(pair=short, property=prop):
                    self.assertEqual(claims[prop]["observation"],
                                     {"left": left, "right": right, "equal": left == right})

    def test_every_trace_record_matches_exact_source_line_and_input(self):
        line_cache = {path: (ROOT / path).read_text(encoding="utf-8").splitlines()
                      for path in (tm.INPUT_PATH, tm.NATIVE_PATH)}
        for pair in self.dataset["pairs"]:
            self.assertEqual(pair["input"], [])
            for name in ("left", "right"):
                side = pair[name]
                self.assertEqual(len(side["trace"]), side["first_halt"] + 2)
                self.assertEqual(len(side["trace_sources"]), len(side["trace"]))
                for step, (record, source) in enumerate(zip(side["trace"], side["trace_sources"])):
                    self.assertEqual(record["steps"], step)
                    self.assertEqual(record["id"], f"{side['case_id']}/step-{step}")
                    self.assertEqual(json.loads(line_cache[source["path"]][source["line"] - 1]), record)
                    input_source = source["input_source"]
                    original = json.loads(line_cache[input_source["path"]][input_source["line"] - 1])
                    self.assertEqual(original, {"id": record["id"], "steps": step,
                                                "machine": side["machine"], "input": []})
                    for locator in (source, input_source):
                        self.assertEqual(locator["sha256"], tm.raw_digest(ROOT / locator["path"]))
                        self.assertEqual(locator["source_commit"], tm.SOURCE_COMMIT)
                        self.assertEqual(locator["url"], tm.SOURCE_URL + locator["path"] + f"#L{locator['line']}")
                self.assertTrue(all(not record["halted"] for record in side["trace"][:side["first_halt"]]))
                self.assertEqual(side["final"], side["trace"][side["first_halt"]])

    def test_citation_pointers_and_source_hashes_resolve_without_self_hash(self):
        cache = {}
        for cite in citations(self.dataset):
            self.assertNotEqual(cite["path"], tm.DATA_PATH)
            self.assertFalse(Path(cite["path"]).is_absolute())
            self.assertNotIn("..", Path(cite["path"]).parts)
            self.assertEqual(cite["sha256"], tm.digest(ROOT / cite["path"]))
            data = cache.setdefault(cite["path"], tm.read_json(ROOT, cite["path"]))
            resolve_pointer(data, cite["json_pointer"])
        for source in self.dataset["sources"].values():
            self.assertEqual(source["sha256"], tm.digest(ROOT / source["path"]))

    def test_first_halt_claims_cite_complete_prefixes_and_exact_identity(self):
        for i, pair in enumerate(self.dataset["pairs"]):
            claim, = tm.query(self.dataset, pair["id"], "halting_time")
            pointers = {c["json_pointer"] for c in claim["citations"] if c["path"] == tm.TRACE_PATH}
            self.assertIn(f"/pairs/{i}/input", pointers)
            for side in ("left", "right"):
                self.assertIn(f"/pairs/{i}/{side}/trace", pointers)
                self.assertIn(f"/pairs/{i}/{side}/machine", pointers)

    def test_lemma_applicability_hypotheses_hold_for_concrete_transition(self):
        for pair in self.dataset["pairs"]:
            for application in pair["applicable_lemmas"]:
                side = pair[application["side"]]
                before = side["trace"][application["at_steps"]["before"]]
                after = side["trace"][application["at_steps"]["after"]]
                machine = side["machine"]
                self.assertEqual(application["case_id"], side["case_id"])
                source = application["source"]
                line = (ROOT / source["path"]).read_text(encoding="utf-8").splitlines()[source["line"] - 1]
                name = application["theorem"].rsplit(".", 1)[-1]
                self.assertTrue(line.startswith("theorem " + name + " "))
                self.assertEqual(source["sha256"], tm.raw_digest(ROOT / source["path"]))
                if name == "halted_fixed":
                    self.assertTrue(before["halted"])
                    self.assertEqual({k: before[k] for k in ("state", "head", "tape", "halted")},
                                     {k: after[k] for k in ("state", "head", "tape", "halted")})
                    continue
                self.assertFalse(before["halted"])
                tape = dict(before["tape"])
                index = before["state"] * (machine["n_alphabet_minus_one"] + 1) + tape.get(before["head"], 0)
                rule = machine["table"][index] if index < len(machine["table"]) else None
                if name == "missing_instruction":
                    self.assertIsNone(rule)
                    self.assertEqual(after["state"], machine["n_states_minus_one"] + 1)
                    self.assertEqual((after["head"], after["tape"]), (before["head"], before["tape"]))
                else:
                    self.assertIsNotNone(rule)
                    self.assertEqual(dict(after["tape"]).get(before["head"], 0), rule[1])
                    self.assertEqual(after["head"], before["head"] + rule[2] - 1)
                    self.assertEqual(after["state"], rule[0])

    def test_tiny_missing_lemma_is_cited_at_its_actual_applicability_record(self):
        claim, = tm.query(self.dataset, "tm-pair:tiny-stay:v1", "tape")
        matches = [item for item in claim["applicable_lemmas"]
                   if item["theorem"] == "TMOracle.Checks.missing_instruction"]
        self.assertEqual(len(matches), 1)
        item = matches[0]
        self.assertEqual((item["side"], item["case_id"], item["at_steps"]),
                         ("left", "missing-rule", {"before": 0, "after": 1}))
        self.assertEqual(item["citations"][0]["json_pointer"], "/pairs/0/applicable_lemmas/0")
        self.assertIn(item["citations"][0], claim["citations"])
        self.assertIn("is none", " ".join(item["conditions"]))

    def test_filters_and_returned_claims_are_independent_copies(self):
        self.assertEqual(len(tm.query(self.dataset)), 12)
        self.assertEqual(len(tm.query(self.dataset, property="tape")), 4)
        selected = tm.query(self.dataset, "tm-pair:bb2:v1", "tape")
        self.assertEqual([c["id"] for c in selected], ["tm:bb2:tape:v1"])
        selected[0]["observation"]["left"].clear()
        self.assertEqual(len(tm.query(self.dataset, "tm-pair:bb2:v1", "tape")[0]["observation"]["left"]), 4)

    def test_unknown_and_malicious_filters_fail(self):
        for bad in ("bb2", "tm-pair:bb5:v1", "../../secrets", "__proto__", [], 1, True):
            with self.subTest(pair=bad), self.assertRaises(ValueError):
                tm.query(self.dataset, pair_id=bad)
        for bad in ("state", "equivalent", "../head_position", {}, 1, True):
            with self.subTest(property=bad), self.assertRaises(ValueError):
                tm.query(self.dataset, property=bad)

    def test_json_duplicates_nonfinite_and_wrong_schema_fail(self):
        for text in ('{"id":"x","id":"y"}', '{"x":NaN}', '{"x":Infinity}', '{'):
            with self.subTest(text=text), self.assertRaises(ValueError):
                tm.parse_json(text)
        for version in (True, 2, "1"):
            altered = copy.deepcopy(self.dataset)
            altered["schema_version"] = version
            with self.subTest(version=version), self.assertRaisesRegex(ValueError, "unsupported"):
                tm.query(altered)

    def test_pinned_sources_cannot_drift_while_retaining_v1_urls(self):
        for source, expected in tm.PINNED_SOURCE_SHA256.items():
            self.assertEqual(tm.raw_digest(ROOT / source), expected)
            def changed_digest(path):
                return "0" * 64 if path == ROOT / source else tm.PINNED_SOURCE_SHA256[path.relative_to(ROOT).as_posix()]
            with self.subTest(source=source), patch.object(tm, "raw_digest", side_effect=changed_digest):
                with patch.object(tm, "replay_evidence") as replay:
                    with self.assertRaisesRegex(ValueError, "pinned TM atlas source changed"):
                        tm.expected_outputs(ROOT)
                    replay.assert_not_called()

    def test_canonical_and_offline_copies_detect_tampering(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for path, content in self.outputs.items():
                target = root / path
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(content)
            for path in tm.OUTPUTS:
                target = root / path
                original = target.read_bytes()
                target.write_bytes(original + b" ")
                with self.subTest(path=path), self.assertRaisesRegex(ValueError, "stale or altered"):
                    tm.verify_outputs(root, self.outputs)
                target.write_bytes(original)
            for field, value in (("observation", {"left": 0, "right": 0, "equal": True}),
                                 ("evidence_status", "formally_proved"),
                                 ("citations", [{"path": "../../other.json", "json_pointer": "", "sha256": "0" * 64}])):
                altered = copy.deepcopy(self.dataset)
                altered["claims"][0][field] = value
                (root / tm.DATA_PATH).write_bytes(tm.encode(altered))
                with self.subTest(field=field), patch.object(tm, "expected_outputs", return_value=(self.dataset, self.outputs)):
                    with self.assertRaisesRegex(ValueError, "stale or altered"):
                        tm.load_dataset(root)
            (root / tm.DATA_PATH).write_bytes(self.outputs[tm.DATA_PATH])
            (root / tm.TRACE_PATH).unlink()
            with patch.object(tm, "expected_outputs", return_value=(self.dataset, self.outputs)):
                with self.assertRaises(FileNotFoundError):
                    tm.load_dataset(root)

    def test_raw_native_tampering_fails_even_if_receipt_hash_is_updated(self):
        # Exercise the REAL replay on an isolated copy, including binary bytes.
        # A replacement hash cannot turn an incorrect trace into valid evidence.
        receipt = tm.read_json(ROOT, tm.RECEIPT_PATH)
        paths = set(receipt["source_sha256"])
        paths.update("evidence/tm-port-v1/" + p for p in receipt["artifacts"])
        paths.update((tm.RECEIPT_PATH, "lean/tm/source/Machine.definitions.txt"))
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for path in paths:
                target = root / path
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / path, target)
            lines = (root / tm.NATIVE_PATH).read_text(encoding="utf-8").splitlines()
            record = json.loads(lines[1])
            record["head"] = 123
            lines[1] = json.dumps(record)
            (root / tm.NATIVE_PATH).write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
            with self.assertRaisesRegex(ValueError, "artifact mismatch"):
                tm.replay_evidence(root)
            receipt["artifacts"]["lean.jsonl"] = tm.raw_digest(root / tm.NATIVE_PATH)
            (root / tm.RECEIPT_PATH).write_bytes(tm.encode(receipt))
            with self.assertRaisesRegex(ValueError, "replay failed"):
                tm.replay_evidence(root)

    def test_real_public_cli_returns_only_selected_json_claim(self):
        completed = subprocess.run([sys.executable, str(ROOT / "scripts/query_atlas.py"), "tm",
                                    "--pair", "tm-pair:bb4:v1", "--property", "head_position"],
                                   capture_output=True, text=True, encoding="utf-8", check=False, timeout=90)
        self.assertEqual(completed.returncode, 0, completed.stderr)
        envelope = json.loads(completed.stdout)
        self.assertEqual(envelope["schema_version"], 1)
        self.assertEqual([c["id"] for c in envelope["results"]], ["tm:bb4:head_position:v1"])


if __name__ == "__main__":
    unittest.main()
