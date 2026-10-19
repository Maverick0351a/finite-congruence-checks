"""Cross-domain context binding controls over one existing bounded TM claim."""
import copy
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import query_context as query
import run_tm_checks
import tm_atlas
import tm_context


class TMContextTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.record = query.explain_claim(tm_context.CLAIM_ID)
        cls.claim = cls.record["claim"]

    def cli(self, *args):
        result = subprocess.run([sys.executable, str(query.ROOT / "scripts/query_context.py"), *map(str, args)],
                                cwd=query.ROOT, capture_output=True, check=False)
        return result, json.loads(result.stdout or result.stderr)

    def assert_unsupported(self, candidate, path):
        with tempfile.TemporaryDirectory() as folder:
            file = Path(folder) / "proposed.json"
            original = query.encode(candidate)
            file.write_bytes(original)
            result, report = self.cli("check", file)
            self.assertEqual(result.returncode, 1, result.stderr)
            self.assertFalse(result.stderr)
            self.assertEqual(report["status"], "unsupported")
            self.assertIn(path, report["mismatch_paths"])
            self.assertEqual(file.read_bytes(), original)
            self.assertNotIn("claim", report)

    def assert_same_trace(self, candidate):
        # Establish that these mutations really preserve the displayed runs;
        # unchanged output alone must not authorize evidence for another input.
        for side in ("left", "right"):
            values = candidate["claim"]["values"]
            for snapshot in values[side]["trace"]:
                case = {"machine": values[side]["machine"], "input": values["input"],
                        "id": snapshot["id"], "steps": snapshot["steps"]}
                self.assertEqual(run_tm_checks.expected(case), snapshot)

    def test_preserves_original_claim_and_resolves_native_input_and_output_lines(self):
        registry = query.read_json(query.ROOT / tm_atlas.DATA_PATH)
        original = next(c for c in registry["claims"] if c["id"] == tm_context.CLAIM_ID)
        for key, value in original.items():
            self.assertEqual(self.claim[key], value, key)
        self.assertEqual(self.claim["observation"], {"left": [], "right": [[0, 1]], "equal": False})
        self.assertEqual(self.claim["construction_id"], tm_context.PAIR_ID)
        self.assertEqual(self.claim["values"]["input"], [])
        self.assertIn("does not prove the Python", self.claim["proof_status"])
        formal = self.claim["formal_supplement"]["claim"]
        self.assertEqual(formal["id"], "tm:tiny-stay:formal-result:v1")
        self.assertEqual(formal["conclusion"]["first_halt"], [1, 1])
        self.assertEqual(formal["conclusion"]["tape"]["quantifier"], "every i : Int")
        for side in ("left", "right"):
            values = self.claim["values"][side]
            self.assertEqual(values["first_halt"], 1)
            self.assertEqual(values["final"]["head"], 0)
            self.assertEqual(len(values["trace"]), 3)
            for snapshot, ref in zip(values["trace"], values["trace_sources"]):
                source = query.ROOT / ref["path"]
                self.assertEqual(tm_atlas.raw_digest(source), ref["sha256"])
                self.assertEqual(json.loads(source.read_text().splitlines()[ref["line"] - 1]), snapshot)
                inp = ref["input_source"]
                source = query.ROOT / inp["path"]
                self.assertEqual(tm_atlas.raw_digest(source), inp["sha256"])
                case = json.loads(source.read_text().splitlines()[inp["line"] - 1])
                self.assertEqual(case["machine"], values["machine"])
                self.assertEqual(case["input"], self.claim["values"]["input"])
                self.assertEqual(case["id"], snapshot["id"])
                self.assertEqual(case["steps"], snapshot["steps"])

    def test_cli_export_round_trip(self):
        with tempfile.TemporaryDirectory() as folder:
            file = Path(folder) / "tm.json"
            result, exported = self.cli("explain", tm_context.CLAIM_ID, "--out", file)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(exported, self.record)
            self.assertEqual(query.read_json(file), self.record)
            result, checked = self.cli("check", file)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(checked["status"], "supported")
            self.assertEqual(checked["mismatch_paths"], [])

    def test_formal_supplement_cannot_change_theorem_or_conclusion(self):
        for field, value in (("theorem", "TMOracle.TinyPair.left_halts_one"),
                             ("conclusion", {"first_halt": [2, 2]}),
                             ("values", {})):
            proposed = copy.deepcopy(self.record)
            proposed["claim"]["formal_supplement"]["claim"][field] = value
            self.assert_unsupported(proposed, "/claim/formal_supplement/claim/" + field if field == "theorem"
                                    else "/claim/formal_supplement/claim/" + field +
                                    ("/first_halt/0" if field == "conclusion" else "/input"))

    def test_changed_unused_rule_preserves_trace_but_loses_binding(self):
        proposed = copy.deepcopy(self.record)
        # State 0 reading symbol 1 is never reached from this blank input.
        proposed["claim"]["values"]["right"]["machine"]["table"][1] = [1, 0, 2]
        self.assert_same_trace(proposed)
        self.assert_unsupported(proposed, "/claim/values/right/machine/table/1/1")

    def test_different_encoding_of_blank_input_still_needs_its_own_binding(self):
        proposed = copy.deepcopy(self.record)
        proposed["claim"]["values"]["input"] = [0]
        self.assert_same_trace(proposed)
        self.assert_unsupported(proposed, "/claim/values/input")

    def test_pair_or_property_substitution_is_unsupported(self):
        for key, value in (("pair_id", "tm-pair:bb4:v1"), ("property", "head_position")):
            with self.subTest(key=key):
                proposed = copy.deepcopy(self.record)
                proposed["claim"][key] = value
                self.assert_unsupported(proposed, "/claim/" + key)

    def test_real_lemma_from_same_file_cannot_move_to_an_active_step(self):
        proposed = copy.deepcopy(self.record)
        lemmas = proposed["claim"]["applicable_lemmas"]
        replacement = copy.deepcopy(lemmas[1])  # Real halted_fixed source and citation.
        replacement["at_steps"] = {"before": 0, "after": 1}
        replacement["conditions"] = ["At saved step 0, M.isHalting c = true."]
        self.assertFalse(proposed["claim"]["values"]["left"]["trace"][0]["halted"])
        self.assertEqual(replacement["source"]["sha256"], lemmas[0]["source"]["sha256"])
        source = query.ROOT / replacement["source"]["path"]
        self.assertEqual(tm_atlas.raw_digest(source), replacement["source"]["sha256"])
        self.assertIn("theorem halted_fixed", source.read_text().splitlines()[replacement["source"]["line"] - 1])
        lemmas[0] = replacement
        self.assert_unsupported(proposed, "/claim/applicable_lemmas/0/theorem")

    def test_existing_trace_in_same_file_cannot_support_a_different_pair(self):
        proposed = copy.deepcopy(self.record)
        citation = proposed["claim"]["citations"][0]
        citation["json_pointer"] = "/pairs/3/left/final/tape"
        source = query.ROOT / citation["path"]
        self.assertEqual(tm_atlas.digest(source), citation["sha256"])
        self.assertTrue(query.read_json(source)["pairs"][3]["left"]["final"]["tape"])
        self.assert_unsupported(proposed, "/claim/citations/0/json_pointer")

    def test_missing_evidence_proof_upgrade_and_universal_claim_are_unsupported(self):
        changes = (("citations", []), ("applicable_lemmas", []), ("assumptions", []),
                   ("evidence_status", "lean_proof_with_recorded_kernel_replay"),
                   ("statement", "These machines are equivalent on every input."))
        for field, value in changes:
            with self.subTest(field=field):
                proposed = copy.deepcopy(self.record)
                proposed["claim"][field] = value
                self.assert_unsupported(proposed, "/claim/" + field)

    def test_domains_load_independently_and_compare_still_has_two_n5_claims(self):
        with patch.object(query, "load_context", side_effect=AssertionError("unrelated N5 load")):
            self.assertEqual(query.explain_claim(tm_context.CLAIM_ID), self.record)
        with patch.object(tm_context, "explain", side_effect=AssertionError("unrelated TM load")):
            saved = query.explain_claim(query.N5_CLAIM_IDS[0])
            self.assertEqual(saved["claim"]["id"], query.N5_CLAIM_IDS[0])
            self.assertEqual([c["id"] for c in query.compare()["claims"]], list(query.N5_CLAIM_IDS))
        result, error = self.cli("explain", "tm:tiny-stay:head_position:v1")
        self.assertEqual(result.returncode, 2)
        self.assertFalse(result.stdout)
        self.assertIn("unknown claim id", error["error"])

    def test_stale_browser_copies_fail_without_being_rewritten(self):
        read = Path.read_bytes
        for relative in ("space/tm-atlas-data.json", "space/tm-atlas-data.js"):
            with self.subTest(path=relative):
                def altered(path):
                    content = read(path)
                    return content + b" " if path == query.ROOT / relative else content
                with patch.object(Path, "read_bytes", altered), self.assertRaises(ValueError):
                    query.explain_claim(tm_context.CLAIM_ID)

    def test_replay_failure_and_timeout_return_json_error(self):
        for error in (ValueError("saved evidence replay failed"), subprocess.TimeoutExpired("replay", 90)):
            with self.subTest(error=type(error).__name__), patch.object(tm_context, "explain", side_effect=error), \
                 patch.object(sys, "stdout", io.StringIO()) as out, patch.object(sys, "stderr", io.StringIO()) as err:
                self.assertEqual(query.main(["explain", tm_context.CLAIM_ID]), 2)
                self.assertEqual(out.getvalue(), "")
                self.assertEqual(json.loads(err.getvalue())["status"], "error")


if __name__ == "__main__":
    unittest.main()
