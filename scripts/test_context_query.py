"""End-to-end evidence binding and deliberate misuse controls for the N5 query."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import build_n5_context as context
import query_context as query


class QueryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = query.load_context()
        cls.saved = query.explain_claim(context.SAVED_CLAIM_ID, cls.data)

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
            self.assertEqual(file.read_bytes(), original, "checker must preserve the original proposal")
            self.assertNotIn("claim", report, "unsupported input must not be returned as a validated claim")

    def test_explain_uses_page_claim_and_exact_named_lemmas(self):
        result, exported = self.cli("explain", context.SAVED_CLAIM_ID)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(exported["claim"], self.data["claims"][0])
        lemmas = exported["claim"]["applicable_lemmas"]
        self.assertEqual([lemma["theorem"] for lemma in lemmas], [
            "FiniteCongruenceChecks.N5.all_relations", "FiniteCongruenceChecks.N5.order_exact",
            "FiniteCongruenceChecks.N5.theta_injective"])
        for lemma in lemmas:
            ref = lemma["citations"][0]
            source = query.ROOT / ref["path"]
            line = source.read_text(encoding="utf-8").splitlines()[ref["line"] - 1]
            self.assertIn("theorem " + lemma["theorem"].split(".")[-1], line)
            self.assertEqual(ref["sha256"], context.digest(source))
            self.assertEqual(lemma["construction_id"], context.SAVED_CONSTRUCTION_ID)

    def test_both_exports_round_trip_including_utf8_file(self):
        for identifier in query.N5_CLAIM_IDS:
            with self.subTest(identifier=identifier), tempfile.TemporaryDirectory() as folder:
                file = Path(folder) / "claim.json"
                result, exported = self.cli("explain", identifier, "--out", file)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(query.read_json(file), exported)
                result, checked = self.cli("check", file)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(checked["status"], "supported")
                self.assertEqual(checked["mismatch_paths"], [])

    def test_compare_preserves_both_evidence_statuses_and_exact_bijection(self):
        result, answer = self.cli("compare")
        self.assertEqual(result.returncode, 0, result.stderr)
        comparison = answer["comparison"]
        self.assertEqual(comparison, self.data["atlas_relation"])
        self.assertEqual(comparison["saved_to_atlas"], [1, 3, 2, 0])
        self.assertEqual(comparison["transformed_saved_operations"], [[2, 3, 0, 1], [3, 1, 1, 3]])
        self.assertEqual(comparison["atlas_operations"], [[1, 3, 3, 1], [2, 3, 0, 1]])
        self.assertTrue(comparison["inclusion_order_preserved"])
        self.assertFalse(comparison["formal_proof_transferred"])
        saved, atlas = answer["claims"]
        self.assertEqual(saved["evidence_status"], "lean_proof_with_recorded_kernel_replay")
        self.assertEqual(atlas["evidence_status"], "exhaustive_computation_independently_checked")
        self.assertEqual(atlas["applicable_lemmas"], [])
        self.assertNotEqual(saved["construction_id"], atlas["construction_id"])
        self.assertEqual(atlas["values"]["operations"], comparison["atlas_operations"])
        self.assertTrue({"evidence/atlas.json", "evidence/atlas-review.json"} <=
                        {c["path"] for c in atlas["citations"]})

    def test_changed_rule_with_same_five_groupings_is_still_unsupported(self):
        proposed = copy.deepcopy(self.saved)
        proposed["claim"]["values"]["operations"][1] = [1, 0, 1, 0]  # f composed with g
        # A separately phrased block-image oracle confirms that the visible
        # classification has not changed. Matching the diagram is insufficient.
        for row in self.data["partition_audit"]:
            p = row["partition"]
            blocks = [{i for i in range(4) if p[i] == label} for label in set(p)]
            valid = all(any({op[x] for x in block} <= target for target in blocks)
                        for op in proposed["claim"]["values"]["operations"] for block in blocks)
            self.assertEqual(valid, row["valid"])
        self.assert_unsupported(proposed, "/claim/values/operations/1/0")

    def test_swapped_construction_id_is_unsupported(self):
        proposed = copy.deepcopy(self.saved)
        proposed["claim"]["construction_id"] = context.ATLAS_CONSTRUCTION_ID
        self.assert_unsupported(proposed, "/claim/construction_id")

    def test_unrelated_real_theorem_in_same_hashed_file_is_unsupported(self):
        proposed = copy.deepcopy(self.saved)
        lemma = proposed["claim"]["applicable_lemmas"][0]
        lemma["theorem"] = "FiniteCongruenceChecks.B3.all_relations"
        ref = lemma["citations"][0]
        ref["line"] = 210
        ref["url"] = ref["url"].split("#")[0] + "#L210"
        self.assertEqual(context.digest(query.ROOT / ref["path"]), ref["sha256"])
        self.assert_unsupported(proposed, "/claim/applicable_lemmas/0/theorem")

    def test_changed_assumptions_conclusion_and_missing_evidence_are_unsupported(self):
        for field in ("assumptions", "limits", "citations", "applicable_lemmas"):
            with self.subTest(field=field):
                proposed = copy.deepcopy(self.saved)
                proposed["claim"][field] = []
                self.assert_unsupported(proposed, "/claim/" + field)
        proposed = copy.deepcopy(self.saved)
        proposed["claim"]["statement"] = "Every four-point algebra has congruence lattice N5."
        self.assert_unsupported(proposed, "/claim/statement")

    def test_booleans_and_floats_cannot_impersonate_integer_inputs(self):
        for replacement in (True, 1.0):
            with self.subTest(replacement=replacement):
                proposed = copy.deepcopy(self.saved)
                proposed["claim"]["values"]["operations"][0][0] = replacement
                self.assert_unsupported(proposed, "/claim/values/operations/0/0")

    def test_unknown_claim_does_not_fall_back_to_shape_name(self):
        result, error = self.cli("explain", "N5")
        self.assertEqual(result.returncode, 2)
        self.assertFalse(result.stdout)
        self.assertIn("unknown claim id", error["error"])
        proposed = copy.deepcopy(self.saved)
        proposed["claim"]["id"] = "construction:N5"
        self.assert_unsupported(proposed, "/claim/id")

    def test_stale_page_record_fails_closed_without_rebuilding(self):
        original = Path.read_text
        for output in context.OUTPUTS:
            with self.subTest(output=output):
                def altered(path, *args, **kwargs):
                    text = original(path, *args, **kwargs)
                    return text + " " if path == query.ROOT / output else text
                with patch.object(Path, "read_text", altered), self.assertRaisesRegex(ValueError, "stale context"):
                    query.load_context()

    def test_bad_json_duplicate_keys_and_invalid_cli_return_json_errors(self):
        for text in ("{", '{"claim": {}, "claim": {}}', '{"claim": NaN}'):
            with self.subTest(text=text), tempfile.TemporaryDirectory() as folder:
                file = Path(folder) / "bad.json"
                file.write_text(text, encoding="utf-8")
                result, error = self.cli("check", file)
                self.assertEqual(result.returncode, 2)
                self.assertFalse(result.stdout)
                self.assertEqual(error["status"], "error")
        result, error = self.cli("explain")
        self.assertEqual(result.returncode, 2)
        self.assertFalse(result.stdout)
        self.assertEqual(error["status"], "error")


if __name__ == "__main__":
    unittest.main()
