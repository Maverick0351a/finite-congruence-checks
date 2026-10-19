"""Corruption controls for the native-comparison harness, not binary mutations."""

import copy
import gzip
import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock, patch


SCRIPT = Path(__file__).with_name("run_grouping_checks.py")
SPEC = importlib.util.spec_from_file_location("grouping_harness_under_test", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
harness = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(harness)


VALID = {"status": "checked", "word": 20640, "operation": [0, 0, 2, 2],
         "group_labels": [0, 0, 1, 1], "roundtrip_word": 20640,
         "preserves": True, "violating_pair": None}
INVALID = {"status": "checked", "word": 20648, "operation": [0, 2, 2, 2],
           "group_labels": [0, 0, 1, 1], "roundtrip_word": 20648,
           "preserves": False, "violating_pair": [0, 1]}
WORDS = [20640, 20648]


class NativeComparisonControls(unittest.TestCase):
    def check(self, records):
        return harness.validate_records(records, WORDS)

    def kinds(self, result):
        return {item["kind"] for item in result["disagreements"]}

    def test_known_records_and_different_valid_witness(self):
        reverse = copy.deepcopy(INVALID)
        reverse["violating_pair"] = [1, 0]
        result = self.check([VALID, reverse])
        self.assertEqual(result["disagreements"], [])
        self.assertTrue(result["coverage"]["expected_coverage_complete"])
        self.assertFalse(result["coverage"]["full_domain"])

    def test_missing_word_is_not_full_coverage(self):
        result = self.check([VALID])
        self.assertEqual(result["coverage"]["missing_words"], [20648])
        self.assertIn("missing_word", self.kinds(result))
        self.assertFalse(result["coverage"]["expected_coverage_complete"])

    def test_duplicate_cannot_replace_missing_word(self):
        result = self.check([VALID, VALID])
        self.assertEqual(result["coverage"]["actual_tested_count"], 2)
        self.assertEqual(result["coverage"]["distinct_word_count"], 1)
        self.assertTrue({"duplicate_word", "missing_word"} <= self.kinds(result))

    def test_corrupt_decode_and_roundtrip_are_retained_together(self):
        corrupt = copy.deepcopy(VALID)
        corrupt["operation"] = [0, 0, 0, 0]
        corrupt["group_labels"] = [0, 1, 2, 3]
        corrupt["roundtrip_word"] = 0
        result = self.check([corrupt, INVALID])
        self.assertTrue({"operation", "group_labels", "roundtrip_word"} <= self.kinds(result))

    def test_flipped_acceptance_is_rejected(self):
        corrupt = copy.deepcopy(INVALID)
        corrupt["preserves"] = True
        corrupt["violating_pair"] = None
        result = self.check([VALID, corrupt])
        self.assertTrue({"preserves", "invalid_witness"} <= self.kinds(result))

    def test_bogus_counterexamples_are_rejected(self):
        for pair in ([0, 0], [0, 2], [-1, 0], [0, 4], [False, 1], None, "0,1"):
            with self.subTest(pair=pair):
                corrupt = copy.deepcopy(INVALID)
                corrupt["violating_pair"] = pair
                self.assertIn("invalid_witness", self.kinds(self.check([VALID, corrupt])))

    def test_json_boolean_is_not_an_integer(self):
        for field, bad_value in (("word", True), ("roundtrip_word", True),
                                 ("operation", [False, 0, 2, 2]),
                                 ("group_labels", [False, 0, 1, 1]), ("preserves", 1)):
            with self.subTest(field=field):
                corrupt = copy.deepcopy(VALID)
                corrupt[field] = bad_value
                self.assertTrue(self.check([corrupt, INVALID])["disagreements"])

    def test_malformed_json_duplicate_keys_and_blank_lines_survive(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "output.jsonl"
            path.write_bytes(b'{"word":1,"word":2}\n\n{"x":NaN}\n\xff\n')
            result = harness.validate_records(harness.read_jsonl(path), [])
        self.assertEqual(result["coverage"]["total_output_records"], 4)
        self.assertEqual([item["kind"] for item in result["disagreements"]], ["invalid_json"] * 4)

    def test_axiom_reports_require_exact_eleven_and_reject_sorry(self):
        reports = [f"'{name}' depends on axioms: [propext, Quot.sound]"
                   for name in harness.EXPECTED_DECLARATIONS]
        reports[7] = f"'{harness.EXPECTED_DECLARATIONS[7]}' does not depend on any axioms"
        self.assertTrue(harness.validate_axioms("\n".join(reports))["passed"])
        for changed in (reports[:-1], reports + [reports[0]],
                        [line.replace("Quot.sound", "sorryAx") for line in reports],
                        reports + ["'Extra.theorem' does not depend on any axioms"]):
            with self.subTest(changed=changed):
                self.assertFalse(harness.validate_axioms("\n".join(changed))["passed"])

    def test_gzip_preserves_bytes_and_has_reproducible_header(self):
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            source = base / "arbitrary-name.bin"
            source.write_bytes(bytes(range(256)) * 10)
            first = harness.gzip_artifact(source, base / "one.gz")
            second = harness.gzip_artifact(source, base / "two.gz")
            self.assertEqual(first["sha256"], second["sha256"])
            self.assertEqual(gzip.decompress((base / "one.gz").read_bytes()), source.read_bytes())
            self.assertEqual((base / "one.gz").read_bytes()[4:8], bytes(4))
            self.assertEqual(first["raw_sha256"], harness.sha256(source))

    def test_nonempty_output_directory_is_never_overwritten(self):
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory)
            (target / "keep.txt").write_text("existing evidence", encoding="utf-8")
            with self.assertRaises(ValueError):
                harness.run(target, target / "absent-binary")
            self.assertEqual((target / "keep.txt").read_text(encoding="utf-8"), "existing evidence")

    def test_wrapper_mutation_is_narrow_and_fails_closed_on_changed_source(self):
        source = b'unchanged\r\n("preserves", toJson (check w)),\r\n("violating_pair", pair)\r\n'
        expected = source.replace(b'toJson (check w)', b'toJson (!(check w))')
        self.assertEqual(harness.mutate_wrapper_source(source), expected)
        for invalid in (b"unexpected wrapper", source + source):
            with self.assertRaises(ValueError):
                harness.mutate_wrapper_source(invalid)

    def test_git_prefers_native_and_converts_wsl_path_for_windows_fallback(self):
        capture = Mock()
        with patch.object(harness.shutil, "which", return_value="/usr/bin/git"):
            self.assertEqual(harness.git_prefix(capture), ["/usr/bin/git"])
            capture.run.assert_not_called()
        capture.run.return_value = {"exit_code": 0}
        capture.stdout.return_value = "C:\\repo with spaces\n"
        paths = {"git": None, "git.exe": "/mnt/c/git.exe", "wslpath": "/usr/bin/wslpath"}
        with patch.object(harness.shutil, "which", side_effect=paths.get), \
                patch.object(harness.platform, "system", return_value="Linux"):
            self.assertEqual(harness.git_prefix(capture),
                             ["/mnt/c/git.exe", "-C", "C:\\repo with spaces"])
            capture.run.assert_called_once_with("git-path-conversion", ["wslpath", "-w", str(harness.ROOT)], harness.ROOT)


if __name__ == "__main__":
    unittest.main(verbosity=2)
