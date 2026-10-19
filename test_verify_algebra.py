"""Reject ambiguous schemas and retain JSON evidence for unreadable inputs."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import verify_algebra

ROOT = Path(__file__).resolve().parent


class AlgebraVerifierTests(unittest.TestCase):
    def test_labels_must_be_a_list_and_name_must_be_text(self):
        original = json.loads((ROOT / "evidence" / "C3-witness.json").read_text(encoding="utf-8"))
        for bad in ["012", {"0": 0, "1": 1, "2": 2}]:
            damaged = copy.deepcopy(original)
            damaged["lattice"]["elements"] = bad
            with self.assertRaises(ValueError):
                verify_algebra.verify(damaged)
        for bad in ["", None, 3]:
            damaged = copy.deepcopy(original)
            damaged["lattice"]["name"] = bad
            with self.assertRaises(ValueError):
                verify_algebra.verify(damaged)

    def test_missing_input_replaces_stale_success_with_failure_report(self):
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            output = folder / "result.json"
            output.write_text('{"passed": true}', encoding="utf-8", newline="\n")
            process = subprocess.run([sys.executable, str(ROOT / "verify_algebra.py"),
                                      str(ROOT / "evidence" / "C2-witness.json"),
                                      str(folder / "missing.json"), "--out", str(output)],
                                     capture_output=True, text=True)
            self.assertEqual(process.returncode, 1, process.stdout + process.stderr)
            result = json.loads(output.read_text(encoding="utf-8"))
            self.assertFalse(result["passed"])
            self.assertEqual([row["passed"] for row in result["certificates"]], [True, False])
            self.assertIsNone(result["certificates"][1]["sha256"])

    def test_self_check_detects_broken_partition_enumerator_under_optimization(self):
        code = "import verify_algebra as m; m.partitions=lambda n: iter(()); m.self_check()"
        process = subprocess.run([sys.executable, "-O", "-c", code], cwd=ROOT,
                                 capture_output=True, text=True)
        self.assertNotEqual(process.returncode, 0)
        self.assertIn("AssertionError", process.stderr)


if __name__ == "__main__":
    unittest.main()
