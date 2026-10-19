"""Regression tests for mathematical boundaries and auditable CLI failures."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import minimize_operations as minimizer

ROOT = Path(__file__).resolve().parent


class OperationMinimizerTests(unittest.TestCase):
    def test_zero_operations_means_all_equivalence_relations(self):
        for name, n in [("C2", 2), ("M3", 3)]:
            data = json.loads((ROOT / "evidence" / f"{name}-witness.json").read_text(encoding="utf-8"))
            carrier, targets = minimizer.read_targets(data)
            result = minimizer.choose_operations(carrier, targets)
            self.assertEqual(carrier, n)
            self.assertTrue(result["passed"])
            self.assertEqual(result["minimum_unary_operation_count"], 0)
            self.assertEqual(result["selected_unary_operations"], [])
            self.assertEqual(set(result["recovered_congruence_partitions"]), set(targets))

    def test_missing_unavoidable_relations_is_impossible(self):
        for targets in [[], [(0, 0)], [(0, 1)]]:
            result = minimizer.choose_operations(2, targets)
            self.assertFalse(result["passed"])
            self.assertIsNone(result["minimum_unary_operation_count"])
            self.assertFalse(result["checks"]["exact_target_congruences_recovered"])

    def test_mixed_good_missing_and_invalid_inputs_preserve_failure_evidence(self):
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            invalid = folder / "invalid.json"
            invalid.write_text("{bad JSON", encoding="utf-8", newline="\n")
            output = folder / "result.json"
            valid = ROOT / "evidence" / "C2-witness.json"
            missing = folder / "missing.json"
            process = subprocess.run([sys.executable, str(ROOT / "minimize_operations.py"),
                                      str(valid), str(missing), str(invalid), "--out", str(output)],
                                     capture_output=True, text=True)
            self.assertEqual(process.returncode, 1, process.stdout + process.stderr)
            result = json.loads(output.read_text(encoding="utf-8"))
            self.assertFalse(result["passed"])
            self.assertEqual([row["passed"] for row in result["certificates"]], [True, False, False])

    def test_output_cannot_overwrite_input_certificate(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "certificate.json"
            before = (ROOT / "evidence" / "C2-witness.json").read_bytes()
            path.write_bytes(before)
            process = subprocess.run([sys.executable, str(ROOT / "minimize_operations.py"),
                                      str(path), "--out", str(path)], capture_output=True, text=True)
            self.assertEqual(process.returncode, 2)
            self.assertEqual(path.read_bytes(), before)

    def test_invalid_lattice_name_cannot_leave_success_evidence(self):
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            data = json.loads((ROOT / "evidence" / "C2-witness.json").read_text(encoding="utf-8"))
            data["lattice"]["name"] = []
            path = folder / "certificate.json"
            path.write_text(json.dumps(data), encoding="utf-8", newline="\n")
            output = folder / "result.json"
            process = subprocess.run([sys.executable, str(ROOT / "minimize_operations.py"),
                                      str(path), "--out", str(output)], capture_output=True, text=True)
            self.assertEqual(process.returncode, 1)
            result = json.loads(output.read_text(encoding="utf-8"))
            self.assertFalse(result["passed"])
            self.assertFalse(result["certificates"][0]["passed"])

    def test_certificates_must_be_explicit(self):
        process = subprocess.run([sys.executable, str(ROOT / "minimize_operations.py")],
                                 cwd=ROOT, capture_output=True, text=True)
        self.assertEqual(process.returncode, 2)

    def test_self_check_detects_broken_partition_enumerator_under_optimization(self):
        code = "import minimize_operations as m; m.all_partitions=lambda n: []; m.self_check()"
        process = subprocess.run([sys.executable, "-O", "-c", code], cwd=ROOT,
                                 capture_output=True, text=True)
        self.assertNotEqual(process.returncode, 0)
        self.assertIn("AssertionError", process.stderr)


if __name__ == "__main__":
    unittest.main()
