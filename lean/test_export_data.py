"""Negative controls for the JSON-to-Lean data boundary."""
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("export_data", HERE / "export_data.py")
exporter = importlib.util.module_from_spec(spec)
spec.loader.exec_module(exporter)


class ExportDataTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        (self.root / "evidence").mkdir()
        for name in ("N5-witness.json", "B3-witness.json", "minimized-algebras.json"):
            (self.root / "evidence" / name).write_bytes((HERE.parent / "evidence" / name).read_bytes())

    def mutate(self, filename, change):
        path = self.root / "evidence" / filename
        data = json.loads(path.read_text())
        change(data)
        path.write_text(json.dumps(data), encoding="utf-8")

    def test_exact_reproducible_export(self):
        self.assertEqual(exporter.render(self.root), (HERE / "CertificateData.lean").read_text())

    def test_failed_minimization_cannot_export(self):
        self.mutate("minimized-algebras.json", lambda d: d.update(passed=False))
        with self.assertRaisesRegex(ValueError, "did not pass"):
            exporter.render(self.root)

    def test_changed_valid_color_cannot_reuse_old_operation_record(self):
        def swap_vertices(d):
            order = [1, 0, 2, 3]
            d["color"] = [[d["color"][i][j] for j in order] for i in order]
        self.mutate("N5-witness.json", swap_vertices)
        with self.assertRaisesRegex(ValueError, "different certificate"):
            exporter.render(self.root)

    def test_invalid_join_rejected(self):
        def bad_join(d):
            d["lattice"]["join"][1][3] = 1
        self.mutate("N5-witness.json", bad_join)
        with self.assertRaisesRegex(ValueError, "least upper bound"):
            exporter.render(self.root)

    def test_out_of_carrier_operation_rejected(self):
        def bad_op(d):
            row = next(r for r in d["certificates"] if r["certificate"] == "B3-witness.json")
            row["selected_unary_operations"][0][3] = 4
        self.mutate("minimized-algebras.json", bad_op)
        with self.assertRaisesRegex(ValueError, "two total operations"):
            exporter.render(self.root)

    def test_duplicate_operation_record_rejected(self):
        def duplicate(d):
            d["certificates"].append(copy.deepcopy(d["certificates"][0]))
        self.mutate("minimized-algebras.json", duplicate)
        with self.assertRaisesRegex(ValueError, "duplicate"):
            exporter.render(self.root)


if __name__ == "__main__":
    unittest.main()
