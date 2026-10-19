"""Negative controls for atlas completeness, exact constructions, and grouping."""
from copy import deepcopy
from contextlib import redirect_stderr, redirect_stdout
import io
import json
from pathlib import Path
import tempfile
import unittest

from scripts import check_atlas

ROOT = Path(__file__).resolve().parents[1]


class AtlasIndependentChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.original = json.loads((ROOT / "evidence/atlas.json").read_text(encoding="utf-8"))

    def setUp(self):
        self.data = deepcopy(self.original)

    def test_complete_atlas_matches_independent_exhaustion(self):
        result = check_atlas.check(self.data)
        self.assertTrue(result["passed"])
        self.assertEqual([row["labeled_relation_families"] for row in result["carrier_summary"]],
                         [1, 1, 8, 303])
        self.assertEqual(result["total_embedding_orbits"], 39)
        self.assertEqual(result["abstract_types_across_carriers"], 22)

    def test_missing_orbit_is_rejected(self):
        self.data["entries"].pop()
        with self.assertRaisesRegex(ValueError, "incomplete embedding orbit coverage"):
            check_atlas.check(self.data)

    def test_duplicate_representative_is_rejected(self):
        duplicate = deepcopy(self.data["entries"][0])
        duplicate["id"] += "-duplicate"
        self.data["entries"].append(duplicate)
        with self.assertRaisesRegex(ValueError, "duplicate embedding orbit"):
            check_atlas.check(self.data)

    def test_wrong_operation_is_rejected(self):
        entry = next(row for row in self.data["entries"] if row["minimum_unary_operations"] == 1)
        entry["operations"] = [list(range(entry["carrier_size"]))]
        with self.assertRaisesRegex(ValueError, "operations do not recover exact family"):
            check_atlas.check(self.data)

    def test_false_operation_minimum_is_rejected(self):
        entry = next(row for row in self.data["entries"] if row["minimum_unary_operations"] == 2)
        entry["minimum_unary_operations"] = 1
        with self.assertRaisesRegex(ValueError, "incorrect minimum_unary_operations"):
            check_atlas.check(self.data)

    def test_nonisomorphic_types_cannot_be_merged(self):
        first, second = self.data["abstract_types"][:2]
        first["embedding_ids"].extend(second["embedding_ids"])
        with self.assertRaisesRegex(ValueError, "non-isomorphic embeddings grouped together"):
            check_atlas.check(self.data)

    def test_isomorphic_types_cannot_be_split(self):
        original = next(row for row in self.data["abstract_types"] if row["name"] == "C2")
        split = deepcopy(original)
        split["id"] = "T99"
        split["embedding_ids"] = [original["embedding_ids"].pop()]
        entry = next(row for row in self.data["entries"] if row["id"] == split["embedding_ids"][0])
        entry["abstract_type"] = split["id"]
        self.data["abstract_types"].append(split)
        with self.assertRaisesRegex(ValueError, "isomorphic embeddings split across types"):
            check_atlas.check(self.data)

    def test_missing_type_member_is_rejected(self):
        self.data["abstract_types"][-1]["embedding_ids"].pop()
        with self.assertRaisesRegex(ValueError, "empty or duplicate type membership"):
            check_atlas.check(self.data)

    def test_false_named_shape_is_rejected(self):
        entry = next(row for row in self.data["entries"] if row["name"] == "C4")
        entry["named_targets"] = ["B2"]
        with self.assertRaisesRegex(ValueError, "named targets do not match its poset"):
            check_atlas.check(self.data)

    def test_wrong_order_and_cover_are_rejected(self):
        self.data["entries"][0]["order"][0][0] = False
        with self.assertRaisesRegex(ValueError, "incorrect order matrix"):
            check_atlas.check(self.data)
        self.data = deepcopy(self.original)
        next(row for row in self.data["entries"] if row["covers"])["covers"].pop()
        with self.assertRaisesRegex(ValueError, "incorrect covering pairs"):
            check_atlas.check(self.data)

    def test_incomplete_source_registry_is_rejected(self):
        self.data["source_sha256"].pop(next(iter(self.data["source_sha256"])))
        with self.assertRaisesRegex(ValueError, "source_sha256 registry is incomplete"):
            check_atlas.check(self.data)

    def test_cli_fails_without_emitting_success_receipt(self):
        self.data["entries"].pop()
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "broken.json"
            receipt = Path(directory) / "review.json"
            path.write_text(json.dumps(self.data), encoding="utf-8")
            with redirect_stderr(io.StringIO()):
                status = check_atlas.main(["--atlas", str(path), "--out", str(receipt)])
            self.assertEqual(status, 1)
            self.assertFalse(receipt.exists())

    def test_stale_review_receipt_is_rejected_after_recomputation(self):
        with tempfile.TemporaryDirectory() as directory:
            receipt = Path(directory) / "review.json"
            with redirect_stdout(io.StringIO()):
                self.assertEqual(check_atlas.main(["--out", str(receipt)]), 0)
            # A Windows checkout may rewrite LF to CRLF; this remains equivalent.
            receipt.write_bytes(receipt.read_bytes().replace(b"\n", b"\r\n"))
            with redirect_stdout(io.StringIO()):
                self.assertEqual(check_atlas.main(["--check-receipt", str(receipt)]), 0)
            stale = json.loads(receipt.read_text(encoding="utf-8"))
            stale["abstract_types_across_carriers"] += 1
            receipt.write_text(json.dumps(stale, indent=2) + "\n", encoding="utf-8", newline="\n")
            output = Path(directory) / "new-review.json"
            with redirect_stderr(io.StringIO()) as error:
                status = check_atlas.main(["--check-receipt", str(receipt), "--out", str(output)])
            self.assertEqual(status, 1)
            self.assertIn("saved review receipt is stale or modified", error.getvalue())
            self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
