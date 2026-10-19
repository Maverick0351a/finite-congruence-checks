"""Exercise the real atlas CLI as a reader, including evidence citations."""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
CLI = ROOT / "scripts/query_atlas.py"


def normalized_hash(path):
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def resolve_pointer(value, pointer):
    if pointer == "":
        return value
    if not pointer.startswith("/"):
        raise ValueError(f"Invalid JSON pointer: {pointer}")
    for token in pointer[1:].split("/"):
        token = token.replace("~1", "/").replace("~0", "~")
        value = value[int(token)] if isinstance(value, list) else value[token]
    return value


def citations_in(value):
    if isinstance(value, dict):
        for key, child in value.items():
            if key == "citations":
                yield from child
            else:
                yield from citations_in(child)
    elif isinstance(value, list):
        for child in value:
            yield from citations_in(child)


class AtlasQueryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.atlas = json.loads((ROOT / "evidence/atlas.json").read_text(encoding="utf-8"))
        cls.review = json.loads((ROOT / "evidence/atlas-review.json").read_text(encoding="utf-8"))
        cls.entries = {row["id"]: row for row in cls.atlas["entries"]}
        cls.entry_indices = {row["id"]: i for i, row in enumerate(cls.atlas["entries"])}
        cls.review_entries = {row["id"]: row for row in cls.review["entries"]}

    def command(self, *arguments):
        return subprocess.run([sys.executable, str(CLI), *arguments], cwd=ROOT,
                              capture_output=True, text=True, timeout=30, check=False)

    def query(self, *arguments):
        run = self.command(*arguments)
        self.assertEqual(run.returncode, 0, run.stderr)
        data = json.loads(run.stdout)
        self.assertEqual(data["schema_version"], 1)
        self.assertEqual(data["status"], "ok")
        self.assertEqual(data["dataset"]["sha256"], normalized_hash(ROOT / "evidence/atlas.json"))
        self.assertEqual(data["review"]["sha256"], normalized_hash(ROOT / "evidence/atlas-review.json"))
        self.assertTrue(data["scope"])
        self.assertTrue(data["assumptions"])
        self.assertTrue(data["limits"])
        self.assertEqual(data["evidence_status"], "exhaustive_computation_independently_checked")
        self.assertTrue(any(word in json.dumps(data["limits"]).lower() for word in ("lean", "formal")))
        references = list(citations_in(data))
        self.assertTrue(references)
        for reference in references:
            path = ROOT / reference["path"]
            self.assertTrue(path.is_file(), reference)
            self.assertEqual(reference["sha256"], normalized_hash(path), reference)
            resolve_pointer(json.loads(path.read_text(encoding="utf-8")), reference["json_pointer"])
        return data

    def assert_entry_citation(self, data, identifier):
        self.assertTrue(any(reference["path"] == "evidence/atlas.json" and
                            reference["json_pointer"] == f"/entries/{self.entry_indices[identifier]}"
                            for reference in citations_in(data)), identifier)

    def test_complete_list_has_stable_entry_and_shape_keys(self):
        data = self.query("list")
        self.assertEqual({row["id"] for row in data["results"]}, set(self.entries))
        self.assertEqual(len(data["results"]), 39)
        for entry in data["results"]:
            expected = self.review_entries[entry["id"]]["poset_canonical_sha256"]
            self.assertEqual(entry["shape_key"], "poset-v1:" + expected)

    def test_combined_filters_select_the_one_rule_c4(self):
        data = self.query("list", "--carrier", "4", "--shape", "C4", "--min-rules", "1")
        self.assertEqual([row["id"] for row in data["results"]], ["n4-E16403"])
        entry = data["results"][0]
        self.assertEqual(entry["carrier_size"], 4)
        self.assertEqual(entry["minimum_unary_operations"], 1)
        self.assert_entry_citation(data, entry["id"])

    def test_shape_alias_and_stable_shape_key_select_same_records(self):
        named = self.query("list", "--shape", "C4")
        keyed = self.query("list", "--shape", named["results"][0]["shape_key"])
        alias = self.query("list", "--shape", "T06")
        for other in (keyed, alias):
            self.assertEqual([row["id"] for row in other["results"]],
                             [row["id"] for row in named["results"]])

    def test_show_returns_exact_construction_and_evidence(self):
        data = self.query("show", "n4-E16403")
        self.assertEqual(len(data["results"]), 1)
        result = data["results"][0]
        for field in ("id", "partitions", "operations", "minimum_unary_operations", "order", "covers"):
            self.assertEqual(result[field], self.entries["n4-E16403"][field])
        self.assert_entry_citation(data, "n4-E16403")

    def test_comparison_keeps_fixed_carrier_and_exact_family_costs(self):
        data = self.query("compare", "--shape", "C4", "--carrier", "4")
        self.assertEqual(len(data["results"]), 1)
        group = data["results"][0]
        self.assertEqual(group["carrier_size"], 4)
        self.assertTrue(group["has_different_minima"])
        self.assertEqual(group["minimum_rule_counts"], [1, 2])
        self.assertEqual({row["id"]: row["minimum_unary_operations"] for row in group["entries"]},
                         {"n4-E16403": 1, "n4-E16457": 2})
        for identifier in ("n4-E16403", "n4-E16457"):
            self.assert_entry_citation(data, identifier)
        scope = json.dumps([data["scope"], data["assumptions"], data["limits"]]).lower()
        self.assertIn("exact", scope)
        self.assertIn("fixed", scope)

    def test_default_comparison_exhausts_same_carrier_varying_shapes(self):
        data = self.query("compare")
        self.assertEqual({(group["name"], group["carrier_size"]) for group in data["results"]},
                         {("C3", 4), ("B2", 4), ("C4", 4), ("Shape T18", 4)})
        self.assertTrue(all(group["has_different_minima"] for group in data["results"]))

    def test_entry_claims_have_specific_evidence_and_scope(self):
        data = self.query("claims", "--entry", "n4-E16403")
        claims = {row["id"]: row for row in data["results"]}
        for identifier in ("construction:n4-E16403", "minimum:n4-E16403"):
            self.assertIn(identifier, claims)
            claim = claims[identifier]
            for field in ("statement", "evidence_status", "scope", "assumptions", "limits", "citations"):
                self.assertTrue(claim[field], (identifier, field))
            self.assert_entry_citation(claim, "n4-E16403")

    def test_unknown_entry_is_an_explicit_failure(self):
        for arguments in (("show", "n4-E999999"), ("claims", "--entry", "n4-E999999")):
            with self.subTest(arguments=arguments):
                run = self.command(*arguments)
                self.assertNotEqual(run.returncode, 0)
                self.assertFalse(run.stdout.strip())
                self.assertTrue(run.stderr.strip())

    def test_claim_registry_is_reproducible(self):
        run = self.command("build-claims", "--check")
        self.assertEqual(run.returncode, 0, run.stderr)

    def test_changed_atlas_cannot_reuse_a_successful_saved_review(self):
        specification = importlib.util.spec_from_file_location("atlas_query_under_test", CLI)
        query_atlas = importlib.util.module_from_spec(specification)
        specification.loader.exec_module(query_atlas)
        paths = set(self.atlas["source_sha256"]) | {
            "evidence/atlas.json", "evidence/atlas-review.json",
            "scripts/check_atlas.py", "scripts/build_atlas_data.py"}
        with tempfile.TemporaryDirectory() as directory:
            temporary = Path(directory)
            for name in paths:
                destination = temporary / name
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes((ROOT / name).read_bytes())
            query_atlas.load_dataset(root=temporary)
            altered = json.loads((temporary / "evidence/atlas.json").read_text(encoding="utf-8"))
            altered["entries"][9]["operations"] = [[0, 1, 2, 3]]
            (temporary / "evidence/atlas.json").write_text(json.dumps(altered), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "independent review does not bind this atlas"):
                query_atlas.load_dataset(root=temporary)


if __name__ == "__main__":
    unittest.main()
