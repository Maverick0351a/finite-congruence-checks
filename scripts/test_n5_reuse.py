"""Cross-check the reading guide, exact query downloads and deliberate mistakes."""
import copy
import itertools
import unittest
from unittest.mock import patch

import build_n5_reuse as demo
import query_context as query


def partition_relation(labels):
    return {(i, j) for i in range(4) for j in range(4) if labels[i] == labels[j]}


def valid(operations, labels):
    blocks = [{i for i in range(4) if labels[i] == b} for b in set(labels)]
    return all(len({labels[op[i]] for i in block}) == 1 for op in operations for block in blocks)


class ReuseTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = demo.build()

    def test_downloads_are_exact_query_records(self):
        for t in self.data["transfers"]:
            record = query.explain_claim(t["record"]["claim"]["id"])
            self.assertEqual(t["record"], record)
            path = demo.ROOT / "space" / t["download"]
            self.assertEqual(path.read_bytes(), query.encode(record))
            self.assertEqual(query.check_record(query.read_json(path))["status"], "supported")

    def test_generated_files_are_current(self):
        for name, text in zip(demo.OUTPUTS, demo.output_texts(self.data)):
            self.assertEqual((demo.ROOT / name).read_text(encoding="utf-8"), text)

    def test_both_transfers_preserve_every_relation_and_order(self):
        all_relations = {frozenset(partition_relation(p)): p for p in itertools.product(range(4), repeat=4)}
        self.assertEqual(len(all_relations), 15)
        for t in self.data["transfers"]:
            c = t["record"]["claim"]
            p = c["mapping"]["object_forward_source_to_target"]
            source, target = c["values"]["source"], c["values"]["target"]
            accepted = {r for r, labels in all_relations.items() if valid(target["operations"], labels)}
            self.assertEqual(accepted, {frozenset(partition_relation(g)) for g in target["groupings"]})
            self.assertEqual(len(accepted), 5)
            for r, labels in all_relations.items():
                transported = [0] * 4
                for i in range(4):
                    transported[p[i]] = labels[i]
                self.assertEqual(valid(source["operations"], labels), valid(target["operations"], transported))
            for a, b in itertools.product(range(5), repeat=2):
                self.assertEqual(partition_relation(source["groupings"][a]) <= partition_relation(source["groupings"][b]),
                                 partition_relation(target["groupings"][a]) <= partition_relation(target["groupings"][b]))

    def test_grouping_failure_is_a_real_counterexample(self):
        control = self.data["controls"][0]
        self.assertFalse(valid(control["operations"], control["partition"]))
        self.assertEqual(control["witness"], {"rule": 1, "pair": [2, 3], "outputs": [0, 1]})
        target = self.data["transfers"][0]["record"]["claim"]["values"]["target"]
        self.assertTrue(valid(target["operations"], control["partition"]))

    def test_wrong_rule_map_keeps_family_but_breaks_equation(self):
        t = self.data["transfers"][1]
        c = t["record"]["claim"]
        control = self.data["controls"][1]
        witness = control["witness"]
        self.assertNotEqual(witness["target_output"], witness["expected_output"])
        self.assertTrue(all(valid(c["values"]["target"]["operations"], g) for g in c["values"]["target"]["groupings"]))
        changed = copy.deepcopy(t["record"])
        changed["claim"]["mapping"]["rule_target_to_source"] = control["rule_map"]
        self.assertEqual(query.check_record(changed)["status"], "unsupported")
        self.assertEqual(changed["claim"]["values"], c["values"])

    def test_theorem_substitution_changes_only_evidence(self):
        original = self.data["transfers"][0]["record"]
        changed = copy.deepcopy(original)
        changed["claim"]["theorem"] = self.data["controls"][2]["proposed_theorem"]
        self.assertEqual(query.check_record(changed)["mismatch_paths"], ["/claim/theorem"])
        self.assertEqual(changed["claim"]["values"], original["claim"]["values"])

    def test_source_links_are_commit_pinned(self):
        prefix = demo.GITHUB + self.data["source_revision"] + "/"
        for t in self.data["transfers"]:
            self.assertTrue(all(url.startswith(prefix) for url in t["links"].values()))
        anchor = query.read_json(demo.ROOT / demo.ANCHOR)
        self.assertEqual(set(anchor["files"]), set(demo.linked_paths([t["record"] for t in self.data["transfers"]])))

    def test_changed_linked_source_rejects_export(self):
        original_digest = demo.rotate.digest
        target = demo.ROOT / "lean/FiniteCongruenceChecks.lean"
        with patch.object(demo.rotate, "digest", side_effect=lambda p: "0" * 64 if p == target else original_digest(p)), \
             patch.object(demo, "records", return_value=[t["record"] for t in self.data["transfers"]]):
            with self.assertRaisesRegex(ValueError, "linked source changed"):
                demo.build()

    def test_wrong_source_revision_rejects_export(self):
        anchor = query.read_json(demo.ROOT / demo.ANCHOR)
        anchor["revision"] = "0" * 40
        with self.assertRaisesRegex(ValueError, "anchored Git source unavailable"):
            demo.check_source_commit(demo.ROOT, anchor, list(anchor["files"]))

    def test_wrong_commit_file_hash_rejects_export(self):
        anchor = query.read_json(demo.ROOT / demo.ANCHOR)
        path = next(iter(anchor["files"]))
        anchor["files"][path] = "0" * 64
        with self.assertRaisesRegex(ValueError, "Git source differs"):
            demo.check_source_commit(demo.ROOT, anchor, [path])


if __name__ == "__main__":
    unittest.main()
