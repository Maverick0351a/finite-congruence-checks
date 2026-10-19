"""Finite five-object audit tests, including a different partition construction."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import check_five_object as audit


def block_partitions(elements):
    """Insert an object into each existing block or create a new block.

    This does not use label-assignment enumeration from the audit.
    """
    if not elements:
        yield ()
        return
    first, rest = elements[0], elements[1:]
    for grouping in block_partitions(rest):
        yield (frozenset((first,)),) + grouping
        for index in range(len(grouping)):
            yield grouping[:index] + (grouping[index] | {first},) + grouping[index + 1:]


def block_labels(blocks):
    ordered = sorted(blocks, key=min)
    return tuple(next(i for i, block in enumerate(ordered) if x in block) for x in range(5))


def quotient_preserves(operation, blocks):
    """Each block image must be contained in a single block of the quotient."""
    return all(any({operation[x] for x in block} <= target for target in blocks) for block in blocks)


class FiveObjectAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.input = audit.expected_input()
        cls.report = audit.audit()
        cls.blocks = tuple(block_partitions(tuple(range(5))))

    def test_independent_block_enumeration_and_full_classification(self):
        labels = {block_labels(p) for p in self.blocks}
        self.assertEqual(len(self.blocks), 52)
        self.assertEqual(len(labels), 52)
        self.assertEqual(labels, set(audit.partitions()))
        for name in ("A", "B"):
            operations = self.input["values"][name]["operations"]
            actual = {block_labels(p) for p in self.blocks
                      if all(quotient_preserves(op, p) for op in operations)}
            self.assertEqual(actual, {tuple(p) for p in self.input["values"][name]["groupings"]})
            self.assertEqual(len(actual), 8)

    def test_complete_admissible_map_tables_and_obstruction_profiles(self):
        for name, count in (("A", 67), ("B", 63)):
            rows = self.report["constructions"][name]["admissible_map_records"]
            self.assertEqual(len(rows), count)
            self.assertEqual(len({tuple(row["operation"]) for row in rows}), count)
            required = set(map(tuple, self.input["values"][name]["groupings"]))
            for row in rows:
                with self.subTest(construction=name, operation=row["operation"]):
                    preserved = {block_labels(p) for p in self.blocks if quotient_preserves(row["operation"], p)}
                    self.assertTrue(required <= preserved)
                    self.assertEqual(preserved, {audit.partitions()[i] for i in row["preserved_partition_indices"]})
                    self.assertEqual(row["obstruction_destruction"],
                                     [tuple(p) not in preserved for p in self.input["obstructing_groupings"][name]])

    def test_three_rule_lower_bound_has_readable_obstruction_argument(self):
        rows = self.report["constructions"]["A"]["admissible_map_records"]
        self.assertEqual(self.report["constructions"]["A"]["unordered_pairs_with_repetition_excluded"], 2278)
        for row in rows:
            profile = row["obstruction_destruction"]
            if profile[0]:
                self.assertFalse(any(profile[1:]))
            self.assertLessEqual(sum(profile[1:]), 2)
        # The actual three maps jointly remove every forbidden relation.
        upper = self.report["constructions"]["A"]["supplied_operation_destruction_profiles"]
        self.assertTrue(all(any(row[i] for row in upper) for i in range(4)))

    def test_two_rule_lower_bound_excludes_one_rule(self):
        rows = self.report["constructions"]["B"]["admissible_map_records"]
        self.assertTrue(all(not all(row["obstruction_destruction"]) for row in rows))
        upper = self.report["constructions"]["B"]["supplied_operation_destruction_profiles"]
        self.assertTrue(all(any(row[i] for row in upper) for i in range(2)))
        for name in ("A", "B"):
            self.assertTrue(self.report["constructions"][name]["empty_signature_excluded"])

    def test_order_isomorphism_by_block_inclusion(self):
        def blocks(labels):
            return {frozenset(x for x in range(5) if labels[x] == label) for label in labels}

        def below(first, second):
            return all(any(block <= target for target in blocks(second)) for block in blocks(first))

        first = self.input["values"]["A"]["groupings"]
        second = self.input["values"]["B"]["groupings"]
        mapping = self.input["values"]["A_to_B"]
        self.assertEqual(sorted(mapping), list(range(8)))
        for i in range(8):
            for j in range(8):
                self.assertEqual(below(first[i], first[j]), below(second[mapping[i]], second[mapping[j]]))

    def test_wrong_rules_and_grouping_conclusions_rejected(self):
        changes = (
            lambda doc: doc["values"]["A"]["operations"][0].__setitem__(2, 0),
            lambda doc: doc["values"]["B"]["operations"].__setitem__(1, [0, 1, 2, 3, 4]),
            lambda doc: doc["values"]["A"]["groupings"].__setitem__(1, [0, 0, 0, 0, 1]),
            lambda doc: doc["values"]["B"]["groupings"].pop(),
            lambda doc: doc["values"]["A"].__setitem__("minimum_unary_operations", 2),
        )
        for index, change in enumerate(changes):
            with self.subTest(change=index):
                document = copy.deepcopy(self.input)
                change(document)
                with self.assertRaises(ValueError):
                    audit.mathematical_audit(document)

    def test_wrong_order_mapping_and_false_obstructions_rejected(self):
        changes = (
            lambda doc: doc["values"].__setitem__("A_to_B", list(range(8))),
            lambda doc: doc["values"]["A_to_B"].__setitem__(0, 2),
            lambda doc: doc["obstructing_groupings"]["A"].__setitem__(0, [0, 0, 0, 0, 0]),
            lambda doc: doc["obstructing_groupings"]["B"].__setitem__(1, [0, 0, 0, 0, 1]),
        )
        for index, change in enumerate(changes):
            with self.subTest(change=index):
                document = copy.deepcopy(self.input)
                change(document)
                with self.assertRaises(ValueError):
                    audit.mathematical_audit(document)

    def test_domain_types_and_unsupported_claim_scope_rejected(self):
        changes = (
            lambda doc: doc.__setitem__("schema_version", True),
            lambda doc: doc["values"]["carrier"].__setitem__(0, False),
            lambda doc: doc["values"]["A"]["operations"][0].__setitem__(0, -1),
            lambda doc: doc["values"]["A"]["operations"][0].__setitem__(0, 5),
            lambda doc: doc["values"]["A"]["operations"][0].__setitem__(0, 0.0),
            lambda doc: doc["values"]["A"]["groupings"].__setitem__(0, [1, 1, 1, 1, 1]),
            lambda doc: doc.__setitem__("scope", "All five-object algebras"),
            lambda doc: doc["values"]["A"].__setitem__("id", doc["values"]["B"]["id"]),
        )
        for index, change in enumerate(changes):
            with self.subTest(change=index):
                document = copy.deepcopy(self.input)
                change(document)
                with self.assertRaises(ValueError):
                    audit.mathematical_audit(document)

    def test_saved_receipt_recomputed_and_deterministic(self):
        self.assertEqual(audit.encode(audit.replay()), audit.encode(self.report))
        self.assertEqual(audit.encode(audit.audit()), audit.encode(self.report))

    def test_receipt_corruption_and_boolean_integer_substitution_rejected(self):
        changes = (
            lambda doc: doc["checks"].__setitem__("passed", 1),
            lambda doc: doc["checks"].__setitem__("all_unary_maps", 3124),
            lambda doc: doc["constructions"]["A"]["admissible_map_records"].pop(),
            lambda doc: doc["constructions"]["A"]["admissible_map_records"][0]["obstruction_destruction"].__setitem__(0, True),
            lambda doc: doc["source_sha256"].__setitem__(audit.INPUT, "0" * 64),
            lambda doc: doc["constructions"]["B"].__setitem__("minimum_unary_operations", 1),
        )
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "receipt.json"
            for index, change in enumerate(changes):
                with self.subTest(change=index):
                    receipt = copy.deepcopy(self.report)
                    change(receipt)
                    audit.write(output, receipt)
                    with self.assertRaises(ValueError):
                        audit.replay(output)

    def test_duplicate_json_keys_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "duplicate.json"
            path.write_text('{"schema_version": 1, "schema_version": 1}', encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "Duplicate JSON key"):
                audit.read(path)

    def test_cli_check_replay_and_optimized_python_failure(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "receipt.json"
            for command in ("check", "replay"):
                result = subprocess.run([sys.executable, str(audit.ROOT / audit.SOURCE), command, "--out", str(output)],
                                        capture_output=True, text=True, timeout=30, check=False)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertTrue(json.loads(result.stdout)["passed"])
            damaged = audit.read(output)
            damaged["checks"]["distinct_partitions"] = 51
            audit.write(output, damaged)
            result = subprocess.run([sys.executable, "-O", str(audit.ROOT / audit.SOURCE), "replay", "--out", str(output)],
                                    capture_output=True, text=True, timeout=30, check=False)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("differs from independent recomputation", result.stderr)

    def test_cli_cannot_overwrite_input(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "input.json"
            audit.write(path, self.input)
            original = path.read_bytes()
            result = subprocess.run([sys.executable, str(audit.ROOT / audit.SOURCE), "check", "--input", str(path),
                                     "--out", str(path)], capture_output=True, text=True, timeout=30, check=False)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("must not overwrite", result.stderr)
            self.assertEqual(path.read_bytes(), original)


if __name__ == "__main__":
    unittest.main()
