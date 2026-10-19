"""Contract tests for the independent reference, without loading Lean code."""

import importlib.util
import json
from pathlib import Path
import unittest


ROOT = Path(__file__).resolve().parents[1]
MODULE_PATH = ROOT / "scripts" / "grouping_reference.py"
SPEC = importlib.util.spec_from_file_location("grouping_reference_under_test", MODULE_PATH)
reference = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(reference)


class GroupingReferenceTests(unittest.TestCase):
    def test_contract_fixtures(self):
        contract = json.loads((ROOT / "specs" / "unary-grouping-v1.json").read_text(encoding="utf-8"))
        self.assertEqual(contract["contract_id"], reference.CONTRACT_ID)
        for fixture in contract["examples"]:
            with self.subTest(input_id=fixture["input_id"]):
                word = fixture["input"]["word"]
                operation, labels = reference.decode(word)
                self.assertEqual(operation, fixture["input"]["operation"])
                self.assertEqual(labels, fixture["input"]["group_labels"])
                result = reference.evaluate(word)
                self.assertEqual(result["preserves"], fixture["expected"]["preserves"])
                self.assertEqual(result["violating_pair"], fixture["expected"].get("violating_pair"))

    def test_every_field_position_and_extreme_words(self):
        # Literal positional weights independently spell out the input layout.
        weights = [1, 4, 16, 64, 256, 1024, 4096, 16384]
        for position, weight in enumerate(weights):
            for value in range(4):
                with self.subTest(position=position, value=value):
                    operation, labels = reference.decode(weight * value)
                    expected = [0] * 8
                    expected[position] = value
                    self.assertEqual(operation + labels, expected)
        self.assertEqual(reference.decode(0), ([0] * 4, [0] * 4))
        self.assertEqual(reference.decode(65535), ([3] * 4, [3] * 4))

    def test_invalid_values_are_not_false_preservation(self):
        for function in [reference.decode, reference.evaluate, reference.repair_grouping]:
            for invalid in [True, False, 1.0, -1.0, "20640", None, [], {}]:
                with self.subTest(function=function.__name__, invalid=invalid):
                    with self.assertRaises(TypeError):
                        function(invalid)
            for invalid in [-1, 65536, -(10 ** 100), 10 ** 100]:
                with self.subTest(function=function.__name__, invalid=invalid):
                    with self.assertRaises(ValueError):
                        function(invalid)

    def test_equality_universal_and_identity_controls(self):
        # Every operation preserves equality and the universal grouping.
        for operation_word in range(256):
            for labels_word in [0, 255, 228]:  # [0,0,0,0], [3,3,3,3], [0,1,2,3]
                word = operation_word + 256 * labels_word
                self.assertEqual(reference.evaluate(word), {"preserves": True, "violating_pair": None})
        # Identity preserves every label array, including noncanonical arrays.
        for labels_word in range(256):
            self.assertTrue(reference.evaluate(228 + 256 * labels_word)["preserves"])

    def test_preserved_inputs_retain_their_exact_encoding(self):
        for word in [0, 65535, 0x50A0, 0xFFE4, 0xE4A8]:
            self.assertTrue(reference.evaluate(word)["preserves"])
            self.assertEqual(reference.repair_grouping(word), word)

    def test_specification_failure_repairs_to_the_universal_grouping(self):
        self.assertEqual(reference.repair_grouping(0x50A8), 0x00A8)
        self.assertEqual(reference.decode(0x00A8), ([0, 2, 2, 2], [0, 0, 0, 0]))

    def test_nontrivial_repair_retains_two_groups(self):
        # AB | C | D -> ABC | D; D still remains distinct.
        before, after = 0x90E8, 0x80E8
        self.assertEqual(reference.decode(before), ([0, 2, 2, 3], [0, 0, 1, 2]))
        self.assertEqual(reference.evaluate(before), {"preserves": False, "violating_pair": [0, 1]})
        self.assertEqual(reference.repair_grouping(before), after)
        self.assertEqual(reference.decode(after), ([0, 2, 2, 3], [0, 0, 0, 2]))
        self.assertEqual(reference.evaluate(after), {"preserves": True, "violating_pair": None})

    def test_repair_repeats_after_a_merge_creates_a_new_obligation(self):
        # A -> B -> C -> D: merging AB forces ABC, then all four.
        self.assertEqual(reference.decode(0x90F9), ([1, 2, 3, 3], [0, 0, 1, 2]))
        self.assertEqual(reference.repair_grouping(0x90F9), 0x00F9)

    def test_reference_outcomes_and_witnesses_on_every_raw_word(self):
        # Literal ordered-pair evaluation differs from the block-image method.
        # This is still Python testing, not a proof of the reference.
        for word in range(reference.INPUT_COUNT):
            operation, labels = reference.decode(word)
            expected = all(
                labels[x] != labels[y] or labels[operation[x]] == labels[operation[y]]
                for x in range(4) for y in range(4)
            )
            result = reference.evaluate(word)
            self.assertIs(result["preserves"], expected, word)
            if expected:
                self.assertIsNone(result["violating_pair"], word)
            else:
                x, y = result["violating_pair"]
                self.assertIn(x, range(4), word)
                self.assertIn(y, range(4), word)
                self.assertEqual(labels[x], labels[y], word)
                self.assertNotEqual(labels[operation[x]], labels[operation[y]], word)

    def test_repair_properties_on_every_raw_word(self):
        # These are reference checks, not evidence about a compiled checker.
        for word in range(reference.INPUT_COUNT):
            operation, original = reference.decode(word)
            repaired_word = reference.repair_grouping(word)
            repaired_operation, repaired = reference.decode(repaired_word)
            self.assertEqual(repaired_operation, operation, word)
            self.assertEqual(reference.repair_grouping(repaired_word), repaired_word, word)
            for x in range(4):
                for y in range(4):
                    if original[x] == original[y]:
                        self.assertEqual(repaired[x], repaired[y], word)
                    if repaired[x] == repaired[y]:
                        self.assertEqual(repaired[operation[x]], repaired[operation[y]], word)


if __name__ == "__main__":
    unittest.main()
