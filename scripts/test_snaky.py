"""Geometry, malformed-certificate, and saved-evidence controls for Snaky."""
from pathlib import Path
import shutil
import tempfile
import unittest

import check_snaky as audit


class SnakyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.payload = (audit.ROOT / audit.INPUT).read_bytes()
        cls.cards, cls.expressions, cls.counts = audit.reconstruct(cls.payload)

    def test_exact_source_bytes(self):
        self.assertEqual(len(self.payload), 38367)
        self.assertEqual(audit.raw_digest(self.payload), audit.CERTIFICATE_SHA256)
        self.assertNotIn(b"\r", self.payload)

    def test_six_bases_are_one_cell_completions(self):
        expected = {(0, 0), (1, 0), (2, 0), (3, 0), (3, 1), (4, 1)}
        self.assertEqual(len(self.cards[:6]), 6)
        self.assertEqual({next(iter(expected - c.required)) for c in self.cards[:6]}, expected)
        for card in self.cards[:6]:
            self.assertEqual(card.support, expected)
            self.assertEqual(len(card.required), 5)
            self.assertEqual(card.height, 1)

    def test_first_geometric_fork(self):
        # Direct coordinates from two overlapping vertical Snaky copies.
        required = {(0, y) for y in range(5)}
        self.assertEqual(self.cards[6].required, required)
        self.assertEqual(self.cards[6].support, required | {(1, 3), (1, 4), (1, 5)})
        self.assertEqual(self.cards[6].height, 2)

    def test_second_geometric_fork(self):
        self.assertEqual(self.cards[7].required, {(0, y) for y in range(1, 5)})
        self.assertEqual(self.cards[7].support,
                         {(0, y) for y in range(1, 6)} | {(1, y) for y in (0, 1, 2, 4, 5, 6)})
        self.assertEqual(self.cards[7].height, 3)

    def test_all_eight_signed_permutations(self):
        expected = [(2, 3), (3, 2), (-2, 3), (3, -2), (2, -3), (-3, 2), (-2, -3), (-3, -2)]
        for s, point in enumerate(expected):
            self.assertEqual(audit.transform({(2, 3)}, s, (0, 0)), {point})
            self.assertEqual(audit.transform({(2, 3)}, s, (5, 7)), {(point[0] + 5, point[1] + 7)})

    def test_transform_order_matters(self):
        # Mode3 negates x BEFORE swapping: (2,3)->(3,-2), then translate.
        self.assertEqual(audit.transform({(2, 3)}, 3, (4, 5)), {(7, 3)})
        self.assertNotEqual(audit.transform({(2, 3)}, 3, (4, 5)), {(1, 7)})

    def test_transforms_are_bijections_on_negative_coordinates(self):
        points = {(x, y) for x in range(-3, 4) for y in range(-2, 3)}
        for s in range(8):
            transformed = audit.transform(points, s, (-8, 6))
            self.assertEqual(len(transformed), len(points))
            self.assertTrue(any(x < 0 for x, _ in transformed))

    def test_nested_coordinates_are_absolute(self):
        expr = audit.parse_line("6 88 (14 4:100 5:101)", 6)
        self.assertEqual(expr.children[0].pivot, (1, 4))
        result = audit.evaluate(expr, self.cards[:6])
        self.assertEqual(result.support, self.cards[6].support | {(8, 8)})
        self.assertEqual(result.height, 3)

    def test_invalid_reference_domains(self):
        for token in ("-1", "+1", "01", "0:800", "0:-00", "0:0H0", "0:0000", "0:", "1:000:000"):
            with self.subTest(token=token), self.assertRaises(ValueError):
                audit.parse_line("6 00 " + token, 6)

    def test_missing_or_extra_expression_tokens(self):
        for line in ("6", "6 00", "6 00 (11)", "6 00 (11 0", "6 00 0)", "6 00 )0", "6 H0 0"):
            with self.subTest(line=line), self.assertRaises(ValueError):
                audit.parse_line(line, 6)

    def test_backward_references_at_every_depth(self):
        for line in ("6 00 6", "6 00 (11 6)", "6 00 (11 (22 7))"):
            with self.subTest(line=line), self.assertRaisesRegex(ValueError, "earlier card"):
                audit.parse_line(line, 6)

    def test_card_number_must_be_consecutive(self):
        for line in ("7 14 4:100 5:101", "06 14 4:100 5:101"):
            with self.subTest(line=line), self.assertRaises(ValueError):
                audit.parse_line(line, 6)

    def test_non_ascii_and_blank_lines_rejected(self):
        for payload in (b"", b"\xff", self.payload + b"\n", self.payload.replace(b"\n", b"\n\n", 1)):
            with self.subTest(payload=payload[:20]), self.assertRaises(ValueError):
                audit.reconstruct(payload)

    def test_missing_final_card_does_not_establish_endpoint(self):
        cards, exprs, _ = audit.reconstruct(b"\n".join(self.payload.splitlines()[:-1]))
        with self.assertRaisesRegex(ValueError, "728"):
            audit.validate_endpoint(cards, exprs)

    def test_changed_pivot_cannot_reuse_the_endpoint(self):
        changed = self.payload.replace(b"727 88 ", b"727 89 ")
        cards, exprs, _ = audit.reconstruct(changed)
        self.assertEqual(cards[-1].required, {(8, 8)})
        with self.assertRaisesRegex(ValueError, "pivot"):
            audit.validate_endpoint(cards, exprs)

    def test_final_support_geometry_and_arithmetic(self):
        audit.validate_endpoint(self.cards, self.expressions)
        final = self.cards[-1]
        self.assertEqual(len(final.support), 251)
        self.assertEqual(final.required, set())
        self.assertEqual(final.height, 21)
        self.assertTrue(final.support <= {(x, y) for x in range(17) for y in range(17)})
        self.assertEqual(min(251 - 2 * (move - 1) for move in range(1, 22)), 211)

    def test_wrong_board_or_move_bound_rejected(self):
        for bounds in ((0, 15, 0, 15), (1, 17, 1, 17), (False, 16, 0, 16)):
            with self.subTest(bounds=bounds), self.assertRaises(ValueError):
                audit.validate_endpoint(self.cards, self.expressions, board_bounds=bounds)
        for bound in (20, 22, 21.0, True):
            with self.subTest(bound=bound), self.assertRaises(ValueError):
                audit.validate_endpoint(self.cards, self.expressions, move_bound=bound)

    def test_invalid_child_requirements_and_height_rejected(self):
        invalid = (audit.Card(frozenset({(2, 2)}), frozenset({(0, 0)}), 1),
                   audit.Card(frozenset(), frozenset({(0, 0)}), 0),
                   audit.Card(frozenset(), frozenset({(0, 0)}), True))
        for child in invalid:
            with self.subTest(child=child), self.assertRaises(ValueError):
                audit.combine_cards((0, 0), [child])

    def test_every_card_local_invariants(self):
        self.assertEqual(self.counts, {"combination_nodes": 1620, "reference_nodes": 4089, "maximum_inline_depth": 8})
        for index, card in enumerate(self.cards):
            with self.subTest(index=index):
                self.assertTrue(card.required <= card.support)
                self.assertGreaterEqual(card.height, 1)
                self.assertLessEqual(card.height, 21)

    def test_final_children_using_separate_coordinate_formula(self):
        # Independent coordinate formulas, without the evaluator's matrix code.
        functions = (lambda x,y:(x,y), lambda x,y:(y,x), lambda x,y:(-x,y), lambda x,y:(y,-x),
                     lambda x,y:(x,-y), lambda x,y:(-y,x), lambda x,y:(-x,-y), lambda x,y:(-y,-x))
        supports = []
        for ref in self.expressions[-1].children:
            f = functions[ref.symmetry]
            dx, dy = ref.translation
            placed = {(f(x, y)[0] + dx, f(x, y)[1] + dy) for x, y in self.cards[ref.index].support}
            supports.append(placed)
        self.assertEqual(set.intersection(*supports), {(8, 8)})
        self.assertEqual(set.union(*supports), self.cards[-1].support)
        self.assertEqual([len(set.intersection(*supports[:n]) - {(8, 8)}) for n in (4, 8, 16, 20, 28, 32)],
                         [35, 31, 21, 12, 4, 0])

    def make_copy(self, directory):
        root = Path(directory)
        for path in (audit.INPUT, audit.OUTPUT, audit.SOURCE):
            (root / path).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(audit.ROOT / path, root / path)
        return root

    def test_saved_receipt_replays(self):
        self.assertEqual(audit.replay()["status"], "PASS")

    def test_mutated_raw_bytes_fail_pin_even_if_semantics_unchanged(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.make_copy(directory)
            (root / audit.INPUT).write_bytes(self.payload.replace(b"\n", b"\r\n"))
            with self.assertRaisesRegex(ValueError, "raw-byte"):
                audit.replay(root)

    def test_changed_receipt_and_boolean_numeric_substitution_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.make_copy(directory)
            for edit in (lambda x: x["final"].update(height=20), lambda x: x.update(schema_version=True)):
                report = audit.read(audit.ROOT / audit.OUTPUT)
                edit(report)
                (root / audit.OUTPUT).write_bytes(audit.encode(report))
                with self.assertRaisesRegex(ValueError, "receipt differs"):
                    audit.replay(root)

    def test_duplicate_json_keys_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "bad.json"
            path.write_text('{"status":"FAIL","status":"PASS"}')
            with self.assertRaisesRegex(ValueError, "Duplicate JSON key"):
                audit.read(path)


if __name__ == "__main__":
    unittest.main()
