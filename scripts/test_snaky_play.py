"""Controls for one illustrative execution, including a separate replacement fixture."""
from copy import deepcopy
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

import build_snaky_play as build
import check_snaky_play as check
import check_snaky as oracle


class SnakyPlayTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.record = build.build()
        cls.cards, cls.expressions = check.reconstruct()
        cls.board = cls.cards[727][1]

    def reject(self, edit, message=None):
        record = deepcopy(self.record)
        edit(record)
        with self.assertRaisesRegex(ValueError, message or "."):
            check.validate(record)

    def test_complete_example_replays_in_eight_claims(self):
        checked = check.validate(self.record)
        self.assertEqual(checked["result"]["maker_claims"], 8)
        self.assertEqual(checked["result"]["breaker_claims"], 7)
        self.assertEqual([s["active"]["height"] for s in checked["steps"]], [21, 20, 18, 14, 7, 3, 2, 1])
        self.assertEqual([s["global_budget_before"] for s in checked["steps"]], list(range(21, 13, -1)))
        self.assertEqual(checked["result"]["remaining_global_budget"], 13)

    def test_saved_record_matches_and_replays(self):
        check.same(oracle.read(check.ROOT / check.INPUT), self.record, "Saved example")
        self.assertEqual(check.replay()["id"], build.EXAMPLE_ID)

    def test_replay_does_not_call_move_generator(self):
        with patch.object(build, "build", side_effect=RuntimeError("generator unavailable")), \
             patch.object(build, "build_step", side_effect=RuntimeError("generator unavailable")):
            self.assertIs(check.validate(self.record), self.record)

    def test_independent_geometry_matches_all_numbered_cards(self):
        cards, _, _ = oracle.reconstruct((oracle.ROOT / oracle.INPUT).read_bytes())
        for number, original in enumerate(cards):
            self.assertEqual(self.cards[number], (original.required, original.support, original.height), number)

    def test_paper_prefix_inline_step_and_terminal_placement(self):
        self.assertEqual([s["breaker"]["cell"] for s in self.record["steps"][:2]], [[7, 8], [8, 6]])
        inline = self.record["steps"][3]["active"]
        self.assertEqual((inline["card"], inline["inline_path"]), (684, [0]))
        self.assertEqual(inline["placement"], {"matrix": [[0, 1], [1, 0]], "translation": [1, 1]})
        target = self.record["result"]["target"]
        self.assertEqual(target, {"symmetry": 1, "translation": [8, 7],
                                 "cells": [[8, 7], [8, 8], [8, 9], [8, 10], [9, 10], [9, 11]]})
        self.assertTrue(self.record["steps"][-1]["active"]["certificate_ref"]["url"].endswith("Height01Part01.lean#L36"))

    def test_composition_order_is_checked(self):
        self.reject(lambda r: r["steps"][4]["active"]["placement"].update(translation=[6, 11]), "placement")

    def test_inline_coordinates_cannot_be_rebased(self):
        self.reject(lambda r: r["steps"][3]["active"]["placement"].update(translation=[12, 9]), "placement")

    def test_changed_pivot_and_claim_kind_rejected(self):
        self.reject(lambda r: r["steps"][0]["maker"].update(cell=[8, 9]), "Maker claim")
        self.reject(lambda r: r["steps"][0]["maker"].update(kind="replacement"), "Maker claim")

    def test_occupied_offboard_and_boolean_breaker_replies_rejected(self):
        for cell in ([8, 8], [17, 0], [True, 8]):
            self.reject(lambda r, cell=cell: r["steps"][0]["breaker"].update(cell=cell), "fresh|integer")

    def test_other_legal_reply_changes_this_registered_example(self):
        self.reject(lambda r: r["steps"][0]["breaker"].update(cell=[7, 7]), "declared choices")

    def test_wrong_continuation_and_envelope_rejected(self):
        self.reject(lambda r: r["steps"][0]["continuation"].update(child_index=0), "continuation")
        self.reject(lambda r: r["steps"][1]["active"]["envelope"].pop(), "placement")

    def test_wrong_required_cells_and_source_reference_rejected(self):
        self.reject(lambda r: r["steps"][1]["active"].update(required=[]), "placement")
        self.reject(lambda r: r["steps"][1]["active"]["certificate_ref"].update(line=1), "placement")

    def test_state_cannot_omit_a_claim(self):
        self.reject(lambda r: r["steps"][2]["maker_after"].pop(), "Maker state after")
        self.reject(lambda r: r["steps"][2]["breaker_after"].pop(), "Breaker state after")

    def test_budget_is_not_a_predicted_actual_finish(self):
        self.reject(lambda r: r["steps"][2].update(global_budget_before=18), "Global budget")
        self.reject(lambda r: r["steps"][2]["active"].update(height=19), "placement")

    def test_cropped_or_changed_terminal_target_rejected(self):
        self.reject(lambda r: r["steps"][-1]["witness"]["cells"].pop(), "target witness")
        self.reject(lambda r: r["steps"][-1]["witness"].update(translation=[7, 8]), "target witness")

    def test_no_breaker_reply_or_extra_move_after_victory(self):
        self.reject(lambda r: r["steps"][-1].update(breaker={"cell": [0, 9]}), "after victory")
        self.reject(lambda r: r["steps"].append(deepcopy(r["steps"][-1])), "after victory")

    def test_incomplete_trace_does_not_establish_a_win(self):
        self.reject(lambda r: r["steps"].pop(), "before a checked win")

    def test_board_and_input_hashes_are_exact(self):
        self.reject(lambda r: r["board"]["cells"].append([0, 0]), "Exact board")
        self.reject(lambda r: r["sources"]["certificate"].update(sha256="0"*64), "hashes")

    def test_exact_raw_certificate_bytes_are_required(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for path in (oracle.INPUT, oracle.SOURCE, build.SOURCE, check.SOURCE):
                (root / path).parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(check.ROOT / path, root / path)
            path = root / oracle.INPUT
            path.write_bytes(path.read_bytes().replace(b"727 88 ", b"727 89 "))
            with self.assertRaisesRegex(ValueError, "certificate bytes"):
                check.validate(self.record, root)

    def test_scope_cannot_be_promoted_to_verified_policy(self):
        self.reject(lambda r: r.update(kind="formally_verified_extracted_policy"), "Evidence kind")
        self.reject(lambda r: r.update(limits=[]), "Evidence limits")
        self.reject(lambda r: r.update(proof_receipt_status="PASS"), "fields")

    def test_numeric_types_and_malformed_steps_rejected(self):
        self.reject(lambda r: r.update(schema_version=True), "Schema version")
        self.reject(lambda r: r["steps"][0].update(move=True), "move number")
        self.reject(lambda r: r["steps"].__setitem__(0, None), "object")

    def replacement_fixture(self):
        # An isolated legal card-6 position, not asserted to be reached by the
        # displayed play. The owned pivot still consumes a fresh Maker claim.
        cards, expressions, _ = oracle.reconstruct((oracle.ROOT / oracle.INPUT).read_bytes())
        cursor = (6, (), (1, 0, 0, 1, 4, 4))
        data = build.data_at(cursor, cards, expressions)
        maker = data.required | {(5, 8)}
        breaker = frozenset(sorted(self.board - data.support - maker)[:len(maker)])
        step, nxt, m2, b2 = build.build_step(cursor, maker, breaker, len(maker)+1, None,
                                            self.board, cards, expressions, build.targets_on(self.board))
        return cursor, maker, breaker, step, nxt, m2, b2

    def test_already_owned_pivot_uses_a_fresh_counted_replacement(self):
        cursor, maker, breaker, step, nxt, m2, b2 = self.replacement_fixture()
        self.assertEqual(step["maker"]["kind"], "replacement")
        self.assertEqual(step["maker"]["prescribed_cell"], [5, 8])
        self.assertNotIn(tuple(step["maker"]["cell"]), maker | breaker)
        self.assertEqual(len(m2), len(maker)+1)
        self.assertEqual(step["global_budget_after"], step["global_budget_before"]-1)
        self.assertEqual(check.validate_step(step, cursor, maker, breaker, self.board, self.cards, self.expressions),
                         (nxt, m2, b2))
        self.assertTrue(all(s["maker"]["kind"] != "replacement" for s in self.record["steps"]))

    def test_reusing_owned_pivot_or_skipping_replacement_is_rejected(self):
        cursor, maker, breaker, step, _, _, _ = self.replacement_fixture()
        wrong = deepcopy(step)
        wrong["maker"]["cell"] = wrong["maker"]["prescribed_cell"]
        with self.assertRaisesRegex(ValueError, "Maker claim"):
            check.validate_step(wrong, cursor, maker, breaker, self.board, self.cards, self.expressions)
        wrong = deepcopy(step)
        wrong["maker_after"] = wrong["maker_before"]
        with self.assertRaisesRegex(ValueError, "Maker state after"):
            check.validate_step(wrong, cursor, maker, breaker, self.board, self.cards, self.expressions)


if __name__ == "__main__":
    unittest.main()
