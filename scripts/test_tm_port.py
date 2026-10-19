"""Regression checks for the pinned Lean machine semantics and Python bounds.

These are executable tests, not a formal proof of the Python translation.
Expected transitions below follow the source definitions directly, without
using the port's bounded helpers to determine the expected halting times.
"""

from dataclasses import FrozenInstanceError
from types import MappingProxyType
import unittest

import tm_port as tm


class IntSubclass(int):
    pass


BAD_NAT = (True, False, -1, 1.0, "1", None, IntSubclass(1))


def looping_machine():
    return tm.Machine(0, 0, 0, [], [tm.Rule(0, 0, tm.RIGHT)])


def three_step_halt():
    # 0 -> 1 -> 2 -> missing-rule sentinel 3. The missing rule does not move.
    return tm.Machine(2, 0, 0, [], [
        tm.Rule(1, 0, tm.RIGHT), tm.Rule(2, 0, tm.RIGHT), None,
    ])


class TransitionTests(unittest.TestCase):
    def test_initial_tape_has_zero_default_on_both_sides(self):
        c = tm.initial(looping_machine(), [2, 0, 4])
        self.assertEqual((c.state, c.head), (0, 0))
        self.assertEqual([c.read(i) for i in (-100, -1, 0, 1, 2, 3, 100)],
                         [0, 0, 2, 0, 4, 0, 0])
        self.assertEqual(c.written(), {0: 2, 2: 4})

    def test_missing_rule_only_changes_state(self):
        for table in ([], [None]):
            with self.subTest(table=table):
                machine = tm.Machine(0, 0, 0, [], table)
                before = tm.Configuration(0, -3, {-3: 0, 2: 7})
                after = tm.step(machine, before)
                self.assertEqual((after.state, after.head), (1, -3))
                self.assertEqual(dict(after.tape), {-3: 0, 2: 7})
                self.assertEqual((before.state, before.head), (0, -3))
                self.assertTrue(tm.is_halting(machine, after))
                self.assertIs(tm.step(machine, after), after)

    def test_explicit_halting_transition_still_writes_and_moves(self):
        machine = tm.Machine(1, 1, 0, [1], [tm.Rule(1, 1, tm.LEFT)])
        before = tm.initial(machine, [])
        after = tm.step(machine, before)
        self.assertEqual((after.state, after.head, after.read(0)), (1, -1, 1))
        self.assertTrue(tm.is_halting(machine, after))
        self.assertIs(tm.step(machine, after), after)
        self.assertEqual((before.state, before.head, before.read(0)), (0, 0, 0))

    def test_all_three_moves_use_integer_offset(self):
        for move, expected_head in ((tm.LEFT, -1), (tm.STAY, 0), (tm.RIGHT, 1)):
            with self.subTest(move=move):
                machine = tm.Machine(0, 1, 0, [], [tm.Rule(0, 1, move)])
                after = tm.step(machine, tm.initial(machine, []))
                self.assertEqual((after.head, after.read(0)), (expected_head, 1))

    def test_writing_zero_erases_an_existing_nonzero_symbol(self):
        machine = tm.Machine(0, 1, 0, [], [None, tm.Rule(0, 0, tm.STAY)])
        before = tm.initial(machine, [1])
        after = tm.step(machine, before)
        self.assertEqual(after.read(0), 0)
        self.assertEqual(after.written(), {})
        self.assertEqual(before.read(0), 1)

    def test_negative_head_reads_and_updates_its_actual_cell(self):
        machine = tm.Machine(0, 1, 0, [], [None, tm.Rule(0, 0, tm.RIGHT)])
        before = tm.Configuration(0, -2, {-2: 1, 0: 1})
        after = tm.step(machine, before)
        self.assertEqual((after.state, after.head), (0, -1))
        self.assertEqual((after.read(-2), after.read(0)), (0, 1))
        self.assertEqual(before.read(-2), 1)
        self.assertEqual(after.read(-100), 0)

    def test_only_sentinel_or_list_members_are_halting(self):
        machine = tm.Machine(0, 0, 0, [7], [])
        self.assertFalse(machine.well_formed())
        self.assertTrue(tm.is_halting(machine, tm.Configuration(1, 0)))
        self.assertTrue(tm.is_halting(machine, tm.Configuration(7, 0)))
        self.assertFalse(tm.is_halting(machine, tm.Configuration(2, 0)))
        self.assertEqual(tm.step(machine, tm.Configuration(2, 0)).state, 1)


class FuelAndTraceTests(unittest.TestCase):
    def test_zero_fuel_performs_no_transition(self):
        machine = tm.Machine(0, 0, 0, [], [])
        halted, n, c = tm.halts(machine, [5], fuel=0)
        self.assertIs(halted, False)
        self.assertEqual(n, 0)
        self.assertEqual((c.state, c.head, c.read(0)), (0, 0, 5))
        self.assertEqual(c, tm.run(machine, [5], 0))

    def test_halt_at_exact_fuel_and_first_halt_time(self):
        machine = three_step_halt()
        halted, n, c = tm.halts(machine, [], fuel=2)
        self.assertEqual((halted, n, c.state, c.head), (False, 2, 2, 2))
        self.assertEqual(c, tm.run(machine, [], n))
        for fuel in (3, 10):
            with self.subTest(fuel=fuel):
                halted, n, c = tm.halts(machine, [], fuel=fuel)
                self.assertEqual((halted, n, c.state, c.head), (True, 3, 3, 2))
                self.assertEqual(c, tm.run(machine, [], n))

    def test_nonhalting_result_matches_run_at_reported_time(self):
        machine = looping_machine()
        for fuel in (0, 1, 7):
            with self.subTest(fuel=fuel):
                halted, n, c = tm.halts(machine, [], fuel=fuel)
                self.assertEqual((halted, n, c.state, c.head), (False, fuel, 0, fuel))
                self.assertEqual(c, tm.run(machine, [], n))

    def test_already_halted_is_observed_at_time_zero(self):
        machines = [tm.Machine(0, 0, 0, [0], [tm.Rule(0, 0, tm.RIGHT)]),
                    tm.Machine(0, 0, 1, [], [])]
        for machine in machines:
            for fuel in (0, 5):
                with self.subTest(machine=machine, fuel=fuel):
                    halted, n, c = tm.halts(machine, [8], fuel=fuel)
                    self.assertEqual((halted, n, c.head, c.read(0)), (True, 0, 0, 8))
                    self.assertEqual(c, tm.run(machine, [8], 9))

    def test_trace_limit_counts_configurations_including_time_zero(self):
        machine = looping_machine()
        self.assertEqual(list(tm.trace(machine, [], limit=0)), [])
        for limit in (1, 4):
            rows = list(tm.trace(machine, [], limit=limit))
            self.assertEqual([n for n, _ in rows], list(range(limit)))
            self.assertEqual([c.head for _, c in rows], list(range(limit)))
            for n, c in rows:
                self.assertEqual(c, tm.run(machine, [], n))

    def test_trace_includes_halt_once_and_stops(self):
        machine = three_step_halt()
        rows = list(tm.trace(machine, [], limit=20))
        self.assertEqual([(n, c.state, c.head) for n, c in rows],
                         [(0, 0, 0), (1, 1, 1), (2, 2, 2), (3, 3, 2)])
        self.assertEqual(len(list(tm.trace(machine, [], limit=3))), 3)
        already = tm.Machine(0, 0, 0, [0], [])
        self.assertEqual(len(list(tm.trace(already, [], limit=20))), 1)


class LeanDomainTests(unittest.TestCase):
    def test_rule_naturals_and_fin3_are_strict(self):
        for bad in BAD_NAT:
            for position in (0, 1):
                values = [0, 0, tm.STAY]
                values[position] = bad
                with self.subTest(field=position, bad=bad), self.assertRaises(ValueError):
                    tm.Rule(*values)
        for bad in (*BAD_NAT, 3, 4):
            with self.subTest(move=bad), self.assertRaises(ValueError):
                tm.Rule(0, 0, bad)
        for move in (0, 1, 2):
            self.assertEqual(tm.Rule(100, 200, move).move, move)

    def test_machine_natural_fields_and_rule_table_types(self):
        for bad in BAD_NAT:
            for position in (0, 1, 2):
                values = [0, 0, 0, [], []]
                values[position] = bad
                with self.subTest(field=position, bad=bad), self.assertRaises(ValueError):
                    tm.Machine(*values)
            with self.subTest(halting_state=bad), self.assertRaises(ValueError):
                tm.Machine(0, 0, 0, [bad], [])
        for bad in (0, False, (0, 0, 1), {"next_state": 0}, "rule"):
            with self.subTest(table_entry=bad), self.assertRaises(ValueError):
                tm.Machine(0, 0, 0, [], [bad])

    def test_configuration_and_read_distinguish_int_from_nat(self):
        for bad in BAD_NAT:
            with self.subTest(state=bad), self.assertRaises(ValueError):
                tm.Configuration(bad, 0)
            with self.subTest(symbol=bad), self.assertRaises(ValueError):
                tm.Configuration(0, 0, {0: bad})
        c = tm.Configuration(0, -9, {-9: 3})
        self.assertEqual(c.read(-9), 3)
        for bad in (True, False, 1.0, "1", None, IntSubclass(1)):
            with self.subTest(head=bad), self.assertRaises(ValueError):
                tm.Configuration(0, bad)
            with self.subTest(position=bad), self.assertRaises(ValueError):
                tm.Configuration(0, 0, {bad: 0})
            with self.subTest(read=bad), self.assertRaises(ValueError):
                c.read(bad)
        with self.assertRaises(ValueError):
            tm.Configuration(0, 0, [(0, 1)])

    def test_instruction_and_bounded_helpers_reject_non_naturals(self):
        machine = looping_machine()
        for bad in BAD_NAT:
            calls = {
                "instruction state": lambda: machine.instruction(bad, 0),
                "instruction symbol": lambda: machine.instruction(0, bad),
                "run steps": lambda: tm.run(machine, [], bad),
                "halts fuel": lambda: tm.halts(machine, [], bad),
                "trace limit": lambda: list(tm.trace(machine, [], bad)),
                "initial symbol": lambda: tm.initial(machine, [bad]),
                "run input": lambda: tm.run(machine, [bad], 0),
                "halts input": lambda: tm.halts(machine, [bad], 0),
                "trace input": lambda: list(tm.trace(machine, [bad], 1)),
            }
            for name, call in calls.items():
                with self.subTest(call=name, bad=bad), self.assertRaises(ValueError):
                    call()
            self.assertFalse(machine.valid_input([bad]))

    def test_valid_input_is_separate_from_natural_valued_execution(self):
        rule = tm.Rule(1, 1, tm.STAY)
        machine = tm.Machine(1, 1, 0, [], [None, None, rule])
        self.assertTrue(machine.well_formed())
        self.assertTrue(machine.valid_input([]))
        self.assertTrue(machine.valid_input((0, 1)))
        self.assertFalse(machine.valid_input([2]))
        self.assertFalse(machine.valid_input("01"))
        # Lean indexes the flat list by q*alphabet+a, with no symbol bounds
        # test in instruction/run. Symbol 2 therefore reaches entry (1,0).
        self.assertEqual(machine.instruction(0, 2), rule)
        after = tm.run(machine, [2], 1)
        self.assertEqual((after.state, after.head, after.read(0)), (1, 0, 1))

    def test_short_tables_and_unaddressed_padding_match_lean(self):
        rule = tm.Rule(0, 0, tm.STAY)
        short = tm.Machine(2, 1, 0, [], [rule])
        self.assertEqual((short.states, short.alphabet), (3, 2))
        self.assertTrue(short.well_formed())
        self.assertEqual(short.instruction(0, 0), rule)
        for q, a in ((0, 1), (1, 0), (2, 1), (100, 100)):
            self.assertIsNone(short.instruction(q, a))
        extra = tm.Rule(42, 99, tm.RIGHT)
        padded = tm.Machine(0, 0, 0, [], [rule, extra])
        self.assertTrue(padded.well_formed())
        self.assertEqual(padded.instruction(0, 1), extra)
        self.assertEqual(padded.instruction(1, 0), extra)
        after = tm.run(padded, [1], 1)
        self.assertEqual((after.state, after.head, after.read(0)), (42, 1, 99))
        self.assertFalse(tm.is_halting(padded, after))

    def test_type_valid_ill_formed_machines_are_representable(self):
        machines = [tm.Machine(0, 0, 2, [], []),
                    tm.Machine(0, 0, 0, [2], []),
                    tm.Machine(0, 0, 0, [], [tm.Rule(2, 0, tm.STAY)]),
                    tm.Machine(0, 0, 0, [], [tm.Rule(0, 2, tm.STAY)])]
        for machine in machines:
            with self.subTest(machine=machine):
                self.assertFalse(machine.well_formed())
                self.assertEqual(tm.run(machine, [], 0).state, machine.initial_state)
        # A direct transition to the sentinel is ill-formed but still writes
        # and moves before isHalting applies to the resulting configuration.
        machine = tm.Machine(0, 0, 0, [], [tm.Rule(1, 5, tm.RIGHT)])
        self.assertFalse(machine.well_formed())
        c = tm.run(machine, [], 1)
        self.assertEqual((c.state, c.head, c.read(0)), (1, 1, 5))
        self.assertTrue(tm.is_halting(machine, c))


class SnapshotTests(unittest.TestCase):
    def test_machine_copies_caller_lists_and_all_dataclass_fields_are_frozen(self):
        rule = tm.Rule(0, 0, tm.STAY)
        stop, table = [], [rule]
        machine = tm.Machine(0, 0, 0, stop, table)
        stop.append(0)
        table[0] = None
        self.assertEqual(machine.halting_states, ())
        self.assertEqual(machine.table, (rule,))
        self.assertFalse(tm.is_halting(machine, tm.initial(machine, [])))
        self.assertEqual(machine.instruction(0, 0), rule)
        c = tm.Configuration(0, 0)
        for value, field, replacement in ((rule, "write", 1),
                                           (machine, "table", (None,)),
                                           (machine, "initial_state", 1),
                                           (c, "state", 1), (c, "head", -1),
                                           (c, "tape", {})):
            with self.subTest(type=type(value).__name__, field=field), self.assertRaises(FrozenInstanceError):
                setattr(value, field, replacement)

    def test_configuration_copies_and_freezes_tape(self):
        external = {-2: 5, 0: 1}
        c = tm.Configuration(0, -2, external)
        self.assertIsInstance(c.tape, MappingProxyType)
        external[-2] = 99
        external[4] = 7
        self.assertEqual(c.read(-2), 5)
        self.assertEqual(c.read(4), 0)
        with self.assertRaises(TypeError):
            c.tape[-2] = 0
        written = c.written()
        written[-2] = 0
        self.assertEqual(c.read(-2), 5)

    def test_input_and_trace_snapshots_do_not_alias_caller_containers(self):
        machine = tm.Machine(0, 1, 0, [], [tm.Rule(0, 1, tm.RIGHT),
                                             tm.Rule(0, 0, tm.RIGHT)])
        word = [0, 1, 0]
        original_word = word.copy()
        rows = list(tm.trace(machine, word, 4))
        self.assertEqual(word, original_word)
        self.assertEqual([c.written() for _, c in rows],
                         [{1: 1}, {0: 1, 1: 1}, {0: 1}, {0: 1, 2: 1}])
        word[:] = [9, 9, 9]
        self.assertEqual([rows[0][1].read(i) for i in range(3)], original_word)
        self.assertEqual(rows[-1][1].written(), {0: 1, 2: 1})
        for _, c in rows:
            with self.assertRaises(TypeError):
                c.tape[0] = 8


if __name__ == "__main__":
    unittest.main(verbosity=2)
