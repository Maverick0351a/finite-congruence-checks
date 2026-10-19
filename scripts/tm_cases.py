"""Frozen deterministic cases for a bounded Python/Lean comparison.

These are specified encodings, not claims about Busy Beaver optimality. The
explicit variants restore a write-1/right-move halt instruction. The original
archive used a missing entry instead. See docs/TM_TRANSLATION_CHECKS.md.
"""
from __future__ import annotations

from itertools import product
import random


def machine(states, alphabet, initial, halting, table):
    return {"n_states_minus_one": states - 1,
            "n_alphabet_minus_one": alphabet - 1,
            "initial_state": initial, "halting_states": halting, "table": table}


def named_cases():
    """Return machine/input/time-bound triples whose full traces are compared."""
    cases = [
        ("missing-rule", machine(1, 2, 0, [], [None, None]), [], 2),
        ("write-stay-halt", machine(2, 2, 0, [1],
            [[1, 1, 1], [1, 1, 1], None, None]), [], 2),
        ("initially-halted", machine(1, 1, 0, [0], [[0, 9, 2]]), [], 2),
        ("erase-and-halt", machine(2, 2, 0, [1],
            [[0, 1, 0], [1, 0, 2], None, None]), [1], 3),
        ("left-loop", machine(1, 1, 0, [], [[0, 0, 0]]), [], 6),
        ("short-table", machine(2, 2, 1, [], [[0, 0, 1]]), [1, 0, 1], 3),
        ("large-natural-state", machine(1, 1, 2**80, [], []), [2**80], 2),
        # Natural input beyond the alphabet is legal in the source type, though
        # ValidInput is false. Address arithmetic can reach an extra table cell.
        ("above-alphabet-alias", machine(1, 1, 0, [],
            [None, None, [0, 0, 2]]), [2], 3),
    ]
    tables = {
        "bb2": ([[1, 1, 2], [1, 1, 0], [0, 1, 0], None], 3, 6),
        "bb3": ([[1, 1, 2], None, [2, 0, 2], [1, 1, 2],
                 [2, 1, 0], [0, 1, 0]], 1, 14),
        "bb4": ([[1, 1, 2], [1, 1, 0], [0, 1, 0], [2, 0, 0],
                 None, [3, 1, 0], [3, 1, 2], [0, 0, 2]], 4, 107),
    }
    for name, (table, halt_index, time) in tables.items():
        states = len(table) // 2
        cases.append((name + "-missing", machine(states, 2, 0, [], table), [], time + 1))
        explicit = list(table) + [None, None]
        explicit[halt_index] = [states, 1, 2]
        cases.append((name + "-write-right-halt",
                      machine(states + 1, 2, 0, [states], explicit), [], time + 1))
    return cases


def comparison_cases():
    cases = []

    def add(name, m, word, times):
        for n in times:
            cases.append({"id": f"{name}/step-{n}", "machine": m,
                          "input": word, "steps": n})

    for name, m, word, last in named_cases():
        add(name, m, word, range(last + 1))
    # Complete enumeration for this stated subdomain: one ordinary state,
    # two symbols, complete two-entry table, in-range transitions, either halt
    # set, four input words, times 0..4. 49*2*4*5 = 1,960 snapshots.
    rules = [None] + [[0, write, move] for write in range(2) for move in range(3)]
    for table_index, table in enumerate(product(rules, repeat=2)):
        for halted in (False, True):
            m = machine(1, 2, 0, [0] if halted else [], list(table))
            for wi, word in enumerate(([], [0], [1], [0, 1])):
                add(f"small-{table_index}-{int(halted)}-{wi}", m, word, range(5))
    # Additional reproducible samples exercise type-valid machines that need
    # not satisfy WellFormed or ValidInput, and short/extra tables.
    rng = random.Random(20261018)
    for i in range(100):
        table = [None if rng.randrange(5) == 0 else
                 [rng.randrange(4), rng.randrange(4), rng.randrange(3)]
                 for _ in range(rng.randrange(7))]
        m = machine(2, 2, rng.randrange(4),
                    [q for q in range(4) if rng.randrange(4) == 0], table)
        word = [rng.randrange(4) for _ in range(rng.randrange(5))]
        add(f"sample-{i}", m, word, (0, 1, 2, 3, 7, 16))
    return cases
