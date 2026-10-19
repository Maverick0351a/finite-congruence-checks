"""Executable port of the Turing machine defined in openai/math

    lean/ComparatorChallenges/NavierStokesAlternating.lean  (namespace OAI.AlternatingNS)

Adapted from the supplied Python port, retaining the source semantics while
checking Python inputs against Lean's Nat/Int/Fin types. Bounded helpers are
Python additions, not definitions of unbounded decidable halting. See
docs/TM_TRANSLATION_CHECKS.md for exact provenance and the tested boundary.
Lean source for reference:

    abbrev Rule    := N x N x Fin 3
    abbrev Machine := N x N x N x List N x List (Option Rule)

    def states        (M) := M.1 + 1
    def alphabet      (M) := M.2.1 + 1
    def initialState  (M) := M.2.2.1
    def haltingStates (M) := M.2.2.2.1
    def table         (M) := M.2.2.2.2
    def instruction (M) (q a) := (M.table[q * M.alphabet + a]?).join

    structure Configuration where
      state : N ; head : Z ; tape : Z -> N

    def isHalting (M) (c) := decide (c.state = M.states or c.state in M.haltingStates)
    def initial (M) (w) := { state := M.initialState, head := 0,
                             tape := fun i => if 0 <= i then w[i.toNat]?.getD 0 else 0 }
    def step (M) (c) :=
      if M.isHalting c then c else
        match M.instruction c.state (c.tape c.head) with
        | none   => { c with state := M.states }
        | some r => { state := r.1, head := c.head + (r.2.2.val - 1),
                      tape := Function.update c.tape c.head r.2.1 }
    def run (M) (w) (n) := (M.step)^[n] (M.initial w)
    def Halts (M) (w)   := exists n, M.isHalting (M.run w n)
"""
from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass, field, replace
from types import MappingProxyType

LEFT, STAY, RIGHT = 0, 1, 2          # Fin 3; offset is (val - 1)


def _nat(value, name):
    if type(value) is not int or value < 0:
        raise ValueError(f"{name} must be a nonnegative integer")


def _list(value, name):
    if type(value) not in (list, tuple):
        raise ValueError(f"{name} must be a list or tuple")
    return tuple(value)


@dataclass(frozen=True)
class Rule:
    """Lean: N x N x Fin 3 -- (next state, symbol written, move)."""
    next_state: int
    write: int
    move: int                         # 0,1,2 -> offset -1,0,+1

    def __post_init__(self):
        _nat(self.next_state, "next_state")
        _nat(self.write, "write")
        if type(self.move) is not int or self.move not in (LEFT, STAY, RIGHT):
            raise ValueError("move must be 0, 1 or 2 (Lean Fin 3)")


@dataclass(frozen=True)
class Machine:
    """Lean: N x N x N x List N x List (Option Rule).

    Note the off-by-one encoding: `states` is `M.1 + 1`, so a machine always
    has at least one state and `n_states_minus_one` is what is stored.
    """
    n_states_minus_one: int
    n_alphabet_minus_one: int
    initial_state: int
    halting_states: tuple[int, ...]
    table: tuple[Rule | None, ...]

    def __post_init__(self):
        for name in ("n_states_minus_one", "n_alphabet_minus_one", "initial_state"):
            _nat(getattr(self, name), name)
        stop = _list(self.halting_states, "halting_states")
        table = _list(self.table, "table")
        for q in stop:
            _nat(q, "halting state")
        if any(r is not None and type(r) is not Rule for r in table):
            raise ValueError("table entries must be Rule or None")
        object.__setattr__(self, "halting_states", stop)
        object.__setattr__(self, "table", table)

    @property
    def states(self) -> int:
        return self.n_states_minus_one + 1

    @property
    def alphabet(self) -> int:
        return self.n_alphabet_minus_one + 1

    def instruction(self, q: int, a: int) -> Rule | None:
        """Lean: (M.table[q * M.alphabet + a]?).join -- out of range is `none`."""
        _nat(q, "state")
        _nat(a, "symbol")
        idx = q * self.alphabet + a
        if idx < 0 or idx >= len(self.table):
            return None
        return self.table[idx]

    def well_formed(self) -> bool:
        """Lean: WellFormed -- initial state in range, halting states in range,
        targets in range for instructions addressed by in-range state/symbol
        pairs. Lean does not require the table to have exactly states*alphabet
        entries, and ignores extra unaddressed entries in this predicate."""
        if not self.initial_state < self.states:
            return False
        if any(not (q < self.states) for q in self.halting_states):
            return False
        for q in range(self.states):
            for a in range(self.alphabet):
                r = self.instruction(q, a)
                if r is not None and not (r.next_state < self.states and r.write < self.alphabet):
                    return False
        return True

    def valid_input(self, w) -> bool:
        """Lean: ValidInput -- every input symbol below the alphabet size."""
        return type(w) in (list, tuple) and all(
            type(a) is int and 0 <= a < self.alphabet for a in w)


@dataclass(frozen=True)
class Configuration:
    state: int
    head: int
    tape: Mapping[int, int] = field(default_factory=dict)  # finite support, else 0

    def __post_init__(self):
        _nat(self.state, "state")
        if not isinstance(self.tape, Mapping):
            raise ValueError("tape must map integer positions to natural symbols")
        if type(self.head) is not int or any(type(i) is not int for i in self.tape):
            raise ValueError("head and tape positions must be integers")
        for symbol in self.tape.values():
            _nat(symbol, "tape symbol")
        # Lean values are immutable. Copy and freeze caller-owned containers so
        # a validated state or previously returned trace cannot change later.
        object.__setattr__(self, "tape", MappingProxyType(dict(self.tape)))

    def read(self, i: int) -> int:
        if type(i) is not int:
            raise ValueError("tape position must be an integer")
        return self.tape.get(i, 0)

    def written(self) -> dict[int, int]:
        return {k: v for k, v in self.tape.items() if v != 0}


def is_halting(M: Machine, c: Configuration) -> bool:
    """Lean: c.state = M.states OR c.state in M.haltingStates.

    `M.states` is one past the last valid state -- an out-of-range sentinel the
    `none` branch of `step` jumps to when no rule applies.
    """
    return c.state == M.states or c.state in M.halting_states


def initial(M: Machine, w) -> Configuration:
    """Natural-valued input; ValidInput is a separate predicate, as in Lean."""
    w = _list(w, "input")
    for symbol in w:
        _nat(symbol, "input symbol")
    return Configuration(state=M.initial_state, head=0,
                         tape={i: a for i, a in enumerate(w)})


def step(M: Machine, c: Configuration) -> Configuration:
    if is_halting(M, c):
        return c
    rule = M.instruction(c.state, c.read(c.head))
    if rule is None:
        return replace(c, state=M.states)
    tape = dict(c.tape)
    tape[c.head] = rule.write
    return Configuration(state=rule.next_state,
                         head=c.head + (rule.move - 1),
                         tape=tape)


def run(M: Machine, w, n: int) -> Configuration:
    _nat(n, "steps")
    c = initial(M, w)
    for _ in range(n):
        c = step(M, c)
    return c


def halts(M: Machine, w, fuel: int = 100_000) -> tuple[bool, int, Configuration]:
    """Search times 0..fuel inclusive, executing at most fuel transitions.

    Return (halted, n, run(M,w,n)), where n is the first halting time within
    the bound or fuel if none was observed. False is not proof of nonhalting.
    """
    _nat(fuel, "fuel")
    c = initial(M, w)
    for n in range(fuel + 1):
        if is_halting(M, c):
            return True, n, c
        if n < fuel:
            c = step(M, c)
    return False, fuel, c


def trace(M: Machine, w, limit: int = 40):
    """Yield at most limit configurations (including time zero), stopping at halt."""
    _nat(limit, "limit")
    c = initial(M, w)
    for n in range(limit):
        yield n, c
        if is_halting(M, c):
            return
        c = step(M, c)
