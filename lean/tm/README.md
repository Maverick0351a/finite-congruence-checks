# Pinned Lean Turing-machine oracle

This standalone Lake project executes the machine definitions from the pinned
`openai/math` file `lean/ComparatorChallenges/NavierStokesAlternating.lean`.
It compiles only the machine fragment. The complete upstream PDE source is
retained for provenance; this project does not check its PDE statements.

`source/manifest.json` binds the full source SHA-256, upstream commit, exact
byte and line span (10–66 inclusive), extraction, and generated module.
`MachineExtract.lean` adds narrow imports and a namespace wrapper around that
unchanged slice. The upstream snapshot and extraction carry the Apache-2.0
license in `source/LICENSE`.

With the pinned Lean 4.34.1 toolchain available, from this directory:

```sh
python check_source.py
lake exe cache get Mathlib.Logic.Function.Iterate Mathlib.Data.Int.Basic
lake build tmOracle MachineChecks
lake env lean MachineChecks.lean
lake env leanchecker MachineExtract MachineChecks
.lake/build/bin/tmOracle < cases.jsonl > results.jsonl
```

Each input line is one JSON object:

```json
{"id":"example","machine":{"n_states_minus_one":0,"n_alphabet_minus_one":0,"initial_state":0,"halting_states":[],"table":[[0,5,0]]},"input":[],"steps":2}
```

Rules are `null` or `[next_state, write_symbol, move]`, with move `0` meaning
left, `1` stay, and `2` right. Natural-number fields require nonnegative integer
JSON tokens. Booleans, decimal/exponent tokens, negative values, and moves
outside 0–2 fail. A malformed line produces a diagnostic on stderr and process
exit code 1, without a result for that line. Earlier valid lines may already
have produced output. Blank lines fail; an empty file ends successfully.

The adapter accepts all type-valid machine tuples, including those failing
upstream `WellFormed`, and inputs failing upstream `ValidInput`. It does not
truncate natural numbers to fixed-width integers or enforce alphabet bounds.
The example above deliberately writes a symbol outside its declared alphabet.

Output contains `id`, `steps`, `state`, `head`, `halted`, and `tape`:

```json
{"id":"example","steps":2,"state":0,"head":-2,"halted":false,"tape":[[-1,5],[0,5]]}
```

`tape` lists only nonzero cells, sorted by integer position. The initial support
lies in `[0,input.length-1]`; after `steps` moves the head lies in
`[-steps,steps]`. Therefore scanning
`[-steps,max(steps,input.length-1)]` contains every potentially nonzero cell.
This observation adapter is ordinary executable code; the support argument is
documented here, not claimed as a Lean theorem.

`MachineChecks.lean` contains five general kernel-checked statements about the
upstream step definition: an already halted configuration is fixed, a missing
instruction changes only the state to the sentinel, and a present instruction
has the stated update, writes its head cell, and preserves other cells.
Their axiom reports contain only `propext` and `Quot.sound`. They contain no
`sorry`, `native_decide`, or added axioms. These statements do not prove a
general equivalence with a Python implementation. Finite comparisons with the
compiled executable remain differential tests.

Local build/check logs are in `evidence/`. The repository-level runner owns
fresh build provenance and differential evidence. Rebuilding is necessary to
bind a binary to the maintained sources; a preexisting executable alone does
not establish that binding.
