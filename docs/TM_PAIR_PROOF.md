# One exact Turing pair, with a proof

Two machines can stop at the same time while leaving different results. The
`tiny-stay` pair makes that distinction small enough to inspect completely.
Both start in state zero, with their heads at position zero and a blank tape.

| Machine | Its first action | First halt | Head | Entire resulting tape |
| --- | --- | ---: | ---: | --- |
| Left: missing instruction | Enter the sentinel halt state; preserve head and tape | 1 | 0 | Zero at every integer position |
| Right: explicit instruction | Write `1`, stay in place, enter explicit halt state | 1 | 0 | `1` at zero; zero at every other integer position |

```text
                     one transition
blank tape ── missing instruction ──> blank tape, halted
blank tape ── write 1, stay, halt ───> one 1 at position 0, halted
```

The proof covers the infinite tape, including every cell outside a drawing.
For every integer `i`, it establishes

```text
left tape(i)  = 0
right tape(i) = if i = 0 then 1 else 0
```

It separately proves that neither machine is halted at step zero and that
both are halted at step one. Since times are natural numbers, those facts
establish **first halt after exactly one transition**. The universal tape
quantifier does not broaden the input scope: the input is exactly `[]`.

## Follow the evidence

- [Exact machines and theorem](../lean/tm-pair/TinyPair.lean):
  `TMOracle.TinyPair.exact_result` combines initial nonhalting, halting after
  one step, both head positions, both whole-tape formulas, and tape inequality.
- [Generated Lean binding](../lean/tm-pair/TinyPairBinding.lean): named equality
  proofs bind both complete machine tuples and the exact input to atlas data.
  A further declaration requires the selected theorem to inhabit a separately
  generated target expressed with `Machine.run` on those literals.
- [Supplemental claim](../evidence/tm-pair-proof-v1/claim.json):
  `tm:tiny-stay:formal-result:v1`, with exact inputs, conclusion, declarations,
  assumptions, scope, citations, and links to separate execution evidence.
- [Proof receipt](../evidence/tm-pair-proof-v1/summary.json): source hashes,
  toolchain version, pinned dependency revisions, exact commands, durations,
  logs, axiom reports, kernel replay, and deliberate-error results.
- [Pinned upstream definition](../lean/tm/source/manifest.json): links the
  unchanged extracted machine definitions to OpenAI math family 376. Its
  surrounding fluid-flow argument is outside this theorem.

The original `tm:tiny-stay:tape:v1` record remains a saved execution claim.
Its historical limits describe that snapshot. The context interface attaches
this separately identified formal supplement; it does not relabel the
original native receipt. `query_atlas.py`, frozen records, and browser copies
retain their existing meaning.

## Reproduce from a fresh checkout

Prerequisites: Git, Python 3.10 or newer, and `lake` from an installed Lean
toolchain manager. The project pins Lean 4.34.1 and its dependency revisions.
Use Linux, macOS, or WSL for the full Lean run. No API key or model is needed.

```sh
git clone https://github.com/Maverick0351a/finite-congruence-checks.git
cd finite-congruence-checks
# While PR #11 is open, select its reviewed branch:
git checkout codex/n5-source-context
python scripts/tm_pair_proof.py run --out runs/tm-pair-fresh
python scripts/tm_pair_proof.py replay --out runs/tm-pair-fresh
python scripts/query_context.py explain tm:tiny-stay:tape:v1 --out proposed-tm.json
python scripts/query_context.py check proposed-tm.json
```

Record `git rev-parse HEAD` when reporting a replication. The `run` command
checks source extraction, restores pinned dependencies/cache, compiles the
proof and binding, audits elaborated declarations, runs `leanchecker`, and
tests the invalid bindings. It requires a new output directory and retains
failed runs. CI executes the same command in a separate job.

For a quick offline check of retained evidence, including on Windows:

```sh
python scripts/tm_pair_proof.py replay
python -m unittest discover -s scripts -p 'test_tm_pair_proof.py' -v
python -m unittest discover -s scripts -p 'test_context_tm.py' -v
```

Offline replay checks the saved receipt; it does not rerun Lean. Matching
hashes identifies the artifacts and is not by itself a mathematical proof.
These records are not signed or authenticated build attestations.

## Deliberate errors

The real Lean probes reject a changed unused rule, a different input `[0]`,
an unrelated existing theorem, a different tape conclusion, a theorem about
only one tape cell, and a theorem proving halting without the complete first
halt result. The `[]` and `[0]` inputs describe the same blank tape, and the
changed unused rule preserves this run; exact object equalities still reject
both substitutions.

A seventh probe supplies the desired statement using `sorry`. Lean accepts
the declaration with a warning, but the axiom gate rejects `sorryAx`.
The audit includes both the original result and all four binding declarations.
Missing, duplicated, or unknown axiom reports also fail. Standard reported
axioms are retained explicitly rather than described as absent.

Python controls check changed claim types and conclusions, substituted step
two, wrong commands or working directories, missing logs/reports, source
changes after verification, and redirected local dependencies. These controls
test the evidence interface; the Lean build checks the mathematical result.

## Trust boundary and work record

This theorem concerns the formal machines. It does not prove that the Python
simulator, native JSON adapter, compiled executable, or compiler implements
those definitions. [Native agreement evidence](TM_TRANSLATION_CHECKS.md)
remains separate, with its original bounded coverage and exact build identity.
The theorem is not general translation equivalence or a fluid-simulation proof.

On 2026-10-19, the pair proof was placed in its own Lake project so the frozen
native-build source hashes remain intact. Review tightened UTF-8 handling,
strict JSON type matching, command provenance, and the local dependency path.
The final local Lean run passed all 13 stages, including kernel replay and
seven deliberate-error probes. Local Python validation passed 128 tests:
10 proof-evidence, 23 context/query, 50 atlas, and 45 simulator/evidence tests.
Independent review also passed the 10 proof-evidence and 12 Turing context
tests and found no remaining actionable issues. CI results for the current
commit are recorded in
[PR #11](https://github.com/Maverick0351a/finite-congruence-checks/pull/11).
The four agent benchmark answering sessions remain paused.
