# Proposed second-domain pilot: two ways to halt

**Status: the executable foundation, five source step lemmas, four-pair atlas,
and first agent retrieval exercise are implemented. Pair-specific Lean
preservation theorems remain proposed.**
See [TM translation checks](TM_TRANSLATION_CHECKS.md) for the maintained port,
exact source extraction, test domain, and reproduction commands.
The [pair atlas](TM_ATLAS.md) and [retrieval record](TM_ATLAS_EVALUATION.md)
document the implemented observation records and the six-question guided run.
This follows the [archive review](ARCHIVE_REVIEW.md). Keep the completed
[grouping checker](GROUPING_CHECKER.md) and its evidence intact while testing
whether the atlas can explain a precise semantic difference in another domain.

## The question in plain language

A machine reads one tape cell and follows a rule. What happens on its last step
depends on how stopping is encoded:

```text
                         one step
blank tape, head at 0 ──────────────> halted, head at 0, cell 0 = 0
                         no rule

                         one step
blank tape, head at 0 ──────────────> halted, head at 0, cell 0 = 1
                      write 1, stay,
                     enter halt state
```

Both machines stop. Their final tapes differ. “Preserves halting” and “preserves
the final tape” are separate claims, each requiring its own evidence.

The source definitions are pinned in [the review record](ARCHIVE_REVIEW.md).
Import those exact definitions. If a minimal model is extracted instead, prove
its correspondence to the pinned definitions before attributing results to them.

## Freeze a tiny pair

Use the empty input, hence an all-zero initial tape and head position zero.
Both machines have two symbols, numbered 0 and 1.

1. **Missing-instruction machine.** One ordinary state, initial state 0, no
   declared halting states, and two missing instruction entries. A step enters
   the sentinel state 1 without writing or moving.
2. **Write-and-halt machine.** Two ordinary states, initial state 0, declared
   halting state 1. Each state-0 instruction writes 1, stays at the current
   position, and enters state 1. State-1 entries are missing and are never
   executed because the configuration is already halting.

The source's first two encoding fields store state and alphabet counts minus
one. Direction values are 0 for left, 1 for stay, and 2 for right. Record the
actual tables as data with stable IDs; English names do not identify a machine.

| Proposed observation on the empty input | Missing instruction | Write and halt |
|:--|:--|:--|
| First halting time | 1 step | 1 step |
| Head position at that time | 0 | 0 |
| Symbol at position 0 | 0 | 1 |
| Further steps | Same halted configuration | Same halted configuration |

This table states the pair-specific proof obligations. The native comparison
includes these two cases; it does not replace those remaining theorem obligations.
Matching the numeric final state alone would also be misleading: state 1 is a
sentinel in the first encoding and an ordinary declared halt state in the second.

## Small, reviewable deliverables

1. **Definitions and identity.** Save the two exact inputs, source revision and
   hashes, Lean toolchain, import path, and stable construction IDs.
2. **Lean claims.** Prove well-formedness of both machines, the missing-rule
   no-write/no-move behavior, the explicit transition's update behavior, first
   halting at step 1 for the pair, equality of the observed head positions,
   inequality of the final tapes witnessed at cell 0, and stability after
   halting. Retain fully qualified theorem names and axiom reports. Any broader
   preservation theorem must state its own input domain and hypotheses.
3. **Traces.** Save the initial and one-step configurations with the head,
   state, and changed cells explicit. The Lean theorem describes the entire
   tape; a finite displayed window does not establish equality of infinite tapes.
   Compare with an independently written reference for this bounded example,
   labeling execution tests separately from source proofs and binary refinement.
4. **Claim records.** Link each observation to its exact construction, input,
   definition, theorem, trace, checker version, assumptions, and limits. Record
   that halting agrees for this pair and input while final-tape agreement fails;
   do not promote the pair into a general translation theorem.
5. **Retrieval demonstration.** Ask an agent which observations agree, which
   differ, and why. Require citations to the specific records. Admission checks
   must reject altered writes, moves, source hashes, or claim-to-evidence links
   when the attached evidence no longer supports them. Preserve those controls.

Success means the atlas can answer a small semantic question accurately and
show the supporting definitions and evidence. It does not establish a general
Lean translator, universal verification, machine-code correctness, or verified
fluid simulation.

## Run alongside a harder feedback experiment

The [first repair pilot](REPAIR_BENCHMARK.md) scored 12/12 in both arms. With
only one distinct initially grouped pair, its initial counterexample was
inferable, leaving no measured feedback benefit.

For a second protocol, first study six objects initially grouped in blocks of
sizes **2, 2, 1, 1**. Keep the operation fixed, allow merges only, preserve a
designated separation, and require exactly two final groups. These constraints
exclude both trivial extremes. Select cases with multiple violations, multiple
permitted repairs where available, and no permitted repair.

Extend the specification and checker assurance to this six-object interface
before describing feedback as formally verified. Exhaustively enumerate the
15 coarsenings of the four initial blocks and filter by separation, final block
count, and preservation. Independently check the oracle. Forced-merge closure
alone is insufficient for the new exact-final-count constraint: additional
merges may be needed and may create new conflicts or violate the separation.

Use disjoint operation families for development and test, freeze the protocol
before test calls, and match model settings, context, attempt limits, and
resource budgets across feedback arms. Retain every prompt, response, checked
witness, repair, and impossibility decision. Report paired success, invalid
repairs, false impossibility claims, attempts, and resource use, including null
results and the limits of any small sample.

The two experiments answer different questions: whether precise feedback helps
repair decisions, and whether an agent can retrieve and explain property-specific
evidence across representations. Versioned local records are enough for both.
