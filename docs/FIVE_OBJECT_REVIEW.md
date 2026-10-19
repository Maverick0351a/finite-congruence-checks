# Independent review of the five-object minimum example

Reviewed 19 October 2026. Verdict: **approve the implementation**. No unresolved
correctness finding remains in the reviewed sources and recorded checks.
Protected-branch CI remains a separate merge gate. This is an independent
AI-assisted review within the implementation chat, not external peer review.

## Mathematical obligations

The intended result concerns two exact relation families on five named objects.
The required upper bounds are the displayed three-rule construction A and
two-rule construction B. Lower bounds must exclude arbitrary total unary maps,
including repeated rules and empty signatures, rather than merely exclude
subsets of the displayed rules. Classification must cover arbitrary
proposition-valued equivalence relations.

The inclusion-order correspondence uses lexicographically ordered canonical
groupings and the map `[0,2,4,1,3,5,6,7]`. Independently checking all 64 order
comparisons confirms that it is an order isomorphism. A different map in the
historical pilot reflects a different order of the B records.

## Checks completed during development

- An independent literal related-pair calculation enumerated 52 partitions
  from all 3,125 label assignments and all 3,125 unary maps. It recovered the
  eight declared groupings for each displayed construction.
- A has 67 maps preserving its target family. No single map or unordered pair,
  including a repeated map, gives exactly that family. B has 63 preserving
  maps; none works alone, and the displayed pair works.
- The independent Python audit imports no project mathematics. Its separate
  tests also construct partitions by inserting elements into blocks and check
  preservation through block images.
- The Lean base defines compatibility for arbitrary proposition-valued
  relations and proves the bridge to Boolean relations. It also proves that
  every map on `Fin 5` has a five-entry table.
- The complete proof source covers arbitrary maps through obstruction-profile
  certificates. Identity padding handles empty and shorter signatures, and
  no distinctness assumption is placed on the rules.
- The generated finite certificates cover all 1,024 reflexive symmetric
  Boolean relations and all 3,125 unary tables for each family. Splitting
  these into smaller declarations changes the reduction workload; each
  declaration still requires a Lean proof, and the generator is not trusted.
- All 26 focused audit and proof-receipt tests passed independently during
  review, including query acceptance, changed-claim rejection, invalid domains,
  stale hashes, altered logs, missing stages, and forbidden axioms. The diagram was
  independently rendered and visually inspected: the labels, inclusion edges,
  direction, and explanatory text are legible without overlaps or clipping.
- The native-runtime build log records successful compilation of all six
  project modules, including the exact binding. All 29 axiom reports were
  inspected and use only `propext`, `Classical.choice`, and `Quot.sound`.
  Generated-certificate freshness also passed independently.
- The [complete saved proof receipt](../evidence/five-object-v1/proof/summary.json)
  replays successfully against the current 14 source hashes and 21 artifacts.
  It records all 12 stages: version, build, axiom audit, kernel replay, and eight
  deliberate-error checks. The kernel command explicitly targets all six
  project modules and exits successfully. Receipt replay independently
  recomputes the finite Python audit.
- The CI changes preserve the existing job names, require a fresh proof run,
  replay its receipt, check generated data, run the focused tests, and retain
  the generated proof evidence. Hosted CI completion is assessed separately.

## Deliberate-error diagnostics

Each saved negative-control log was read. These are mathematical or theorem
application failures, rather than missing imports, malformed commands, or
environment setup failures.

| Changed input | Observed Lean rejection |
| --- | --- |
| Operation table | The required equality to the registered A operations is false. |
| Grouping conclusion | The required equality to the registered A groupings is false. |
| Grouping correspondence | The required equality to the proved correspondence is false. |
| Grouping count | The required conclusion contains the false equality `8 = 7`. |
| Order conclusion | The required conclusion contains `false = true`. |
| Minimum count | The stronger lower-bound premise cannot be discharged, and `3 = 4` is false. |
| B classification substituted for A | The theorem's operations and relation family do not match the required type. |
| B lower bound substituted for A | A bound excluding at most one rule cannot discharge the required bound excluding two. |

## Findings resolved during development

1. The initial audit CLI allowed its output to overwrite its input file.
   It now rejects output paths resolving to an input or checker source; a
   regression test preserves the original input bytes.
2. The initial audit reported 520 pair comparisons per unary map as a count.
   Since preservation checks short-circuit, this is now labeled as a maximum.
3. The initial walkthrough used unescaped vertical bars inside Markdown table
   cells. The block displays now use unambiguous separators.
4. The initial proof runner only hashed the current Lake configuration. It
   now checks the exact pinned toolchain, reviewed TOML, and empty dependency
   manifest and rejects an alternate executable Lake configuration before
   invoking the build.
5. The initial machine-readable predicate referred to preservation of an
   arbitrary relation without explicitly requiring equivalence. It now says
   that the relation must be an equivalence relation preserved by the rules,
   matching the actual Lean type.
6. The initial diagram explanation said every paired node had two different
   concrete meanings. Three corresponding groupings coincide; the corrected
   text makes that explicit.

## Scope of this review

The result establishes exact-family minima on the named five-object carrier,
complete classifications, and an inclusion-order correspondence. Mathematical
novelty, shape-wide optimization, larger carriers, higher-arity signatures,
and model performance are outside this milestone. The Python implementation
and exporter have no formal correctness proof; saved receipts are inspectable
records, not authenticated attestations or new kernel executions.

An earlier interrupted attempt encountered the Windows filesystem bridge.
That incomplete attempt is excluded from the mathematical results. The
reviewed complete receipt comes from a clean-source build using the pinned
native Linux Lean runtime.
