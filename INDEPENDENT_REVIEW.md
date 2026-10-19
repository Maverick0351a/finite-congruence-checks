# Original experiment: independent implementation and review

This records the original experiment review. The repository release adds
checks and fixes documented in [the release review](docs/RELEASE_REVIEW.md).

Reviewed 18 October 2026 by a subagent separate from the primary search author.
The review covers `search.py`, its tests, `run_experiment.py`, the search claims
in `README.md` and `METHOD.md`, and the mathematical seed reduction. The reviewer
wrote `verify_witness.py` directly from the pinned Lean predicate, without
importing the primary search. All agents used the same session and interpreter;
this is not external peer review or a mechanically checked proof.

**Outcome:** no blocking findings remain in this reviewed scope. Final packaged
integration results are recorded separately in `evidence/run-evidence.json`.
The separate algebra verifier and operation minimizer have their own checks;
this review does not claim an independent optimality audit of the minimizer.

## Mathematical and implementation review

The seed reduction is sound after the structural conditions hold. Reversing an
edge preserves its color and reverses every marked image, leaving equivalence
closure unchanged. Repeated orientations add nothing to the join or relation
union. Diagonal seeds contribute bottom and only reflexive edges. For a seed
set containing only diagonal pairs, the join is bottom, so the diagonal rule
forces every required target pair to have equal endpoints. Consequently every
other obligation is represented by a nonempty set of unordered nonloop edges.

The primary enumeration generates every symmetric, bottom-diagonal matrix in
the stated range. Structural pruning discards false conjuncts. Admissible maps
include all total functions, not only permutations. Canonicalization identifies
vertex relabelings with lattice colors fixed. The independent implementation
uses full matrices for canonicalization and bitset breadth-first search for
closure, while retaining literal ordered seed subsets including loops.

## Independent results

The complete replay regenerated all 143,685 labeled candidates across 32 rows.
It checked 1,459 structural survivors against 94,509,661 nonempty ordered seed
subsets. All 217 successful labeled matrices, 22 vertex classes, class members
and multiplicities agreed. All 22 reported representatives and the seven actual
minimum-certificate files passed separate literal checks.

The replay reproduced minima C2=2, C3=3, C4=4, B2=3, M3=3, N5=4 and B3=4.
For M4 it rejected all 816 structural survivors, supporting only the bounded
negative conclusion through four vertices. Saved B2, M3, N5 and M4 examples
exercise failures of connectivity after the structural checks pass.

Detailed triangle and order-separation rejection counts were independently
rechecked for all 32 rows. The replay now compares those counts too, using
triangle failure before order separation when both fail. This makes the
documentation's statement that every count was reproduced precise.

## Regression and evidence controls

- Independently reran all 17 search and literal-verifier unit tests successfully.
- Reviewed lattice, join, domain and explicit carrier-bound validation, including
  incomparable colors and a bottom element with a nonzero index.
- Verified that a smaller-bound rerun excludes an old witness from its new
  certificate registry. The runner uses the registry and verifies file hashes.
- Injected a child-stage exit code of 7: the runner returned 1 and saved
  `passed=false` with the failed command and log.
- Reusing a nonempty output directory returned 2 without changing prior evidence.
- Confirmed the pinned local comparator SHA-256 matches the documented digest.

The literal replay is reproducible through `verify_witness.verify_search_record`
and the delivered runner. Minimum-carrier claims are limited to the stated
finite examples and supported lower bound. Documentation correctly distinguishes
finite computation, the uncompiled comparator theorem, bounded failure, and
mathematical novelty.
