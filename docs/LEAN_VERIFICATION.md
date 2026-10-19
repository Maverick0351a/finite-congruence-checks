# Lean verification

This component connects the finite experiment to explicit formal statements in
Lean. Its scope is two concrete algebras on four elements, for N5 and B3, and a
separate check of the actual upstream graph-criterion source.

**All four local checks passed with Lean 4.34.1:** the concrete N5/B3 build,
its bundled `leanchecker` kernel replay, the targeted upstream graph-criterion
build, and replay of the two upstream source modules. Every command returned 0.
The full upstream corpus has not been built.

## Concrete certificates

`lean/FiniteCongruenceChecks.lean` displays the complete color and order tables
from the saved N5/B3 JSON witnesses and the two unary operations selected by the
operation minimizer. It proves that their full congruence orders are the specified
N5 and B3 orders:

1. A symmetric reflexive Boolean relation on four points is determined by its
   six unordered off-diagonal pairs. There are exactly 64 such assignments.
2. `relation_complete` proves that **every** equivalence relation is covered by
   this representation. The finite calculation therefore covers all congruences,
   rather than only a supplied list of partitions.
3. `finite_classification` classifies which of the 64 assignments are
   equivalence relations preserved by the two displayed operations.
4. `all_congruences` transfers that classification to arbitrary Boolean
   relations on the carrier. `order_exact` and `theta_injective` establish the
   inclusion order and absence of duplicate lattice elements.
5. `all_relations` extends this to arbitrary **Prop-valued** relations, using
   classical logic to encode each relation as a Boolean relation.

The finite proofs use ordinary `decide`, whose proof is checked by Lean's kernel.
They do not use `native_decide`, `sorry`, or newly declared axioms. The successful
build printed these actual axiom dependencies for **both** N5 and B3:

| Declaration | Axioms reported by Lean |
| --- | --- |
| `finite_classification`, `all_congruences`, `representation` | `propext`, `Quot.sound` |
| `all_relations` | `propext`, `Classical.choice`, `Quot.sound` |

These are standard Lean axioms; no `sorryAx` or native evaluation axiom was
reported. These certificates do
not prove the correctness of the Python search, its exhaustiveness across all
candidate colorings, or the minimality of the selected operation sets.

Run from the repository root:

```text
python lean/check_data.py
cd lean
lake build
lake env leanchecker FiniteCongruenceChecks
```

The project pins `leanprover/lean4:v4.34.1`. The concrete certificate project has
no Mathlib or other external package dependencies. `check_data.py` checks the
explicit Lean tables against the JSON evidence and verifies the exact bytes of
the two vendored upstream source files.

The successful build log is in `lean/evidence/core-build.log`; the separate
replay result is in `lean/evidence/core-leanchecker.log`. Lean's bundled checker
replays the module's declarations through its kernel to detect environment
manipulation. It is not an external verifier with an independent implementation.

## Upstream graph criterion

Pinned source revision:
[`1581d4cbdd69a0faf34b2089614fe2a814316a6a`](https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a).

The actual solution is
[`OAI/Algebra/Universal/GraphCriterion.lean`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Universal/GraphCriterion.lean),
which imports
[`Congruence.lean`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Universal/Congruence.lean)
and four Mathlib modules. Both are copied verbatim under `lean/upstream/OAI/`;
the existing upstream Apache-2.0 license in `reference/LICENSE` applies to these files.

| Source file | SHA-256 |
| --- | --- |
| `GraphCriterion.lean` | `bd80c2bea95ee1b4f7118fc8dc272aebac7b23038ba93cdafd386dc1b688fb50` |
| `Congruence.lean` | `30e9201344dcf4069ca9ace276c76dc3b1507d09f0f6bfbf5a7c5d693ac9716c` |

The upstream toolchain is Lean 4.34.1 and its Mathlib revision is
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The small project under
`lean/upstream/` uses those same pins and only this theorem's dependency closure.
It avoids fetching unrelated packages from the full corpus build. This is a
targeted build environment, not a build of the full upstream repository.

The successful targeted build compiled `Congruence.lean`, `GraphCriterion.lean`,
and `UpstreamAudit.lean` after retrieving the 723-module Mathlib dependency cache.
The compiled source bytes match the vendored repository files, and all nine
dependency checkouts match `lean/upstream/lake-manifest.json` with clean working
trees. This provenance is recorded in `lean/evidence/upstream-environment.json`.

```text
cd lean/upstream
lake update
lake exe cache get Mathlib.Data.Fin.Tuple.Basic Mathlib.Data.Setoid.Basic Mathlib.Order.Hom.Basic Mathlib.Data.Finset.Lattice.Fold Mathlib.Data.Fintype.EquivFin Mathlib.Data.Fintype.Pi Mathlib.Data.Fintype.Prod
lake build
lake env leanchecker -v OAI.Algebra.Universal UpstreamAudit
```

`UpstreamAudit.lean` imports the actual theorem and prints its type and axiom
dependencies. This is distinct from the official comparator workflow: the
comparator file intentionally ends with a placeholder proof, while the solution
module contains the proof to be checked. A source review shows the same key
definitions and theorem statement; this repository does not present that review
as an official comparator run.

The build and replay logs are `lean/evidence/upstream-build.log` and
`lean/evidence/upstream-leanchecker.log`. The actual axiom report is:

| Upstream declaration | Axioms reported by Lean |
| --- | --- |
| `graph_criterion` | `propext`, `Classical.choice`, `Quot.sound` |
| `graphOrderIso` | `propext`, `Classical.choice`, `Quot.sound` |
| `principalColor_isGraphWitness` | `propext`, `Classical.choice`, `Quot.sound` |

No `sorryAx` or native evaluation axiom is reported. The dependency cache and
official Lean distribution are part of the build's trust boundary; the replay
checks the two OAI modules and audit module against their imported environment.
It does not freshly replay every imported Mathlib declaration.

## Relationship and limits

The concrete certificates formalize congruence classification for the saved
N5/B3 constructions. The Boolean threshold relation is exactly the table test
`color(x,y) ≤ bound`. They do not yet instantiate the upstream `IsGraphWitness`
predicate or prove a formal equivalence between the Python graph-connectivity
implementation and its `Relation.EqvGen` definition. That graph condition has
separate exhaustive Python evidence in this repository.

The upstream theorem is a supporting graph characterization. As stated in the
corpus scope note, it does not establish the associated manuscript's
undecidability or subgroup-interval conclusions. No new mathematical result or
external peer review is claimed here.

## Work log

- 2026-10-19 UTC: Read the actual pinned solution and its one local dependency.
  Confirmed the upstream toolchain and Mathlib pins from the source files.
- 2026-10-19 UTC: Added a small dependency-free certificate project, an explicit
  completeness argument for the finite relation enumeration, and a separate
  targeted upstream project. Added a passing JSON-to-Lean table consistency
  check and upstream source hashes. Compiler validation remains pending at this
  point in the log.
- 2026-10-19 00:26 UTC: Verified the official Lean archive SHA-256, ran Lean
  4.34.1 and Lake 5.0.0, and compiled both concrete examples successfully.
  The first attempt needed explicit case splitting over the six Boolean
  coordinates because Std has no automatic decision instance for that product
  quantifier. After this repair, `lake build` returned 0; the axiom report is
  recorded above. Upstream dependency preparation and kernel replay continue.
- 2026-10-19 00:26 UTC: `lake env leanchecker FiniteCongruenceChecks` completed
  successfully with exit 0 and no diagnostic output.
- 2026-10-19 00:39 UTC: The targeted upstream build and bundled kernel replay
  both passed. The initial cache command required module names because Mathlib
  is installed as a dependency. A slow source-hashing attempt on WSL's mounted
  Windows filesystem was stopped and moved to a native WSL scratch directory.
  The archive copy flattened three documentation/benchmark symlinks; their
  pinned Git versions were restored before compilation. All dependency trees
  were then verified clean, all pinned revisions matched, and the compiled
  project source bytes matched the repository. The theorem files were unchanged.
  This remains a targeted check; no official comparator or full corpus run was
  performed.
