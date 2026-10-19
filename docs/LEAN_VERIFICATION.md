# Lean verification

This component connects the finite experiment to explicit formal statements in
Lean. Its scope is two concrete algebras on four elements, for N5 and B3, and a
separate check of the actual upstream graph-criterion source.

**Concrete N5/B3 build and bundled `leanchecker` kernel replay: passed locally
with Lean 4.34.1 (both exit 0).** The targeted upstream build is in progress.
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

```text
cd lean/upstream
lake update
lake exe cache get Mathlib/Data/Fin/Tuple/Basic.lean Mathlib/Data/Setoid/Basic.lean Mathlib/Order/Hom/Basic.lean Mathlib/Data/Finset/Lattice/Fold.lean Mathlib/Data/Fintype/EquivFin.lean Mathlib/Data/Fintype/Pi.lean Mathlib/Data/Fintype/Prod.lean
lake build
```

`UpstreamAudit.lean` imports the actual theorem and prints its type and axiom
dependencies. This is distinct from the official comparator workflow: the
comparator file intentionally ends with a placeholder proof, while the solution
module contains the proof to be checked. A source review shows the same key
definitions and theorem statement; this repository does not present that review
as an official comparator run.

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
