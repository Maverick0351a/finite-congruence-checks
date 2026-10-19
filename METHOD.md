# Exact scope and verification method

This experiment implements the finite predicate `OAI.FiniteCongruence.IsGraphWitness`
from openai/math revision `1581d4cbdd69a0faf34b2089614fe2a814316a6a`.
The unchanged source and family scope note are in `reference/`. The comparator
source SHA-256 is `2ee495def2e1228bf13df520f6c66699ec22b2cd3bc1ae7383a30957aae9f967`.
Its final theorem uses `sorry`: this file specifies the criterion; it supplies
no checked proof of the general equivalence. The actual solution is a separate
module. Current formal-check status is in [LEAN_VERIFICATION.md](docs/LEAN_VERIFICATION.md);
these Python implementations have not been proved equivalent to Lean.

## Input and predicate

Each certificate contains the full finite lattice order and join tables and an
n-by-n color matrix. Indices identify lattice elements; they are not numerical
order comparisons. Each implementation validates the poset, its bottom, every
least upper bound, and existence of every greatest lower bound. Graph carriers
are nonempty. A valid witness has all five properties:

1. Symmetry: c(x,y) = c(y,x).
2. Bottom exactly on the diagonal: c(x,y) = bottom iff x = y.
3. Join triangle inequality: c(x,y) <= c(x,z) join c(z,y).
4. Order separation: whenever a is not <= b, some c(x,y) is <= a and not <= b.
5. For every nonempty set S of ordered vertex pairs, every pair whose color is
   below the join of the seed colors lies in the equivalence closure of the
   images of S under all admissible maps.

A map p is admissible when c(p(x),p(y)) <= c(x,y) for every ordered pair.
The quantifier over maps includes all n^n total functions, including constant
and noninjective maps. Marked edges are the union of seed images over those
maps. Equivalence closure includes reflexivity, symmetry and transitivity.

## Complete search in the stated range

`search.py` checks eight explicit lattices and every positive carrier size
through four. For an m-element lattice it enumerates exactly
(m-1)^(n(n-1)/2) assignments to the upper triangle. It reflects them to the
lower triangle and puts bottom on the diagonal. This generates every symmetric
matrix with bottom exactly on the diagonal once. Triangle or separation failures
can be discarded because the full predicate is a conjunction. Every remaining
matrix undergoes the connectivity test; the search continues after finding a
witness, so the recorded counts cover the whole range.

All eight built-in definitions are given as cover relations and independently
validated as lattices. B3 uses subset inclusion on three bits, with bitwise OR
as its resulting join table. M4 is the six-element lattice with four incomparable
atoms between bottom and top. These names describe selected test lattices,
not a survey of all lattices of their sizes.

Successful matrices are grouped only by permutations of their vertices. Colors
remain fixed. Counts called "classes" do not quotient by lattice automorphisms,
and do not classify arbitrary algebra signatures. All class representatives
and labeled multiplicities are retained in `search-results.json`.

## Why the primary seed reduction is exact

These observations apply after the first four conditions have passed:

- Reversing a seed leaves its color unchanged, and reverses each image edge.
  Equivalence closure already adds both directions, so reversal has no effect.
- Repeated orientations contribute no new undirected marked edge or join term.
- A diagonal seed contributes bottom to the join and only diagonal marked edges.
  Those pairs are already in every equivalence closure by reflexivity.
- A seed set consisting only of diagonal pairs has join bottom. Any target pair
  below bottom has color bottom and hence equal endpoints, so its obligation
  holds by reflexivity.

Every other ordered seed set therefore has exactly the same obligation as its
set of unordered, nonloop seed edges. There are 2^(n(n-1)/2)-1 such nonempty
sets, at most 63 here. Checking admissibility on unordered nonloop pairs also
suffices, because symmetry handles the reverse orientation and a map sends
equal endpoints to equal endpoints. The primary implementation uses union-find
to compute closure. It caches only results determined by identical marked edge
sets. Finite joins use the validated join table, never `max` on color indices.

## Independent replay

`verify_witness.py` imports no primary search code. It checks all ordered pairs
for admissibility and enumerates all 2^(n^2)-1 nonempty ordered seed subsets,
including loops and both orientations. At n=4 this is 65,535 subsets. It uses
bitset breadth-first search for equivalence closure. It caches evaluations with
identical join bounds and marked relations, while still enumerating every seed
subset and recording their total. This cache does not use the unordered-seed
reduction.

Its `verify_search_record` routine independently regenerates every candidate,
checks structural conditions afresh, applies the ordered-seed verifier to every
structural survivor, and groups successful matrices using full matrices under
every vertex permutation. It compares candidate counts, survivor counts,
connectivity failures, witnesses, classes, each class multiplicity and minima.
Thus a missing candidate or class cannot be concealed by verifying only the
primary program's saved successful examples. The shipped replay covers 143,685
candidates, 1,459 structural survivors and 94,509,661 ordered seed subsets across
those survivors. Representative rechecks and individual certificate rechecks
are additional to that seed total.

## Independent finite algebra recovery

`verify_algebra.py` imports neither implementation above. For each certificate it
forms theta_a = {(x,y): c(x,y) <= a}, verifies these are equivalence relations,
enumerates every total unary function, and enumerates every set partition of
the carrier using restricted-growth strings. It retains exactly the partitions
preserved by all admissible unary functions. This is the full congruence set
of the explicit unary algebra with those functions as its basic operations.

The checks require distinct theta_a, equality of the recovered congruences with
that collection, and agreement of every order comparison. They also check
independently that admissible functions are exactly the functions preserving
all theta_a. An order isomorphism between these finite lattices preserves their
lattice structure. This route establishes each small algebra example without
invoking the general graph-criterion theorem. It does not establish that theorem
for arbitrary lattices.

## Minimum operation lists for a fixed representation

For each of the seven saved minimal-carrier witnesses, the desired congruences
are fixed concrete partitions, not merely an abstract isomorphism type. Every
unary operation in a representation of these partitions must preserve every
one of them. Therefore it belongs to the full pool already enumerated by the
independent algebra calculation. Each other carrier partition must be broken
by at least one selected operation, or it would be an unwanted congruence.

This is a finite set-cover problem: unwanted partitions are the universe, and
each allowable operation covers the partitions it fails to preserve. Covering
the universe is both necessary and sufficient. Equivalent coverage masks can
share a representative without affecting the optimum. An exact optimization
and a separately implemented optimality check are recorded by
`minimize_operations.py`, together with the complete congruences recovered from
the selected operation list. The two zero-operation results are meaningful:
every partition is desired in those examples, so the covering universe is empty.

Minimal operation counts apply to this fixed concrete representation and unary
operations. They do not minimize simultaneously over all graph classes, all
carrier sizes, abstractly isomorphic embeddings, or operations of higher arity.
The finite algebra example can be checked directly from its short operation
tables and its complete partition list.

## Carrier minimality and limits

The first four conditions embed the target lattice into equivalence relations
on n points by a -> theta_a. Symmetry and the diagonal rule give reflexivity and
symmetry; the triangle inequality gives transitivity. Separation reflects order.
Every strict increase of an equivalence relation merges blocks. Therefore a
chain with h strict steps needs n >= h+1 points. This bound also holds directly
for congruences of every finite algebra, with any operation arities.

All seven recovered examples meet that bound, so their carrier sizes are
minimal, subject to computational correctness. The elementary bound is not
claimed as new. M4 passes no full witness test at n<=4. We conclude only this
bounded negative result from the search; we do not claim M4 is unrepresentable.

The search and verifiers are separate implementations by separate agents in
the same session, running on the same Python interpreter. They are not an
external peer review or a machine-checked proof. Shared misunderstandings and
implementation defects remain possible. Known controls, independent enumeration
methods, exact tables, source hashes and reproducible commands make the claims
inspectable. No claim of mathematical novelty, general nonrepresentability,
undecidability, or validation of the whole corpus follows from this experiment.

## Evidence handling

The `certificates` registry in `search-results.json` lists the witnesses from
that invocation with SHA-256 hashes. It is authoritative if `search.py` is run
again with a smaller bound or a narrower lattice list in an old directory;
unlisted files can be leftovers. `run_experiment.py` requires a new or empty
output directory, passes only registered certificates to its verifiers, and
records commands, exit statuses, interpreter, source hashes and output hashes.
An incomplete or failed run never reports overall success.

The corpus files in `reference/` are included under the accompanying upstream
license. The generated example data and Python tools are local experimental
artifacts. No network, API key, package installation or corpus checkout is
needed to rerun the finite experiment.
