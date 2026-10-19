# Release review

This review was performed by an AI subagent separate from the repository's
primary author, in the same session and Python runtime. It is implementation
review with independent algorithms, not external peer review or a formal proof.

## Scope and current status

The review covers the Python graph verifier, algebra verifier, unary operation
minimizer, and their evidence and input-handling contracts. It also covers the
README, method note, claim ledger, evidence guide, contribution guide, and CI
configuration. Carrier and operation minima are stated within their actual
bounds. After the repairs below, no unresolved blockers were found within this
reviewed scope.

The final recorded Python run passes `scripts/check_evidence.py` against the
current root Python source hashes. Its eleven child stages succeeded, its unit
test log records 33 passing tests, and its output registry is complete. The
supplementary minima audit's script and minimizer hashes also match the current
files. Root Python sources use LF line endings, matching the repository checkout
policy. CI configuration was reviewed locally; its hosted execution status is a
separate record.

Three reproducible input/evidence findings were reported and repaired:

1. The algebra checker accepted a string or object instead of the required list
   of lattice element labels.
2. An unreadable algebra-check input aborted the batch before writing failure
   evidence and could leave an earlier success report at the requested output.
3. A minimizer input with an array as its lattice name saved a success report
   and then failed while formatting the console summary.

Regression tests confirm all three repairs. Assertion-based self-checks were
also replaced with explicit checks. Deliberately broken partition enumerators
are now rejected even when the Python interpreter runs with `-O`.

The integrity checker previously accepted an incomplete output-hash registry
and checked only the number of successful stages. It now requires the complete
expected registry and each unique expected stage. Regression tests reject a
missing digest, a duplicated stage, changed output bytes, and a filename that
escapes the evidence directory. A simulated child exit code of 7 produces a
runner exit code of 1 and saved `passed=false` evidence. A nonempty destination
is rejected without changing its contents. All **33** unit tests pass.

## Independent operation-minimum audit

`scripts/audit_operation_minima.py` provides a third algorithm, written during
this review. It generates equivalence relations by enumerating symmetric binary
tables and checking transitivity. It enumerates every total unary map and
computes that map's complete family of invariant equivalence relations.

The empty signature starts with all equivalence relations. Adding an operation
intersects the current family with the relations preserved by that operation.
Breadth-first search over these intersections therefore finds every family
representable by a unary algebra on the fixed carrier and its smallest operation
count. These independent answers are derived before importing the production
minimizer. The comparison calls only its public `choose_operations` function;
it does not reuse its partition generator, preservation predicate, or set-cover
implementations.

| Carrier size | Equivalence relations | Total unary maps | All representable families checked | Minimum counts 0 / 1 / 2 |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 1 | 1 | 1 | 1 / 0 / 0 |
| 2 | 2 | 4 | 1 | 1 / 0 / 0 |
| 3 | 5 | 27 | 8 | 1 / 7 / 0 |
| 4 | 15 | 256 | 303 | 1 / 136 / 166 |

All **313** representable families agreed. All impossible target families for
carriers of sizes 1–3 were also rejected, as were 32 impossible four-point
families containing both equality and the universal relation: **60** negative
controls in total. This audit completes in under one second on the review
machine; runtime is descriptive and not a performance guarantee.

These counts describe labeled, concrete families of equivalence relations.
They are neither lattice-isomorphism counts nor a claim of mathematical novelty.
The audit does not minimize higher-arity signatures or compare all embeddings
of a named abstract lattice.

Run from the repository root:

```console
python scripts/audit_operation_minima.py --out runs/operation-minima-audit.json
```

The JSON records the reviewed minimizer and audit-script SHA-256 digests. A
nonzero exit status and `passed=false` indicate a failed audit.

## Mathematical boundaries checked

- Every basic unary operation in a representation of the exact target relations
  must preserve those relations. Each unwanted equivalence relation must fail
  preservation for at least one selected operation. This justifies the set-cover
  objective and the removal of duplicate or empty destruction masks.
- Zero operations are permitted by the pinned corpus's algebra definition.
  Their congruences are all equivalence relations, giving the saved C2 and M3
  examples on carriers of sizes two and three respectively.
- A strict chain of `h` inclusions between equivalence relations needs at least
  `h+1` carrier points, since every inclusion reduces the number of blocks. The
  seven positive examples meet this lower bound, supporting their stated
  minimum carrier sizes.
- The M4 search outcome is bounded to carriers of sizes one through four. No
  conclusion about all larger carriers is warranted.
- The graph predicate has five conjuncts. Structural validity alone does not
  certify the connectivity condition. The literal verifier includes ordered
  seed pairs and loops, whereas the search uses the documented reduction.

## Limits

The concrete Lean theorem statements also received a focused read-only review.
`relation_complete` covers every Boolean equivalence relation on the four-point
carrier, and `all_relations` extends the classification to arbitrary
proposition-valued relations using classical logic internally. Callers do not
need to supply a decidability assumption. The `Representation` fields provide
soundness, completeness, exact inclusion comparisons, and injectivity; separate
theorems establish the displayed orders' partial-order laws. No logical scope
gap was found in these statements. This is statement review, not compiler or
kernel verification, and does not check the general upstream proof.

The earlier independent search replay is described in `INDEPENDENT_REVIEW.md`.
This reviewer has not repeated that full replay merely to duplicate an unchanged
calculation. The primary agent ran the final pipeline, and this review checked
its source and output bindings. Lean compilation and proof results have their
own record in [LEAN_VERIFICATION.md](LEAN_VERIFICATION.md); this review does not
claim an independent Lean build. Python results alone establish neither the
general graph-criterion theorem nor the manuscript's broader claims.
