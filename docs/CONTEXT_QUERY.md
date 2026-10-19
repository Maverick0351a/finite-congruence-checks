# Query the meaning and evidence of an N5 claim

The first context interface supports two exact construction claims and one
comparison. It reads the same saved N5 record as the website, validates its
pinned inputs, and returns JSON. It runs locally using the Python standard
library. No model, credentials, network access, or new Lean run is needed.

```sh
python scripts/query_context.py explain context:family-206:saved-n5:classification:v1
python scripts/query_context.py explain construction:n4-E16709
python scripts/query_context.py compare
```

| Claim ID | Construction ID | Evidence attached here |
| --- | --- | --- |
| `context:family-206:saved-n5:classification:v1` | `saved:family-206:n5:v1` | Exact local Lean classification with a recorded build and kernel replay |
| `construction:n4-E16709` | `atlas:n4-E16709:displayed-operations:v1` | Exhaustive computation with an independent finite check |

`n4-E16709` identifies a relation-family atlas entry. Its construction ID above
specifically names the displayed operation tables at this version. A lattice
shape name such as `N5` is not an accepted claim ID.

An `explain` result includes:

- The exact claim and construction IDs, carrier, ordered operation tables,
  and complete grouping family.
- The compatibility predicate, its quantifiers, conclusion (`statement`),
  assumptions, scope, evidence status, and limits.
- Source paths, hashes, pinned revision references, and applicable Lean
  declarations with exact names, statements, roles, and line links.
- The hash of the website's context record and a description of the binding
  check's limits.

The saved construction uses `FiniteCongruenceChecks.N5.all_relations` for
completeness, `order_exact` for inclusion order, and `theta_injective` for
distinctness. These declarations refer to fixed saved definitions. The atlas
answer has an empty `applicable_lemmas` list and an explicit absence-of-proof
note for its different displayed tables. Its original atlas claim and
independent review references remain intact.

The correspondence is a small, finite calculation:

```text
Saved objects          Rename by [1,3,2,0]          Atlas objects
{0,1,2,3}  ------------------------------------>  {0,1,2,3}
five valid groupings   ------------------------>  same five groupings
inclusion order        ------------------------>  same N5 order
two operation tables   ------------------------>  DIFFERENT tables
```

`compare` includes both claim records and the page's exact correspondence.
It reports the point permutation, the index map between the grouping lists,
the conjugated saved operations, the atlas operations, and the independent
review references. The builder checks all 15 partitions for each construction
and checks the inclusion-order correspondence. The operation lists differ
under **this bijection**; the interface makes no claim about algebra
isomorphism under all possible permutations. It does not transport the saved
Lean proof to the other operation list.

## Validate a proposed record

Export an answer directly to UTF-8 JSON, then check it:

```sh
python scripts/query_context.py explain context:family-206:saved-n5:classification:v1 --out proposed-n5.json
python scripts/query_context.py check proposed-n5.json
```

`check` compares the complete parsed export with the registered result for its
claim ID. Object-key ordering and JSON whitespace do not matter. List order,
field presence, values, and types do matter, including `true`, `1`, and `1.0`.
Unknown claim IDs never fall back to a shared shape name. Duplicate JSON keys
and nonstandard numeric constants are rejected.

| Outcome | Exit code | Output |
| --- | ---: | --- |
| Valid query or exact registered record match | 0 | JSON on stdout; `check` reports `supported` |
| Proposed record differs or names an unknown claim | 1 | JSON on stdout with `unsupported`, mismatch paths, and candidate hash |
| Malformed input, invalid query, missing/stale source, or I/O error | 2 | JSON error on stderr; stdout is empty |

The candidate hash is SHA-256 of canonical JSON (sorted object keys, compact
separators, UTF-8, no ASCII escaping). Source file hashes separately normalize
CRLF to LF. These hashes identify data; they do not prove a mathematical claim.
`check` preserves the proposed file and does not silently repair it. It accepts
`explain` exports only, not comparison results or free-form English answers.

Here **supported means an exact registered record match**. Applicability is
manually curated as `curated_exact_binding`; the query does not ask Lean to
elaborate a supplied theorem or derive whether a different theorem applies.
Changing a fact makes the proposed record unsupported by this binding even
when that fact could be established by a separate argument. Equivalent wording
also needs review and a registered update. This is an evidence interface, not
a semantic-equivalence grader.

For example, replacing saved `g = [0,1,0,1]` with `f ∘ g = [1,0,1,0]` leaves
the five valid groupings unchanged. The current proof reference still names
the original tables. The test therefore requires an unsupported result; a
matching diagram alone cannot authorize that reference.

## Reproduce the controls

```sh
python scripts/build_n5_context.py --check
python -m unittest discover -s scripts -p 'test_n5_context.py' -v
python -m unittest discover -s scripts -p 'test_context_query.py' -v
node scripts/check_n5_context.cjs
```

The controls include both valid exports, the exact comparison, changed rules
with unchanged groupings, swapped construction IDs, a real B3 theorem in the
same hashed proof file, removed evidence or assumptions, a broadened
conclusion, malformed JSON, incorrect numeric types, and stale page data.

The interface is separate from `query_atlas.py`, so its claim registry and the
frozen semantic-context benchmark need no changes. This milestone tests
deterministic record binding. It does not measure improved agent reasoning or
meaning preservation in natural-language explanations; the four benchmark
answering sessions remain paused pending approval.

See [the N5 walkthrough](N5_SOURCE_CONTEXT.md) for the mathematical explanation,
source roles, general graph criterion, and recorded Lean trust boundary.
