# Query the atlas as structured evidence

The same small, checked catalog can support a human explanation and a software
query. This local interface returns JSON with explicit claims, assumptions,
limits, and citations to individual evidence records. It requires Python 3.10+
and the standard library. It uses no model, network connection, database, or
running service.

The same CLI also exposes [Turing pair evidence](TM_ATLAS.md):
`python scripts/query_atlas.py tm --pair tm-pair:bb2:v1 --property tape`.
That collection reuses the claim/citation fields but has its own bounded
execution status, source-lemma links, and scope. The grouping commands below
continue to query the finite congruence catalog.

## Ask a concrete question

“Can the same shape need different numbers of rules on the same number of objects?”

```sh
python scripts/query_atlas.py compare --shape C4 --carrier 4
```

The answer contains two four-object representations of the four-level chain:

| Stable entry ID | Minimum unary rules | Rules, as zero-based output lists |
|:--|--:|:--|
| `n4-E16403` | 1 | `[1,2,3,3]` |
| `n4-E16457` | 2 | `[0,3,3,3]`, `[2,0,0,1]` |

An output list gives the result for object 0, then object 1, and so on. The first
rule sends 0 to 1, 1 to 2, 2 to 3, and 3 to itself. These representations have
the same abstract shape, but different exact groupings. Each minimum applies to
its own groupings on its own fixed four-object carrier. The comparison does not
assert that the abstract shape itself requires two rules.

Each returned entry cites its full record, partitions, operations, and minimum
field in `evidence/atlas.json`, plus its record in `evidence/atlas-review.json`.
Every citation includes a content hash. A reader or agent can follow the
evidence before making the comparison in natural language.

## Commands

Run these from the repository root:

```sh
# List all entries or intersect exact filters.
python scripts/query_atlas.py list
python scripts/query_atlas.py list --carrier 4 --shape C4 --min-rules 1

# Read the complete operations, partitions, order, and covers of one entry.
python scripts/query_atlas.py show n4-E16403

# Compare a shape within each carrier size. Distinct sizes are separate groups.
python scripts/query_atlas.py compare --shape C4 --carrier 4

# Find every same-carrier shape group whose exact-family minima differ.
python scripts/query_atlas.py compare

# Read the evidence, assumptions, and limits attached to claims.
python scripts/query_atlas.py claims --entry n4-E16403
python scripts/query_atlas.py claims

# Rebuild or check all three deterministic claim-registry copies.
python scripts/query_atlas.py build-claims
python scripts/query_atlas.py build-claims --check
```

`--shape` accepts a display name such as `C4`, a snapshot-local type label such
as `T06`, or the stable `poset-v1:<sha256>` key returned by a previous query.
Matching is case-insensitive and exact. `--min-rules` means **exactly** that
minimum number, not an upper or lower bound. Filters are combined with AND.
Zero is a genuine minimum for an empty operation signature; it never means
missing information. A valid filter with no matching entries returns an empty
`results` list. Unknown shapes and entry IDs are errors.

The supported query vocabulary is deliberately small. For example, a request
for a Lean-proved atlas entry cannot be satisfied by treating a shared `N5` or
`B3` name as a proof link. The current evidence status is computational.

## Versioned response contract

Successful commands exit with status 0 and write one UTF-8 JSON object to
standard output. It has these fields:

| Field | Meaning |
|:--|:--|
| `schema_version` | Integer `1`, the response contract version |
| `status` | `ok` |
| `command`, `query` | Requested command and effective supplied filters |
| `dataset`, `review` | Repository-relative source path and normalized SHA-256 content identifier |
| `scope` | Unary-operation minima on exact relation families and fixed carriers |
| `evidence_status` | `exhaustive_computation_independently_checked` |
| `assumptions`, `limits` | Explicit conditions and boundaries that accompany the answer |
| `results` | List of entry summaries, full entries, comparisons, claims, or build results |
| `citations` | Deduplicated supporting citations from the returned results |

Entry summaries include `id`, `carrier_size`, `abstract_type`, `name`,
`shape_key`, `lattice_elements`, `minimum_unary_operations`, `orbit_size`,
`claim_ids`, and `citations`. `show` also includes the complete atlas entry.
Comparison results group one shape on one carrier size and expose
`minimum_rule_counts`, `has_different_minima`, and the contributing entries.
Without `--shape`, `compare` returns only groups with different minima. With a
shape specified, it includes that shape's selected carrier groups even if all
their minima agree.

Failures exit with status 2, leave standard output empty, and write one JSON
object to standard error: `schema_version: 1`, `status: "error"`, and `error`.
The conventional `--help` option displays human-readable usage text.

## Exact data meanings and stable identity

The canonical dataset is [`evidence/atlas.json`](../evidence/atlas.json).
Its structural contract is [`schema/atlas-v1.schema.json`](../schema/atlas-v1.schema.json).
Structural schema validation does not prove the mathematical values; the
independent checker performs the mathematical cross-check.

- Object labels are the integers `0,...,n-1`.
- A partition is a canonical block-label list. Equal entries identify objects
  in the same block; blocks are numbered by first appearance.
- An operation is a length-`n` list whose entry at index `x` is the image of
  object `x`.
- `order[i][j]` is true exactly when partition `i` refines partition `j`.
- `covers` lists `[lower, upper]` partition indices with no allowed partition
  strictly between them. These edges describe refinement, not operations.
- `orbit_size` counts exact labeled families obtained by renaming the objects.
- `minimum_unary_operations` minimizes the number of basic unary operations
  for the exact displayed family, with no cost charged for derived operations.

An entry ID has the form **`nN-EM`**. In schema version 1, `N` is the carrier
size and `M` is a decimal bit mask with the following fixed definition:

1. List unordered object pairs `(0,1), (0,2), ...` in lexicographic order.
2. Visit their Boolean membership vectors in lexicographic order, `false`
   before `true`. Add the diagonal and symmetric counterparts, and retain
   exactly the transitive relations. This fixes an order on all equivalence
   relations of the carrier.
3. Give retained relation index `i` bit weight `2**i`. Add the weights of the
   relations in the family.
4. Take the smallest mask over all permutations of the object labels. The
   displayed family realizes that canonical mask.

The query checks this identity against the displayed partitions. The ID names
a concrete relation-family orbit, not a particular list of operations or an
abstract lattice shape. A different minimum operation list for the same exact
family does not change its ID. Implementations that change this identity
algorithm must introduce a new identity version; they must not reinterpret an
existing schema-v1 ID. Pair the ID with `schema_version: 1` when storing it.

`T01`, `T02`, and similar `abstract_type` labels are assigned while discovering
shapes. They are **local to this dataset snapshot** and must not serve as stable
cross-version identifiers. Display names are also presentation labels.

The query adds a stable shape key **`poset-v1:<sha256>`** from the independent
review. The version-1 canonicalization groups lattice nodes by the pair
`(number of nodes below, number of nodes above)`, counting the node itself.
It sorts those invariant pairs, exhausts all node permutations within each
group, flattens each full order matrix row by row into bytes `0` or `1`, and
hashes the lexicographically smallest byte string with SHA-256. This is the
algorithm in `scripts/check_atlas.py`'s `canonical_order`, not a hash of a
diagram or a `Txx` label. A changed canonicalization requires a new prefix.
As with any digest, the key relies on SHA-256 collision resistance.

## Claim records and citations

[`evidence/atlas-claims.json`](../evidence/atlas-claims.json) is a deterministic
claim registry, with `schema_version: 1` and namespace
`finite-congruence-atlas/claims-v1`. It contains:

- `census:carriers-1-4`: the complete bounded census;
- `construction:<entry-id>`: each entry's exact operation/partition construction;
- `minimum:<entry-id>`: each exact-family unary-operation minimum;
- `comparison:<shape-key>:nN`: each same-shape, same-carrier comparison group.

Every claim has a `statement`, `kind`, `evidence_status`, `scope`, `assumptions`,
`limits`, and `citations`. Entry claims also name their `entry_id`, carrier,
shape key, and display labels. Comparison claims list their contributing
`entry_ids`. Claim IDs identify the question or assertion being tracked;
the registry content hash identifies the exact recorded wording and values.

A citation contains `path`, `json_pointer`, and `sha256`. The path is relative
to the repository root. The pointer addresses the parsed JSON using JSON Pointer
syntax: `/entries/9/operations`, for example, means the operations field of
array item 9. Array positions may change in another snapshot, so a pointer must
always travel with its source hash. Hashes cover UTF-8 bytes with CRLF normalized
to LF and no other changes. They detect changed content; they do not authenticate
an author or independently prove correctness.

The registry binds the atlas, independent review, and query-generator source
hashes. `build-claims` writes the evidence registry, an identical
`space/atlas-claims.json`, and `space/atlas-claims.js`, which exposes
`window.ATLAS_CLAIMS` for offline browsers. `build-claims --check` checks all
three copies. The browser and CLI therefore consume the same claim records.

Before serving a query, the tool checks the dataset/review link, generator and
source hashes, entry identity, reviewed minima, and reviewed shape-key mapping.
Every read command also checks registry freshness before advertising claim IDs. It reads the saved review rather
than claiming to have re-executed the exhaustive classification.

To regenerate the full evidence chain after an intentional data change:

```sh
python scripts/build_atlas_data.py
python scripts/check_atlas.py --out evidence/atlas-review.json
python scripts/query_atlas.py build-claims
python scripts/query_atlas.py build-claims --check
python scripts/test_atlas_query.py
```

The [query evaluation record](ATLAS_QUERY_EVALUATION.md) records a concrete
agent-style question, the cited answer, and the independent contract tests.
The next infrastructure steps are described in the project roadmap; this
foundation provides file-backed evidence retrieval, not a general theorem
prover or a production agent service.
