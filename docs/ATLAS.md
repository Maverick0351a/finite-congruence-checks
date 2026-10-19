# A readable atlas of finite congruence representations

The atlas follows one story: **objects → rules → consistent groupings → shape**.
Start with the three-object lesson, then explore the catalog and compare two
ways to produce the same four-level chain.

[Open the atlas](https://maverick03511-finite-congruence-checks.static.hf.space/atlas.html)
or open `space/atlas.html` directly from a downloaded repository. The atlas
embeds its data locally and requires no server or internet connection.

## How to read an entry

- **Objects** are the points on which the rules act. The mathematical name for
  this set is the carrier.
- **Rules** are unary operations: each takes one object and returns one object.
- **Consistent groupings** are partitions preserved by every rule. These are
  the congruences. Two inputs in one group must have outputs in one group.
- **Shape** shows how the consistent groupings fit together. Each node is a
  whole grouping; moving up merges groups. Lines join immediate refinements.

Changing a grouping in the lesson gives a concrete pass or failure explanation.
In the catalog, the operations, grouping display, and lattice diagram all refer
to the same object labels. Technical details and downloadable JSON provide the
complete data behind the simplified view.

## What the catalog covers

The atlas classifies representable exact congruence relation families on
nonempty carriers of one through four points. It includes empty operation lists.

| Objects | Exact families with object labels fixed | Families after renaming objects | Abstract lattice shapes on this carrier |
|:--|--:|--:|--:|
| 1 | 1 | 1 | 1 |
| 2 | 1 | 1 | 1 |
| 3 | 8 | 4 | 4 |
| 4 | 303 | 33 | 21 |

There are **313 exact labeled families**, **39 representatives after object
relabeling**, and **22 abstract shapes across all four carrier sizes**. Some
shapes occur at more than one carrier size, so the last column must not be
summed to obtain 22.

These are three different ways of counting. Renaming objects preserves the
actual grouping structure. Abstract shape also forgets which objects occupy
the groups, retaining only the order between whole groupings. The catalog
does not enumerate every possible choice of algebra operations.

The original graph search has a separate result of **22 colored-graph classes**
for its eight named targets, with lattice colors fixed. Its count of 22 and
this atlas's count of 22 abstract shapes count different things.

## Why compare constructions?

Two four-object entries have the same shape, C4, a chain of four groupings.
One requires one unary operation and the other requires two for its exact
relations. Both carrier sizes attain the chain-height lower bound. This shows
why an operation minimum must name the representation being minimized.

Each atlas entry includes a smallest operation list for that entry's exact
relations and carrier. This does not establish a minimum over larger carriers
or operations with multiple inputs. The three-object B2 lesson is linked to
the saved construction in the [illustrated introduction](PLAIN_LANGUAGE_GUIDE.md).

## Reproduce the classification

From the repository root, with Python 3.10+ and Node.js 18+:

```sh
python scripts/build_atlas_data.py --check
python scripts/check_atlas.py --check-receipt evidence/atlas-review.json --out runs/atlas-review.json
python scripts/query_atlas.py build-claims --check
python -m unittest discover -s scripts -p 'test_atlas*.py' -v
node scripts/check_atlas_ui.cjs
```

The exporter starts from the complete small-family enumeration used by the
operation audit, groups families under object permutations, and compares their
inclusion orders. It computes a minimum operation list in each representative's
own labels. `evidence/atlas.json` is the canonical dataset; `space/atlas-data.json`
and `space/atlas-data.js` are generated copies for download and offline display.

The separate checker derives its own partitions and unary-map preservation
results without importing the exporter's mathematical routines. It exhausts
candidate relation families and checks closure, object-relabeling classes,
abstract order isomorphisms, operations, and minima. Corruption controls test
that incorrect data is rejected. The retained result is
[atlas-review.json](../evidence/atlas-review.json).

Text source hashes use the encoding declared in the dataset so Windows and
Linux line endings do not create false differences. A successful freshness
check regenerates all exported data and compares it to the saved files.

## Evidence status

The new classification is **exhaustive finite computational evidence** checked
by separate algorithms. It is not a Lean proof of the atlas or of the Python
programs. Its implementation and review used AI assistance; external peer review
and mathematical novelty have not been established.

The existing formal result covers the exact saved N5/B3 colored graphs. A shared
shape name on an atlas entry does not extend that proof to a different graph.
See [the claim ledger](CLAIMS.md) and [the Lean record](LEAN_VERIFICATION.md).
The five/six-point research pilot and proposed conjectures are outside this atlas.

The static browser illustrates the checked data and evaluates small grouping
examples. It does not rerun the exhaustive classification or Lean proofs.

For structured retrieval, use the [local query interface](ATLAS_QUERY.md).
It exposes the same dataset with claim-level evidence and precise citations.
The [infrastructure direction](INFRASTRUCTURE.md) describes how this can grow
into a reusable evidence interface, with retrieval correctness as its first test.
