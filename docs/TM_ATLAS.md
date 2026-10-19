# Turing examples in the atlas

The atlas now asks three separate questions about each exact pair of machines:
**when do they stop, what is on the tape, and where is the head?** Each answer
has its own claim ID, assumptions, limits, and evidence citations.

Open the [Turing comparison panel](https://maverick03511-finite-congruence-checks.static.hf.space/atlas.html#turing)
or use the local query tool. This first collection has four pairs, all starting
with a blank tape and head at position zero. It reuses the existing claim and
citation format. The 39 grouping-family entries retain their own dataset and
classification scope.

## Reading a comparison

The simplest pair stops after one step in both encodings:

```text
                              first halt
Missing instruction:       [0]  →  [0]     head: 0
Write 1, stay, then halt:   [0]  →  [1]     head: 0
                            ↑       ↑

Halting time: same     Tape: different     Head position: same
```

The head marks the cell being read; cells not listed in a sparse tape contain
zero. Tape equality compares the complete sorted list of nonzero cells, not
just the number of ones. For these finite runs this represents the entire tape.

| Pair ID | First halt, left / right | Complete final tape | Final head, left / right |
|:--|--:|:--|--:|
| `tm-pair:tiny-stay:v1` | 1 / 1 | Different | 0 / 0 |
| `tm-pair:bb2:v1` | 6 / 6 | Equal | -1 / 0 |
| `tm-pair:bb3:v1` | 14 / 14 | Equal | 1 / 2 |
| `tm-pair:bb4:v1` | 107 / 107 | Different at cell -10 | -10 / -9 |

Left always means the missing-instruction encoding. Right means the explicit
write-and-halt variant; it stays in the tiny pair and moves right in the BB
pairs. BB2 and BB3 use a chosen local final-instruction convention. These names
do not establish a unique canonical Busy Beaver encoding or optimality.

## Query exact properties

```sh
python scripts/query_atlas.py tm
python scripts/query_atlas.py tm --pair tm-pair:bb2:v1 --property tape
python scripts/query_atlas.py tm --pair tm-pair:bb2:v1 --property head_position
python scripts/query_atlas.py build-tm --check
```

The first command returns all 12 claim records. Optional filters select an
exact pair and/or `halting_time`, `tape`, or `head_position`. Unknown IDs fail
explicitly; a BB2 record cannot answer a BB5 question. For example,
`tm:bb2:tape:v1` and `tm:bb2:head_position:v1` describe different properties
of the same pair. IDs identify assertions; the registry hash fixes the exact
wording and values being read.

The Turing query has its own evidence status, assumptions, and limits. It does
not inherit the grouping catalog's exhaustive-classification status.

## Follow a claim to evidence

- [Pair registry](../evidence/tm-atlas-v1.json): exact machines, blank input,
  three claim records per pair, and qualified lemma links.
- [Trace document](../evidence/tm-atlas-traces-v1.json): JSON-pointer targets
  for the complete step prefixes, first halt, final configurations, and lemmas.
- [Native build receipt](../evidence/tm-port-v1/summary.json): the tested binary,
  source versions, build checks, and 2,857-configuration comparison.
- [Native inputs](../evidence/tm-port-v1/inputs.jsonl) and
  [outputs](../evidence/tm-port-v1/lean.jsonl): original line-addressed observations.

The existing citation triple is unchanged: `path`, `json_pointer`, `sha256`.
Each derived trace also retains exact native/input JSONL line locators and raw
file hashes. JSON citations normalize CRLF to LF, as the existing atlas does;
native-artifact locators state their raw-byte hash convention explicitly.
The browser opens the selected trace locally and shows its citation. An
ordinary GitHub JSON link is not treated as a JSON-pointer viewer.

First-halting-step claims depend on every observation from time zero through
the first halt. A final halted snapshot alone cannot establish *first* halt.
Tape and head claims point to the corresponding first-halt configurations.
The saved extra post-halt snapshot is visible but is not counted as a later
halting time.

The source lemma `TMOracle.Checks.missing_instruction` requires an active
configuration and a missing instruction. It proves that the Lean step changes
only the state. `instruction_step` describes the write and movement of a
present instruction; `instruction_writes` identifies the old head cell.
The links state these hypotheses. They explain the source behavior; they do
not turn a bounded pair comparison into a proof of the Python implementation.

## Reproduce and evaluate

```sh
python scripts/run_tm_checks.py replay --out evidence/tm-port-v1
python scripts/query_atlas.py build-tm --check
python -m unittest discover -s scripts -p 'test_atlas*.py' -v
node scripts/check_tm_atlas_ui.cjs
```

Rebuild derived records with `python scripts/query_atlas.py build-tm` after
reviewing any intentional source change. Offline replay checks saved evidence;
fresh native execution is documented in [TM translation checks](TM_TRANSLATION_CHECKS.md).

The [six-question retrieval exercise](../benchmarks/tm-evidence-v1/tasks.json)
tests exact pair/property selection, source-lemma applicability, rejection of
universal-equivalence claims, and an absent BB5 pair. Its structured scorer
checks evidence identities, values, citations, and explicit scope. Free-text
explanations and lemma hypotheses receive a separate review. See the
[evaluation record](TM_ATLAS_EVALUATION.md) for the actual run and limitations.

This collection establishes observations about these exact encodings on blank
input. It is not a general translation theorem, a binary-refinement proof, or
verification of the surrounding fluid-equation development.
