# Finite Congruence Checks

[![Reproduce and verify](https://github.com/Maverick0351a/finite-congruence-checks/actions/workflows/verify.yml/badge.svg)](https://github.com/Maverick0351a/finite-congruence-checks/actions/workflows/verify.yml)
[![Recorded Lean 4.34.1 checks passed: concrete N5/B3 and targeted upstream modules](charts/lean-checks-badge.svg)](docs/LEAN_VERIFICATION.md)
[![Release v0.1.0](charts/release-badge.svg)](https://github.com/Maverick0351a/finite-congruence-checks/releases/tag/v0.1.0)
[![License: Apache 2.0](https://img.shields.io/badge/license-Apache%202.0-315B78)](LICENSE)
[![Python: 3.10+](https://img.shields.io/badge/python-3.10%2B-315B78)](#quick-start)

Research tools for exact mathematical claims: finite constructions, independent
checks, and scoped Lean proofs. Compare representations, inspect their hypotheses,
and trace a result back to its source and reproducible evidence.

The project builds on selected results from **[OpenAI Math](reference/README.md)**,
starting with the graph-witness criterion in family 206 and extending to exact
Turing-machine examples and Snaky on finite boards. Source revisions and claim
boundaries are recorded separately for each result. This is independent work;
source attribution does not imply OpenAI affiliation or endorsement.

The broader goal is to discover useful technical capabilities and foundational
technology through sustained mathematical work. AI architectures are one possible
direction. Mathematical progress, failed approaches and reusable methods inform
what to investigate next; novelty and performance gains remain research goals.

**[Explore the research atlas](https://huggingface.co/spaces/Maverick03511/finite-congruence-checks)** ·
**[Inspect exact claims](docs/CLAIMS.md)** · **[Reproduce a result](#quick-start)** ·
**[Read the Lean evidence](docs/LEAN_VERIFICATION.md)** · **[Research roadmap](docs/ROADMAP.md)**

The repository is the canonical source. The hosted Space is a separate deployment;
see the [publication record](docs/HUGGING_FACE_DEMO.md#publish) for its recorded revision.

| Research capability | Evidence and limits |
|:--|:--|
| [Enumerate finite constructions](docs/ATLAS.md) | 39 representatives and 22 abstract shapes through four objects; independently checked finite computation. |
| [Compare exact claims](docs/ATLAS_QUERY.md) | Stable entry IDs, fixed-carrier operation minima, hypotheses and source citations. A shared shape name does not transfer a proof. |
| [Inspect proof correspondence](docs/CONTEXT_QUERY.md) | Exact saved N5/B3 constructions, proved N5 renamings and selected Turing claims; each has its own scope and binding. |
| [Follow finite-board Snaky](docs/SNAKY_FINITE_BOARD.md) | The existing paper result is formalized for its 251-cell envelope and containing 17 × 17 square; an example play is separate from the 21-claim guarantee. |

The original graph experiment searches eight specified lattices on carriers of
size **one through four**, checks every quantified condition independently, and
recovers minimum unary-operation lists for fixed representations. It uses only
Python's standard library. Its totals below are separate from the atlas counts.

| Candidate colorings | Full witnesses | Vertex classes | Saved examples |
|:--|:--|:--|:--|
| **143,685** | **217** | **22** | **7** minimum-carrier constructions |

The HTML gallery is self-contained and works offline. Download the repository
and open `docs/index.html` in a browser; GitHub displays HTML source in its file
viewer. Each figure is also available as PNG and editable SVG in `charts/`.

## Compare constructions and inspect evidence

Use the **[interactive atlas](https://maverick03511-finite-congruence-checks.static.hf.space/atlas.html)**
to move between the construction map, exact entry records and claim citations.
The current source keeps map, catalog, detail and export selection synchronized.
Its claim inspector separates saved finite computation from formal or model
checks that are not supplied for that entry. The yellow/black interface emphasizes
objects, rules and evidence; a worked example explains the diagram notation.

The catalog contains **39 grouping-family representatives** after renaming
objects, covering **22 abstract lattice shapes**. Compare two four-object
constructions with the same chain shape but different minimum rule counts.
Use the **[Cytoscape map](https://maverick03511-finite-congruence-checks.static.hf.space/atlas.html#shape-map)**
to follow construction-to-shape connections, compare rule counts, and open each
entry's evidence. [How to read the map](docs/ATLAS_MAP.md).
These counts describe congruence families and are separate from the original
colored-graph search totals above. [Scope and independent checks](docs/ATLAS.md).

For one complete source-linked example, open `space/context-n5.html` or read
the [N5 walkthrough](docs/N5_SOURCE_CONTEXT.md). Try all 15 groupings, see why
exactly five survive, and follow the source map from the original question to
the exact Lean classification and graph-witness bridge. The comparator target
with `sorry`, completed upstream proof, and local verification record have
separate links. The atlas's N5 entry uses different rule tables; the page shows
the checked renaming of its grouping family without transferring the proof.

Download the repo and open `space/atlas.html` for an offline copy. For a text
walkthrough or presentation script, use the [illustrated introduction](docs/PLAIN_LANGUAGE_GUIDE.md).

## Query examples and evidence

The atlas also provides a small local interface for research tools and agents.
Query the same versioned records used by the website, with stable entry IDs,
claim-level assumptions and limits, and citations to supporting JSON records.

```sh
python scripts/query_atlas.py compare --shape C4
python scripts/query_atlas.py show n4-E16403
python scripts/query_atlas.py claims --entry n4-E16403
```

Explain an exact N5 claim or one Turing tape claim, or compare the two N5 constructions with the
[source-context interface](docs/CONTEXT_QUERY.md):

```sh
python scripts/query_context.py explain context:family-206:saved-n5:classification:v1
python scripts/query_context.py compare
python scripts/query_context.py explain tm:tiny-stay:tape:v1
```

The Turing export includes a [proof for the exact pair](docs/TM_PAIR_PROOF.md):
both machines first halt after one step, both heads stay at zero, and their
complete tapes differ. Reproduce the Lean proof and its atlas binding with
`python scripts/tm_pair_proof.py run --out runs/tm-pair-fresh` in an environment
with the pinned Lean toolchain. Python/native agreement remains separate.

The [proof-reuse guide](docs/N5_PROOF_REUSE.md) shows two justified transformations:
reverse the object labels while keeping rule names, or
[rotate the labels and swap rule names](docs/N5_RENAMING.md). Both transport the
complete classification, inclusion order, and distinctness. Open the N5 lesson's
proof-reuse panel to follow a valid mapping and three deliberate mistakes.
Each construction has its own exact proof and downloadable query record:

```sh
python scripts/query_context.py explain context:family-206:saved-n5:renaming:v1
python scripts/query_context.py explain context:family-206:saved-n5:reverse-labels:v1
```

The [five-object walkthrough](docs/FIVE_OBJECT_MINIMUM.md) asks a different
question: can the same grouping diagram require different numbers of rules?
Its two exact families have the same eight-element inclusion order, while A
requires three unary rules and B requires two. The page explains the compact
lower-bound argument and links the separate formal and computational checks.

```sh
python scripts/five_object_proof.py run --out runs/five-object-fresh
python scripts/query_context.py explain context:family-206:five-object:operation-minima:v1
```

The [Snaky walkthrough](docs/SNAKY_FINITE_BOARD.md) formalizes the paper's
21-Maker-claim guarantee on its exact 251-cell envelope and containing 17 by 17
square. The Lean proof, kernel replay, axiom audit and seven changed-claim
rejections pass, alongside an independent certificate audit. Follow
[one complete example play](docs/SNAKY_PLAY.md) to see each move, a surviving
continuation, the remaining bound and its evidence. The example's eight-claim
win is distinct from the theorem's guarantee against every legal reply.

Read the [query contract](docs/ATLAS_QUERY.md),
[agent retrieval evaluation](docs/ATLAS_QUERY_EVALUATION.md), and
[infrastructure direction](docs/INFRASTRUCTURE.md). These interfaces are an
early foundation for reliable evidence retrieval across these selected mathematical examples.

## Propose a grouping, get a checked counterexample

The new [four-object grouping checker](docs/GROUPING_CHECKER.md) adds an active
tool interface. Lean proves its decoding round trips, acceptance equivalence,
and the correctness of every returned violating pair. A separate runner compares
the compiled build with an independent reference over all **65,536** inputs.

```text
Rule: [0,2,2,3]
Proposal {0,1} | {2} | {3} → reject, pair (0,1)
Repair   {0,1,2} | {3}     → accept
```

The [recorded demo](evidence/grouping-checker-v1/demo.json) links each outcome to
its exact input, source proof, and bounded executable evidence. Read the
[walkthrough and reproduction commands](docs/GROUPING_CHECKER.md). This pilot
checks one rule and grouping; a machine-code refinement proof remains future work.

The [constrained agent repair experiment](docs/REPAIR_BENCHMARK.md) connects a
real Codex model to this checker. It asks the agent to merge existing groups,
preserve a required separation, and recognize when a repair is impossible.
The local runner uses an existing Codex ChatGPT sign-in and saves each prompt,
answer, checked outcome, and evidence record for offline replay.
In the first paired pilot, both pass/fail and counterexample feedback produced
**12/12 correct first decisions**, including six impossible cases. This small
test demonstrated the working connection and scoring process; it did not show
an accuracy advantage for counterexample feedback.

## Quick start

Python 3.10 or later. Clone the repository, enter it, and check a saved example:

```sh
git clone https://github.com/Maverick0351a/finite-congruence-checks.git
cd finite-congruence-checks
python verify_witness.py evidence/N5-witness.json --output runs/N5-check.json
```

You can also download the [tagged release](https://github.com/Maverick0351a/finite-congruence-checks/releases/tag/v0.1.0), including the evidence and checksum.
The command checks all five witness conditions, including every nonempty set
of ordered seed pairs. A successful run returns exit status 0.

Run the complete experiment and compare its mathematical results:

```sh
python run_experiment.py --out runs/reproduction
python scripts/check_evidence.py --evidence runs/reproduction --compare evidence
```

Choose a new or empty output directory. The full run includes the unit tests,
complete search, seven certificate checks, independent exhaustive replay,
congruence recovery, and exact operation minimization. Runtime is usually on the
order of a minute on a desktop; it depends on hardware.

## What the experiment found

![Candidate attrition by lattice: all candidates compared with structural survivors and full witnesses](charts/candidate-attrition.png)

| Lattice | Lattice elements | Smallest carrier found | Full admissible unary pool | Minimum selected unary operations |
|:--|--:|--:|--:|--:|
| C2 · chain | 2 | 2 | 4 | 0 |
| C3 · chain | 3 | 3 | 15 | 1 |
| C4 · chain | 4 | 4 | 64 | 1 |
| B2 · Boolean square | 4 | 3 | 8 | 1 |
| M3 · three-atom diamond | 5 | 3 | 4 | 0 |
| N5 · pentagon | 5 | 4 | 12 | 2 |
| B3 · Boolean cube | 8 | 4 | 14 | 2 |
| M4 · four-atom diamond | 6 | None through 4 | — | — |

The seven positive carrier sizes attain the elementary lower bound from chain
height. Operation minima fix the saved carrier **and exact congruence relations**;
other embeddings and higher arities are outside that minimization. Empty
operation signatures are allowed: all equivalence relations on two or three
points already form C2 or M3. M4's result is negative only within the stated bound.

<details>
<summary><strong>View every lattice × carrier-size result</strong></summary>

![Exact labeled-witness and vertex-class counts for each tested carrier size, including zeros](charts/witness-counts.png)

</details>

<details>
<summary><strong>Compare full unary pools with minimum operation lists</strong></summary>

![Small operation lists for the saved representations](charts/operation-minima.png)

</details>

See the [verification method](METHOD.md) for definitions and the
[research context](RESEARCH_CONTEXT.md) for the relationship to prior work.

## Why multiple checks matter

The independent graph verifier reproduced **94,509,661 ordered seed subsets**
across every structural survivor. Its algorithms include loops and both edge
orientations directly; the search uses a documented reduction to unordered edges.
A third calculation enumerates all unary maps and set partitions to recover the
actual congruence lattices.

Of 1,459 structural survivors, **1,242 fail connectivity**. These are useful
regression cases for implementations that check only the first four conditions.

An additional independent audit compares the operation minimizer with a
breadth-first search through congruence families. It checks all **313**
representable exact families on carriers of sizes 1–4, plus 60 impossible-family
controls. [Review scope and evidence](docs/RELEASE_REVIEW.md).

Lean 4.34.1 proves that the **exact saved N5/B3 colorings satisfy the upstream
`IsGraphWitness` predicate**, including connectivity for every nonempty finite
set of ordered seed pairs. Tables are generated from the JSON certificates;
the proofs passed compilation, bundled kernel replay, and a strict axiom check.
Separately, the original upstream theorem passed its official comparator, with
two invalid controls correctly rejected. [Proofs, logs, scope, and one-command
reproduction](docs/LEAN_VERIFICATION.md).

These implementations and reviews were developed with AI assistance in the same
session. Independent algorithms strengthen the checks; external peer review and
mathematical novelty have not been established. See the precise distinction
between computational evidence, concrete Lean proofs, and upstream verification
in [the claim ledger](docs/CLAIMS.md).

## Explore an example

**[Open the original graph explorer](https://maverick03511-finite-congruence-checks.static.hf.space/index.html).**
Choose a lattice, inspect its relations and unary operations, compare passing
and failing examples, and download the exact certificates. The demo displays
precomputed evidence; its controls do not rerun the exhaustive search or check
Lean proofs. [Rebuild the demo and inspect its scope](docs/HUGGING_FACE_DEMO.md).

![N5 and B3 lattice and witness diagrams](charts/witness-examples.png)

```sh
# Recover every congruence of the algebra defined by a certificate.
python verify_algebra.py evidence/B3-witness.json --out runs/B3-algebra.json

# Minimize the unary operation list for this exact representation.
python minimize_operations.py evidence/B3-witness.json --out runs/B3-operations.json

# Search one target, exhaustively through four vertices.
python search.py --lattice N5 --max-vertices 4 --out runs/N5-search

# Independently audit every small representable congruence family.
python scripts/audit_operation_minima.py --out runs/operation-audit.json
```

Witness-verifier exit codes are **0** for a pass, **1** for a well-formed candidate
that fails, and **2** for malformed input or an explicit resource limit. The
search's certificate registry identifies the witnesses from that invocation;
leftover files in a reused search directory are not part of a new result.

## Rebuild the figures

```sh
python -m pip install -r requirements-charts.txt
python scripts/build_charts.py
python scripts/build_charts.py --check
```

Only chart generation needs third-party dependencies. Figures and the offline
gallery are generated from checked JSON inputs; `charts/chart-data.json` records
the plotted values and source hashes. The `--check` command needs only the standard
library. [Evidence and file formats](docs/EVIDENCE.md).

## Repository map

| Path | Purpose |
|:--|:--|
| [search.py](search.py) | Exhaustive bounded search and vertex-isomorphism classes |
| [verify_witness.py](verify_witness.py) | Independent literal graph-predicate checker and replay |
| [verify_algebra.py](verify_algebra.py) | Direct recovery of all unary-algebra congruences |
| [minimize_operations.py](minimize_operations.py) | Exact operation reduction for fixed relations |
| [evidence/](evidence/) | Certificates, complete results, stage logs, and integrity hashes |
| [lean/](lean/) | Concrete formal checks and pinned upstream source context |
| [charts/](charts/), [docs/index.html](docs/index.html) | Downloadable research figures and offline gallery |
| [space/](space/) | Interactive static explorer and downloadable certificates |
| [scripts/](scripts/) | Evidence integrity, independent minima audit, figure generation |
| [.github/workflows/](.github/workflows/) | Automated replication on Linux and Windows |

Read the [contribution guide](CONTRIBUTING.md), [research roadmap](docs/ROADMAP.md),
and [development record](WORK_LOG.md). To cite the software, use [CITATION.cff](CITATION.cff)
and identify both this project's version and the upstream corpus commit.

Apache-2.0. Upstream source notices are retained in [NOTICE](NOTICE) and `reference/`.

Maintained by **Travis Johnson** · [LinkedIn](https://www.linkedin.com/in/travis-johnson-606207379) · [GitHub](https://github.com/Maverick0351a).
