# Finite Congruence Checks

![Finite Congruence Checks — project identity banner: small algebras, explicit witnesses and reproducible evidence](charts/project-banner.svg)

[![Reproduce and verify](https://github.com/Maverick0351a/finite-congruence-checks/actions/workflows/verify.yml/badge.svg)](https://github.com/Maverick0351a/finite-congruence-checks/actions/workflows/verify.yml)
[![Recorded Lean 4.34.1 checks passed: concrete N5/B3 and targeted upstream modules](charts/lean-checks-badge.svg)](docs/LEAN_VERIFICATION.md)
[![Release v0.1.0](charts/release-badge.svg)](https://github.com/Maverick0351a/finite-congruence-checks/releases/tag/v0.1.0)
[![License: Apache 2.0](https://img.shields.io/badge/license-Apache%202.0-315B78)](LICENSE)
[![Python: 3.10+](https://img.shields.io/badge/python-3.10%2B-315B78)](#quick-start)

A focused research toolkit for finite congruence lattices. Search colored graphs,
verify every quantified condition with an independent implementation, recover
the corresponding unary algebras, and find their smallest operation lists on a
fixed representation. The core experiment uses only Python's standard library.

In plain language, we build small systems whose rules permit exactly a chosen
pattern of consistent groupings. Start with a three-object example in the
**[illustrated introduction](docs/PLAIN_LANGUAGE_GUIDE.md)** to see what that means.

The starting specification is the graph-witness criterion in
[OpenAI's math corpus, family 206](reference/README.md), pinned to an exact commit.
This is an independent companion project. The original graph experiment covers
eight specified lattices on carriers of size **one through four**. The atlas
classifies all representable grouping families through four objects, yielding
22 abstract lattice shapes.

**[Interactive demo](https://huggingface.co/spaces/Maverick03511/finite-congruence-checks)** ·
**[Understand the math](docs/PLAIN_LANGUAGE_GUIDE.md)** ·
**[Readable atlas](https://maverick03511-finite-congruence-checks.static.hf.space/atlas.html)** ·
**[Quick start](#quick-start)** · **[Evidence gallery](docs/index.html)** ·
**[Exact claims](docs/CLAIMS.md)** · **[Lean status](docs/LEAN_VERIFICATION.md)** ·
**[Agent repair experiment](docs/REPAIR_BENCHMARK.md)** ·
**[Changelog](CHANGELOG.md)** · **[Support](SUPPORT.md)**

| Candidate colorings | Full witnesses | Vertex classes | Saved examples |
|:--|:--|:--|:--|
| **143,685** | **217** | **22** | **7** minimum-carrier constructions |

The HTML gallery is self-contained and works offline. Download the repository
and open `docs/index.html` in a browser; GitHub displays HTML source in its file
viewer. Each figure is also available as PNG and editable SVG in `charts/`.

## Understand the math visually

Start with **[the readable atlas](https://maverick03511-finite-congruence-checks.static.hf.space/atlas.html)**:
three objects, one rule, and five possible groupings. Try a grouping, see why
it works or fails, then explore the complete catalog through four objects.
Every diagram explains what its nodes and lines mean; technical data is expandable.

The catalog contains **39 grouping-family representatives** after renaming
objects, covering **22 abstract lattice shapes**. Compare two four-object
constructions with the same chain shape but different minimum rule counts.
Use the **[Cytoscape map](https://maverick03511-finite-congruence-checks.static.hf.space/atlas.html#shape-map)**
to follow construction-to-shape connections, compare rule counts, and open each
entry's evidence. [How to read the map](docs/ATLAS_MAP.md).
These counts describe congruence families and are separate from the original
colored-graph search totals above. [Scope and independent checks](docs/ATLAS.md).

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

Read the [query contract](docs/ATLAS_QUERY.md),
[agent retrieval evaluation](docs/ATLAS_QUERY_EVALUATION.md), and
[infrastructure direction](docs/INFRASTRUCTURE.md). These interfaces are an
early foundation for reliable evidence retrieval in a bounded mathematical domain.

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
