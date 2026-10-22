# Finite Congruence Checks

[![Reproduce and verify](https://github.com/Maverick0351a/finite-congruence-checks/actions/workflows/verify.yml/badge.svg)](https://github.com/Maverick0351a/finite-congruence-checks/actions/workflows/verify.yml)
[![Recorded Lean 4.34.1 checks passed: concrete N5/B3 and targeted upstream modules](charts/lean-checks-badge.svg)](docs/LEAN_VERIFICATION.md)
[![Release v0.1.0](charts/release-badge.svg)](https://github.com/Maverick0351a/finite-congruence-checks/releases/tag/v0.1.0)
[![License: Apache 2.0](https://img.shields.io/badge/license-Apache%202.0-315B78)](LICENSE)
[![Python: 3.10+](https://img.shields.io/badge/python-3.10%2B-315B78)](#quick-start)

**A testbed for small, exactly scoped mathematical claims that people and agents
can check and cite.** Each result here is a finite construction with its own
independent computational checks, a Lean proof where one exists, and a
machine-readable record tying it to its source. The value is the checking
pipeline; the mathematics is deliberately small.

> **Scope.** The lattice examples are known control cases, not open problems.
> Every lattice studied here already has a known finite representation: all
> lattices with at most seven elements were represented in earlier work
> ([context](RESEARCH_CONTEXT.md)), and B3 is distributive. No new theorem or
> classification is claimed. The exact scope of every result is in the
> [claim ledger](docs/CLAIMS.md).

The work starts from selected results in **[OpenAI Math](reference/README.md)**
— the graph-witness criterion in family 206 — and applies the same approach to
Turing-machine examples and Snaky on finite boards. This is independent work;
source attribution does not imply OpenAI affiliation or endorsement.

**[Research atlas](https://huggingface.co/spaces/Maverick03511/finite-congruence-checks)** ·
**[Claim ledger](docs/CLAIMS.md)** · **[Guided tour](docs/TOUR.md)** ·
**[Lean evidence](docs/LEAN_VERIFICATION.md)** · **[Roadmap](docs/ROADMAP.md)**

## Quick start

Python 3.10 or later, standard library only. Check a saved example:

```sh
git clone https://github.com/Maverick0351a/finite-congruence-checks.git
cd finite-congruence-checks
python verify_witness.py evidence/N5-witness.json --output runs/N5-check.json
```

The command checks all five witness conditions, including every nonempty set
of ordered seed pairs, and exits 0 on success. Reproduce the whole experiment
(about a minute on a desktop) and compare it with the recorded evidence:

```sh
python run_experiment.py --out runs/reproduction
python scripts/check_evidence.py --evidence runs/reproduction --compare evidence
```

Use a new or empty output directory. The run includes the unit tests, complete
search, seven certificate checks, an independent exhaustive replay, congruence
recovery, and exact operation minimization. The
[tagged release](https://github.com/Maverick0351a/finite-congruence-checks/releases/tag/v0.1.0)
includes the evidence and a checksum.

## Case studies

| Case study | What is checked |
|:--|:--|
| [Graph witnesses for small lattices](docs/ATLAS.md) | Exhaustive search over eight lattices on 1–4 points, an independent verifier, recovered congruence lattices, minimum operation lists, and Lean proofs for the saved N5/B3 constructions. |
| [Five-object operation minima](docs/FIVE_OBJECT_MINIMUM.md) | Two families with the same eight-element order need three and two unary rules respectively; formal and computational checks. |
| [Turing-machine examples](docs/TM_PAIR_PROOF.md) | Step lemmas for the extracted upstream machine definition, Python/Lean agreement on stated domains, and a proof for one exact machine pair. |
| [Snaky on finite boards](docs/SNAKY_FINITE_BOARD.md) | The paper's 21-claim Maker guarantee, formalized on its exact 251-cell envelope and the containing 17 × 17 square. |
| [Grouping checker and agent repair](docs/GROUPING_CHECKER.md) | A Lean-proved checker that returns counterexamples, and a small pilot connecting a live coding agent to it. |

The [guided tour](docs/TOUR.md) walks through each one with commands, and the
[query interfaces](docs/ATLAS_QUERY.md) let tools and agents retrieve the same
records with stable IDs and citations.

## What the lattice experiment found

The search covers eight specified lattices on carriers of size one through four
and checks every quantified condition independently.

| Candidate colorings | Full witnesses | Vertex classes | Saved examples |
|:--|:--|:--|:--|
| **143,685** | **217** | **22** | **7** minimum-carrier constructions |

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
height. Operation minima fix the saved carrier and exact congruence relations;
other embeddings and higher arities are outside that minimization.

**M4 is representable; it just needs more than four points.** M4 is a
six-element lattice with a known finite representation. The search shows only
that no graph witness for it fits on four or fewer points. This is a bound on
the search, not evidence against representability.

The figures are also available as PNG and editable SVG in `charts/`, and as a
self-contained offline gallery in `docs/index.html`. See the
[verification method](METHOD.md) for definitions.

## Evidence and its limits

Three separate Python implementations — the search, a literal verifier, and a
direct congruence recovery — agree on every result, and an independent audit
cross-checks the operation minimizer. Lean 4.34.1 proves that the saved N5 and
B3 constructions satisfy the exact upstream predicate, with kernel replay and an
axiom check, and the original upstream theorem passes its official comparator.
CI reruns the Python checks on Linux and Windows and the Lean proofs on Linux;
the comparator run is recorded separately in [lean/comparator](lean/comparator/README.md).

These checks were developed with AI assistance. Independent algorithms
strengthen them, but they are not outside peer review, and the Python code is
not formally verified. The [claim ledger](docs/CLAIMS.md) separates
computational evidence, concrete Lean proofs, and upstream verification row by
row; [INDEPENDENT_REVIEW.md](INDEPENDENT_REVIEW.md) records the review process.

## Rebuild the figures

```sh
python -m pip install -r requirements-charts.txt
python scripts/build_charts.py
python scripts/build_charts.py --check
```

Only chart generation needs third-party dependencies; `--check` uses the
standard library. [Evidence and file formats](docs/EVIDENCE.md).

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
| [scripts/](scripts/) | Evidence integrity, audits, query interfaces, figure generation |
| [.github/workflows/](.github/workflows/) | Automated replication on Linux and Windows |

Read the [contribution guide](CONTRIBUTING.md), [research roadmap](docs/ROADMAP.md),
and [development record](WORK_LOG.md). To cite the software, use [CITATION.cff](CITATION.cff)
and identify both this project's version and the upstream corpus commit.

Apache-2.0. Upstream source notices are retained in [NOTICE](NOTICE) and `reference/`.

Maintained by **Travis Johnson** · [LinkedIn](https://www.linkedin.com/in/travis-johnson-606207379) · [GitHub](https://github.com/Maverick0351a).
