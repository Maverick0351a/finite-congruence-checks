# Guided tour

A longer walk through the project's tools and results. The [README](../README.md)
gives the short version; the [claim ledger](CLAIMS.md) states the exact scope of
every result below. Run the commands from the repository root.

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
entry's evidence. [How to read the map](ATLAS_MAP.md).
These counts describe congruence families and are separate from the original
colored-graph search totals above. [Scope and independent checks](ATLAS.md).

For one complete source-linked example, open `space/context-n5.html` or read
the [N5 walkthrough](N5_SOURCE_CONTEXT.md). Try all 15 groupings, see why
exactly five survive, and follow the source map from the original question to
the exact Lean classification and graph-witness bridge. The comparator target
with `sorry`, completed upstream proof, and local verification record have
separate links. The atlas's N5 entry uses different rule tables; the page shows
the checked renaming of its grouping family without transferring the proof.

Download the repo and open `space/atlas.html` for an offline copy. For a text
walkthrough or presentation script, use the [illustrated introduction](PLAIN_LANGUAGE_GUIDE.md).

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
[source-context interface](CONTEXT_QUERY.md):

```sh
python scripts/query_context.py explain context:family-206:saved-n5:classification:v1
python scripts/query_context.py compare
python scripts/query_context.py explain tm:tiny-stay:tape:v1
```

The Turing export includes a [proof for the exact pair](TM_PAIR_PROOF.md):
both machines first halt after one step, both heads stay at zero, and their
complete tapes differ. Reproduce the Lean proof and its atlas binding with
`python scripts/tm_pair_proof.py run --out runs/tm-pair-fresh` in an environment
with the pinned Lean toolchain. Python/native agreement remains separate.

The [proof-reuse guide](N5_PROOF_REUSE.md) shows two justified transformations:
reverse the object labels while keeping rule names, or
[rotate the labels and swap rule names](N5_RENAMING.md). Both transport the
complete classification, inclusion order, and distinctness. Open the N5 lesson's
proof-reuse panel to follow a valid mapping and three deliberate mistakes.
Each construction has its own exact proof and downloadable query record:

```sh
python scripts/query_context.py explain context:family-206:saved-n5:renaming:v1
python scripts/query_context.py explain context:family-206:saved-n5:reverse-labels:v1
```

The [five-object walkthrough](FIVE_OBJECT_MINIMUM.md) asks a different
question: can the same grouping diagram require different numbers of rules?
Its two exact families have the same eight-element inclusion order, while A
requires three unary rules and B requires two. The page explains the compact
lower-bound argument and links the separate formal and computational checks.

```sh
python scripts/five_object_proof.py run --out runs/five-object-fresh
python scripts/query_context.py explain context:family-206:five-object:operation-minima:v1
```

The [Snaky walkthrough](SNAKY_FINITE_BOARD.md) formalizes the paper's
21-Maker-claim guarantee on its exact 251-cell envelope and containing 17 by 17
square. The Lean proof, kernel replay, axiom audit and seven changed-claim
rejections pass, alongside an independent certificate audit. Follow
[one complete example play](SNAKY_PLAY.md) to see each move, a surviving
continuation, the remaining bound and its evidence. The example's eight-claim
win is distinct from the theorem's guarantee against every legal reply.

Read the [query contract](ATLAS_QUERY.md),
[agent retrieval evaluation](ATLAS_QUERY_EVALUATION.md), and
[infrastructure direction](INFRASTRUCTURE.md). These interfaces are an
early foundation for reliable evidence retrieval across these selected mathematical examples.

## Propose a grouping, get a checked counterexample

The new [four-object grouping checker](GROUPING_CHECKER.md) adds an active
tool interface. Lean proves its decoding round trips, acceptance equivalence,
and the correctness of every returned violating pair. A separate runner compares
the compiled build with an independent reference over all **65,536** inputs.

```text
Rule: [0,2,2,3]
Proposal {0,1} | {2} | {3} → reject, pair (0,1)
Repair   {0,1,2} | {3}     → accept
```

The [recorded demo](../evidence/grouping-checker-v1/demo.json) links each outcome to
its exact input, source proof, and bounded executable evidence. Read the
[walkthrough and reproduction commands](GROUPING_CHECKER.md). This pilot
checks one rule and grouping; a machine-code refinement proof remains future work.

The [constrained agent repair experiment](REPAIR_BENCHMARK.md) connects a
real Codex model to this checker. It asks the agent to merge existing groups,
preserve a required separation, and recognize when a repair is impossible.
The local runner uses an existing Codex ChatGPT sign-in and saves each prompt,
answer, checked outcome, and evidence record for offline replay.
In the first paired pilot, both pass/fail and counterexample feedback produced
**12/12 correct first decisions**, including six impossible cases. This small
test demonstrated the working connection and scoring process; it did not show
an accuracy advantage for counterexample feedback.

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
controls. [Review scope and evidence](RELEASE_REVIEW.md).

Lean 4.34.1 proves that the **exact saved N5/B3 colorings satisfy the upstream
`IsGraphWitness` predicate**, including connectivity for every nonempty finite
set of ordered seed pairs. Tables are generated from the JSON certificates;
the proofs passed compilation, bundled kernel replay, and a strict axiom check.
Separately, the original upstream theorem passed its official comparator, with
two invalid controls correctly rejected. [Proofs, logs, scope, and one-command
reproduction](LEAN_VERIFICATION.md).

These implementations and reviews were developed with AI assistance in the same
session. Independent algorithms strengthen the checks; external peer review and
mathematical novelty have not been established. See the precise distinction
between computational evidence, concrete Lean proofs, and upstream verification
in [the claim ledger](CLAIMS.md).

## Explore an example

**[Open the original graph explorer](https://maverick03511-finite-congruence-checks.static.hf.space/index.html).**
Choose a lattice, inspect its relations and unary operations, compare passing
and failing examples, and download the exact certificates. The demo displays
precomputed evidence; its controls do not rerun the exhaustive search or check
Lean proofs. [Rebuild the demo and inspect its scope](HUGGING_FACE_DEMO.md).

![N5 and B3 lattice and witness diagrams](../charts/witness-examples.png)

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
