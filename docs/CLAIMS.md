# Claim ledger

Each claim below has a specific scope and an inspectable record. A green check
for one row does not establish a stronger claim from another row.

| Claim | Evidence | Scope |
|:--|:--|:--|
| Every selected coloring was enumerated | `evidence/search-results.json` | Eight named lattices; carrier sizes 1–4; 143,685 labeled candidates |
| A separate implementation agrees | `evidence/independent-review-results.json` | All 32 lattice/size rows, rejection counts, 217 witnesses and 22 vertex classes |
| Seven saved graphs satisfy the finite predicate | Seven `*.verification.json` files | Literal nonempty ordered seed sets, including loops; all total self-maps |
| Seven explicit algebras have the target congruence lattices | `evidence/verified-algebras.json` | All partitions and admissible unary maps on the saved finite carriers |
| Positive examples attain minimum carrier sizes | `METHOD.md`, search and algebra records | The attained size equals the elementary chain-height lower bound |
| Minimum unary operation counts are 0,1,1,1,0,2,2 | `evidence/minimized-algebras.json` | C2,C3,C4,B2,M3,N5,B3; fixed carriers and exact saved relation families |
| The minimizer agrees with a third exhaustive method | `evidence/operation-minima-audit.json` | All 313 representable exact relation families on carriers 1–4; 60 impossible controls |
| The atlas groups all small representable relation families | [Atlas method](ATLAS.md), `evidence/atlas.json`, `evidence/atlas-review.json` | Carriers 1–4; 313 labeled families, 39 classes under object relabeling, 22 abstract lattice types across the range; finite computational evidence |
| M4 has no graph witness in the searched range | Search and replay records | At most four carrier vertices; larger carriers are outside this claim |
| Saved N5/B3 graphs satisfy the exact upstream predicate in Lean | [Bridge proof and reproduction record](LEAN_VERIFICATION.md) | Exact generated color tables; all five `IsGraphWitness` conditions, including every nonempty finite ordered seed set |
| The pinned upstream theorem passes its official comparator | [Comparator logs and controls](../lean/comparator/README.md) | Original `graph_criterion` challenge/solution; placeholder proof and altered statement both rejected |
| A generic grouping checker implements preservation in Lean | [Checker proofs](../lean/GroupingChecker.lean), [reproduction](GROUPING_CHECKER.md) | All four-object unary operations and four group labels; exact decoding, both round trips, integer bounds, acceptance iff preservation, and returned-pair soundness |
| One compiled grouping checker agrees with an independent reference | [Exact build receipt](../evidence/grouping-checker-v1/summary.json) | All 65,536 encoded inputs for the identified build and environment; malformed-input probes separately; no machine-code refinement claim |
| A proposal can be rejected, repaired, and checked again with claim evidence | [Saved protocol demo](../evidence/grouping-checker-v1/demo.json) | Fixed example and deterministic repair policy; actual native checks; no LLM capability or repair-minimality claim |
| A live Codex repair pilot answered all selected test tasks correctly in both feedback arms | [Run receipt](../evidence/repair-pilot-v1/run.json), [method and result](REPAIR_BENCHMARK.md) | Twelve paired four-object tasks from six locally held-out operation families; six repairable and six impossible; 12/12 first decisions per arm, one repetition and one requested model setting; no demonstrated feedback advantage |
| The constrained impossibility oracle agrees with a different algorithm | [Oracle tests](../scripts/test_repair_tasks.py), [task census](../benchmarks/repair-v1/tasks.json) | Exhaustive 15-partition enumeration compared with independent forced-merge closure on all 8,832 eligible tasks; tested Python, separate from the Lean preservation proof |
| Five step properties hold for the extracted upstream Turing-machine definition | [Source lemmas](../lean/tm/MachineChecks.lean), [axiom reports](../evidence/tm-port-v1/build/axioms.log), [build and kernel receipt](../evidence/tm-port-v1/summary.json) | Halted configurations are fixed; a missing instruction changes only state; a present instruction has the defined write/move/target effect and preserves other cells; exact pinned fragment with narrower imports |
| The maintained Python TM port agrees with one compiled Lean oracle on complete configurations | [Native comparison receipt](../evidence/tm-port-v1/summary.json), [method and limits](TM_TRANSLATION_CHECKS.md) | 2,857 specified snapshots: 297 named, 1,960 exhaustive within a stated small domain, 600 sampled; full nonzero tape support, state, head and halting status; 34 decoder rejection probes and seven output-corruption controls; no general port-equivalence proof |
| The TM atlas compares three properties of four exact encoding pairs | [Pair claims](../evidence/tm-atlas-v1.json), [trace records](../evidence/tm-atlas-traces-v1.json), [method](TM_ATLAS.md) | Twelve separate stopping-time, complete-tape, and head-position observations on blank input; exact source/trace citations and qualified generic lemma links; no pair-equivalence theorem |
| One fresh-context agent selected the required evidence in six guided questions | [First answers and score](../evidence/tm-retrieval-v1/summary.json), [protocol and limits](TM_ATLAS_EVALUATION.md) | Six first responses pass structured pair/property/value/citation checks; prose receives separate same-session AI review; no control arm, feedback advantage, or general capability claim |

No claim of a new mathematical theorem or classification is made. These small
lattices are control examples. The negative M4 result is bounded. The project
does not verify all of OpenAI's math corpus, nor the undecidability or subgroup
interval conclusions explicitly outside family 206's selected formalization.

The upstream comparator challenge is a specification file ending in an
intentional `sorry`; the actual upstream solution lives in a separate module.
The comparator checks that original solution. The concrete N5/B3 bridge has
separate compilation, kernel replay, and axiom checks. Their individual records
and dependency trust boundaries are in [LEAN_VERIFICATION.md](LEAN_VERIFICATION.md).

AI-assisted review and multiple independent algorithms provide useful assurance.
They do not establish Python implementation correctness by formal proof or count
as outside peer review. Novelty would require a separate literature investigation.

The [archive review](ARCHIVE_REVIEW.md) preserves the original inspection scope.
The subsequent [TM checks](TM_TRANSLATION_CHECKS.md), [pair atlas](TM_ATLAS.md),
and [retrieval exercise](TM_ATLAS_EVALUATION.md) support only their scoped rows
above. Pair-specific Lean preservation proofs remain future work in the
[TM halt pilot](TM_HALT_PILOT.md). Lexical dependency counts cannot support proof-dependency claims;
those require elaborated declarations. Evidence does not transfer between
different constructions or certificates merely because they share a name.
