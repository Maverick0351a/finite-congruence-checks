# Finite graph search work log

18 October 2026. Continuing the repaired math corpus audit.

The next experiment is a bounded search over colored graphs for six explicitly
specified finite lattices: chains C2, C3, C4, the four-element Boolean lattice
B2, the five-element diamond M3, and the pentagon N5. The initial carrier bound
is four vertices. We enumerate every labeled symmetric coloring with bottom
exactly on the diagonal; elementary conditions prune candidates before checking
the full connectivity condition.

The primary checker reduces seed sets to unordered nonloop edges. A separate
reviewer confirmed the reduction and is implementing an independent checker
that still enumerates every nonempty ordered seed subset, including loops.
Another subagent is checking primary research sources to contextualize results.

The earlier repaired ZIP and its evidence remain a baseline. New scripts,
certificates and results are saved in this separate directory. No proof of the
general corpus theorem or novelty claim is part of this experiment.

## Expansion and first results

The initial six-lattice search succeeded through four vertices. Added B3, the
eight-element Boolean cube, and M4, the six-element height-two lattice with
four atoms. Kept the same four-vertex bound. This adds a higher-rank Boolean
control and a target with a bounded negative outcome.

The complete search enumerated 143,685 colorings across 32 lattice/size rows.
It found 217 labeled witnesses in 22 classes under vertex permutations, with
seven minimum-size certificates. The elementary block-count lower bound
matches every positive carrier size. M4 has no witness through four vertices.

## Independent review and two verification routes

The review subagent wrote `verify_witness.py` without importing `search.py`.
It regenerated every candidate, checked all 1,459 structural survivors using
the original ordered seed sets including loops, and matched every count,
class multiplicity and minimum. That replay enumerated 94,509,661 seed subsets
across survivors; it also rechecked all 22 reported representatives. Its first
record is retained in the root `independent-review-results.json`; the final
reproducible run writes an updated record under `results/`.

The research subagent wrote `verify_algebra.py` independently of both graph
checkers. It enumerated all unary functions and partitions for each of the
seven certificates, recovered exactly the intended congruences and checked
the order isomorphism. This gives explicit algebras without relying on the
general graph-criterion theorem. It also documented primary research sources
and the limits of this computation in `RESEARCH_CONTEXT.md`.

Both routes identify why the fifth condition matters: 1,242 colorings pass
the first four conditions but fail connectivity. These include all 816 M4
structural survivors. Saved failing examples can act as regression fixtures.

## Reproducibility and compact examples

Added a hashed certificate registry so reusing a search output directory with
a smaller bound cannot make an old witness part of the current result.
The full runner requires a new or empty directory and uses that registry.
Added explicit carrier-size validation and eight primary regression tests;
together with nine independently written verifier tests, 17 tests passed.

The research subagent then minimized each saved algebra's unary operation
list via exact set cover, with a separate optimality check. Counts are C2=0,
C3=1, C4=1, B2=1, M3=0, N5=2, B3=2. The comparison fixes the carrier and exact
congruence relations. These are compact control artifacts and are not claimed
as new mathematical classifications. The empty signatures are intentional
and allowed by the source definition.

Prepared `run_experiment.py`, the method note, source reference files and README.
The earlier repaired audit ZIP has not been modified.

## Final validation and delivery

Final run finished at 2026-10-18 23:56:51 UTC with overall `passed=true` on
Python 3.12.10. All 17 unit tests, the full search, seven individual witness
checks, full independent replay, seven algebra recoveries and seven exact
operation minimizations passed. Every detailed count comparison matched.
The complete run took 28.15 seconds on this machine, including 25.47 seconds
for the replay; this is a single observation, not a benchmark.

The final independent code review reported no blocking findings. It also
injected a failed child stage and confirmed the runner saves `passed=false`
and returns a failure status, and confirmed nonempty output directories are
rejected without changing their contents. The final source guards reject
invalid lattice labels, carriers larger than four for operation optimization,
and output paths that would overwrite input certificates. The primary author
reviewed the minimizer's set-cover argument and both optimization implementations;
the independent review note states its narrower search/runner review scope.

Final integration evidence is in `results/run-evidence.json` and the associated
logs. The actual run was made in `work/finite-graph-final-run`; unchanged result
files are copied into this deliverable, so absolute paths in logs identify the
execution location. Relative filenames and hashes identify packaged inputs.

The package manifest records every delivered file except itself. Packaging
checks the final code and result hashes against the run evidence, verifies the
ZIP's CRCs and each archived manifest hash, and checks the earlier audit ZIP
against its unchanged SHA-256:
`6d16d201ee8cc8e58a1322d650a01c3a00b74a2a3ad9cd5bdb7d1d4732d05fc6`.
The new ZIP has a separate SHA-256 sidecar. Python cache files are excluded.


## Repository release preparation — 18 October 2026 (Pacific time)

Created a separate private-repository deliverable, finite-congruence-checks,
from the frozen finite-graph-search experiment. The older delivered folders and
ZIPs remain unchanged. Earlier entries above describe the original experiment
and its original results/ layout; this repository records its new run in evidence/.

Added explicit-input command lines, portable LF evidence files and normalized
run-log paths. Review found malformed label/name inputs and a missing-file path
that could leave stale success evidence; these now produce failure records.
Self-checks use explicit conditions so Python optimization cannot skip them.

The new reviewer independently enumerated all binary equivalence tables and
searched intersections of unary-map congruence families. The minimizer agreed
on all 313 representable families through four carrier points and rejected
60 impossible-family controls. The probe is retained as a runnable audit.

Added four data-derived charts in PNG/SVG, an offline evidence gallery, a claim
ledger, provenance and format documentation, contribution guidance, a research
roadmap, and a draft announcement. PNGs were visually inspected. Browser preview
of the gallery was unavailable; HTML structure and links were checked statically.

Lean work is recorded separately in docs/LEAN_VERIFICATION.md, including the
exact boundary between concrete examples and the upstream theorem.

Created the private GitHub repository and applied 13 relevant topics, including
openai-math, openai, math, congruence-lattices, universal-algebra, lean4, and
reproducible-research. Added a vector project banner, accessible README navigation,
citation metadata, changelog, support guidance, issue forms, pull request template,
and research-specific issue labels. All 32 README local links resolve; the banner
and scientific figures were visually inspected. Repository visibility remains private.

The concrete N5/B3 certificate project compiled with Lean 4.34.1 and passed its
bundled leanchecker replay locally. The first hosted CI run also passed the Lean
job and Windows Python job. Ubuntu exposed a test-fixture interaction: Linux's
platform metadata probe uses subprocess.run, which the failed-child regression
test was mocking globally. Isolated that metadata call in the test. Production
algorithms were unchanged. All six evidence tests then passed in local WSL, and
the complete 33-test experiment was rerun successfully with fresh recorded hashes.
Hosted run 39180991754 passed all four jobs at commit
dd86efafcb16a0b84fd6a44afedf2b33624f17cb: Ubuntu Python 3.10 and 3.12, Windows
Python 3.12, and concrete Lean compilation with bundled kernel replay.

The targeted upstream project then compiled the unchanged pinned Congruence and
GraphCriterion solution modules, and bundled leanchecker replay passed for those
modules and the audit module. Recorded matching source hashes, all nine pinned
dependency revisions with clean checkouts, and the printed axiom dependencies.
The full upstream corpus, official comparator workflow, and formal connection
from Python connectivity code to the upstream predicate remain outside this run.

Updated the GitHub description to identify validation of the finite congruence
graph criterion from OpenAI's math corpus, with exhaustive small-case experiments,
independent checkers, and Lean proof checks. This names the selected scope rather
than implying validation of the whole corpus. Added an optional future static
Hugging Face demonstration to the roadmap. A final separate subagent review found
no actionable problems in release packaging, manifest coverage, or checksums.

Tagged and released v0.1.0 at ee45ecd2e576a0b3e82a905927c3bf075320eda2 after
hosted run 39181960497 passed all four jobs. The uploaded 110-file ZIP has SHA-256
9b397975697a1efda9649fa0052963bcaefd70f275e3987e065e458c2342fe9d,
matching GitHub's asset digest. The repository remains private.

After the release, added two README badges: a recorded Lean verification badge
linked to its exact scope/logs, and a version badge linked to the tagged release.
These are local SVGs so they work for authorized viewers of a private repository.
The existing CI badge remains live. Badges provide navigation to evidence, not
external certification. This presentation update does not alter the frozen
v0.1.0 archive or tag.
