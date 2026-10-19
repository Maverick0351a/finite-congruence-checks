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

On 18 October 2026 (Pacific time), the user explicitly authorized public release.
Changed repository visibility to public and verified GitHub reports PUBLIC.
Removed the obsolete private-access note and updated the sharing roadmap.
The v0.1.0 tag, archive, checksum, and mathematical evidence remain unchanged.

## Interactive explorer and maintainer links — 18 October 2026

Built a static Hugging Face companion under `space/`, with eight selectable
lattices, seven passing examples, four replayed connectivity obstructions,
relation controls, operation tables, result totals, source provenance, and
downloadable certificates. The deterministic exporter binds 23 source inputs
to commit 355f6d3f0eba56969f3d2a2de2467706a5493db7 and replays the displayed
examples without modifying the original evidence. Added exporter freshness and
browser relation checks to the Linux/Windows CI matrix.

A separate AI-assisted review checked 51 threshold views, 708 point-pair
comparisons, four failure graphs, and UI state transitions. Addressed four
presentation findings: order is described by upward paths, absent generated
edges are omitted from obstruction diagrams, edge labels use dark text, and
diagrams stack on narrow screens. Local checks passed for all exported data,
31 recorded positive relations, four obstructions, and 11 certificate hashes.

Investigated the reported GitHub failure. The only failed workflow was historical
run 39180794258, caused by the Linux metadata mock interaction already fixed in
dd86efa. Current main at 355f6d3 passed all four jobs in run 39182517480.

Added the user-supplied LinkedIn URL for Travis Johnson to the root README,
Space README, and demo footer. Created the public static Space
Maverick03511/finite-congruence-checks. Its publication is documented in
docs/HUGGING_FACE_DEMO.md. The original v0.1.0 archive and tag are unchanged.

## Concrete upstream witness bridge — 19 October 2026 UTC

Started branch `codex/lean-witness-bridge` for the next formal verification
milestone. The selected scope is the exact saved N5/B3 constructions and the
pinned upstream graph criterion. A separate agent is implementing the Lean
connection; another is checking the official comparator procedure in an isolated
environment. Proof compilation and comparator success are pending at this entry.

Extracted the existing Lean data into `CertificateData.lean`, generated from the
two saved JSON witnesses and recorded operation selections. The existing core
proof bodies are unchanged. The exporter also supplies join and meet tables for
the upstream lattice instances; meets are derived from the JSON order. The
independent table reader checks all four matrices, the bottom elements, and both
unary operations. Six exporter checks passed, including rejection of changed
certificate hashes, failed operation evidence, invalid joins, invalid operations,
and duplicate operation records. Exporting data does not itself establish a
formal theorem or prove the Python implementation correct.

Completed the concrete bridge through the upstream two-operation algebra and
its full congruence order. Kernel-checked lattice instances use the generated
join/meet/order tables. Principal-color equality identifies the exact saved
coloring, so the existing upstream theorem yields `IsGraphWitness` for each
saved graph, including all nonempty finite ordered seed sets. This uses the
general upstream theorem and does not independently reprove it or formally
verify the Python algorithms.

A separate AI reviewer found no mathematical bridge defect. The review caught
two automation gaps: compilation success alone did not reject unexpected proof
axioms, and the source manifest omitted the imported root Python validator.
Added a strict 21-declaration axiom allowlist and the missing source hash, plus
checks of the actual Lean version and clean, pinned dependency checkouts.

A fresh native Linux reproduction passed all 11 stages with `--skip-cache`:
fresh builds of our modules, bundled kernel replay, 13 targeted Python tests,
fresh axiom reports, and actual environment verification. The prepared Mathlib
dependency cache was reused. Only `propext`, `Classical.choice`, and `Quot.sound`
were reported. Source hashes matched before/after and against the working
repository. The complete record is in `lean/evidence/bridge-run/`.

Separately ran the official comparator on the unchanged pinned upstream
`graph_criterion` using real Landrun, an unprivileged Linux account, and the
recommended systemd address-family restriction. The original solution passed;
a placeholder solution failed for `sorryAx`, and an altered challenge failed
for statement mismatch. Retained the original challenge/configuration, pinned
runner, tool/dependency hashes, and all three logs under `lean/comparator/`.
Nanoda is disabled by the original configuration; no external kernel is claimed.

Added the same formal runner to hosted CI and updated the claim ledger and
roadmap. The 33 existing Python tests and all 13 new formal-runner/export tests
passed. A fresh complete bounded experiment reproduced all 143,685 candidates,
217 witnesses, and 22 classes, with matching mathematical results. All 25 formal
source hashes, 11 log hashes, comparator input/runner hashes, and changed-document
links were checked. Local verification is complete at this entry; hosted validation and
final review are the remaining publication checks. The original v0.1.0 release
tag, archive, and finite-search evidence are unchanged.

Final read-only AI review at `4961f29` found no actionable issues. It independently
matched the bridge's source/log hashes, 21 axiom reports, nine dependency pins,
and comparator inputs/results, and checked the final claim boundaries.
GitHub branch run [39187428882](https://github.com/Maverick0351a/finite-congruence-checks/actions/runs/39187428882)
and pull-request run [39187462100](https://github.com/Maverick0351a/finite-congruence-checks/actions/runs/39187462100)
each passed all five jobs, including the new 12-stage upstream bridge command.

Downloading and checking the hosted artifact found two local toolchain files
still used CRLF while Git stored LF. Their contents selected the same Lean
version, but byte hashes differed. Normalized the local copies to Git's existing
bytes and replaced the checked-in bridge receipt/logs with the successful hosted
artifact. All 25 source hashes now match Git's stored bytes, and all 12 hosted
log hashes match. Reran the official comparator and both controls against the
normalized toolchain input. Proof sources and pinned dependency revisions did
not change. The change and hosted checks are tracked in
[pull request #1](https://github.com/Maverick0351a/finite-congruence-checks/pull/1).

## Plain-language showcase guide — 18 October 2026, Pacific time

Added an illustrated introduction following the maintainer's request for more
mathematical explanation and simple diagrams. The walkthrough relabels the
saved B2 example as three objects A, B, and C; checks all five partitions; and
draws the four surviving congruences as a Boolean square. It distinguishes
operation arrows, lattice edges, and the colored graphs used in the search.
Added a short presentation script, evidence-scope explanations, README links,
and contributor guidance to keep future explanations concrete and accessible.

Validation passed: a separate AI reviewer independently enumerated the five
partitions, confirmed the one-operation minimum and relabeling, and found no
substantive math or scope issues in the completed guide. Incorporated two
clarifications about repeated output values and choosing a group member.
Checked all 48 local links across the changed documents. The complete Python
experiment passed, including unit tests and independent exhaustive replay;
the evidence checker confirmed agreement with the recorded mathematical
results. The run is saved locally in `runs/plain-language-guide/`.
These are documentation changes prepared locally on
`codex/plain-language-guide`; publication is not part of this entry.

## Readable representation atlas — 18 October 2026, Pacific time

Started the first atlas milestone after approval to proceed. The main reading
path teaches a three-object example before introducing a catalog of all
representable relation families on carriers of one through four points, grouped
under object relabeling and then abstract lattice isomorphism. Each entry will
show its actual partitions and a minimum operation list in matching labels.
The earlier five/six-point research pilot and conjectures remain separate.

Implementation is split between a deterministic exporter, an independent
complete classification check, and the accessible static interface. The
classification check must agree before the new counts are published. Planned
validation includes corruption controls, browser interaction and narrow-screen
review, existing experiment checks, hosted CI, and verification of the public
Hugging Face deployment. No new Lean coverage is claimed for atlas entries.

Completed the independent census: 313 labeled congruence families, 39 classes
under object renaming, and 22 abstract lattice shapes across carriers of sizes
one through four. The exporter and separate exhaustive checker agree on every
family, operation minimum, orbit, order relation, and cover. The saved receipt
is checked against fresh computation in CI, including deliberately corrupted
and incomplete input controls.

The static atlas now introduces objects, rules, groupings, and shapes through
an interactive three-object lesson. Each catalog entry shows its actual rules,
all valid groupings, a labeled order diagram, and a downloadable record. The
C4 comparison explains why two exact grouping families on four objects can
require different numbers of unary rules. Browser review covered desktop and
390-pixel layouts, keyboard selection, empty filters, technical disclosures,
wide diagrams, and a downloaded entry checked against the canonical data.

Following the maintainer's direction to treat this as early AI infrastructure,
added a versioned structural schema, stable relation-family IDs and shape keys,
a dependency-free local JSON query tool, and 106 individual claim records.
Every read command checks evidence freshness before advertising claim IDs.
The website and query tool use the same claim registry. A separate agent used
the real CLI to answer the same-shape/different-rule-count question and inspect
its citations. Four shapes have differing minima at a fixed carrier size;
six do when different sizes are allowed. The evaluation records this distinction
and its same-session, non-blinded limits in `docs/ATLAS_QUERY_EVALUATION.md`.
Architecture decisions and growth criteria are in `docs/INFRASTRUCTURE.md`.

Local validation passed: 23 atlas/query tests, deterministic atlas and claim
exports, fresh independent receipt comparison, and UI checks covering 518
grouping demonstrations, 304 explicit rejection witnesses, 1,428 rendered
nodes, 1,974 rendered edges, and 117 entry-to-claim links with exact source
pointers. The existing complete experiment reproduced its recorded results in
`runs/atlas-release/`; its 33 tests, 13 Lean/export tests, chart regeneration,
original explorer checks, and evidence integrity checks also passed. Hosted
CI and public deployment verification remain release steps at this entry.

Final documentation checks resolved all 86 local Markdown links and validated
the structural JSON Schema against the canonical dataset. Desktop browser
review confirmed the revised C4 diagrams and claim disclosures; the narrow
layout wraps the complete claim IDs without page overflow. Direct `file:`
navigation could not be tested in the controlled browser because its URL policy
allows HTTP and HTTPS only. Local HTTP interaction and the script-only tests
passed; the atlas assets themselves make no network requests.

Final independent AI review found no substantive correctness gaps or publication
blockers. It resolved citations for all 106 claims, checked every claim link for
39 entries and all 27 comparison groups, and reviewed the documentation and CI
integration. A test-harness import defect affecting direct invocation was fixed;
both the documented direct command (10 query tests) and discovery (23 combined
tests) pass. The hash-bound query implementation did not change during that fix.

## 2026-10-18 — Cytoscape map and atlas palette

The maintainer requested Cytoscape and an improved color scheme. Implemented a
construction-to-abstract-shape map backed by the existing atlas and claim
registry. The default C4/four-object view makes the one-rule versus two-rule
comparison explicit. Shape nodes use the existing versioned canonical keys;
construction nodes and links retain their individual claim IDs. The inspector
opens the matching catalog entry, including its rules and evidence. Graph
layout is presentation only; no mathematical data or proof scope changes.

Vendored Cytoscape.js 3.34.4 from the official npm package, checked archive
SHA-512 integrity, and retained its unmodified build, MIT license, and per-file
SHA-256 manifest. The map needs no CDN or package-install step. Added ordinary
selectors and buttons as a keyboard alternative to the canvas, graceful library
failure handling, and explicit empty-filter and cross-carrier scope messages.

Applied midnight blue, tidal teal, and violet across the atlas, including local
SVG diagrams and graph colors. Added dark preference support and forced-color
fallbacks. Modern web guidance informed non-color labels, control contrast,
and preservation of ordinary keyboard navigation. The contrast check exposed
a teal-on-tinted-surface pairing below 4.5:1; darkened it before proceeding.

Initial local checks pass for the actual vendored Cytoscape engine: 115 filter
combinations, 156 construction appearances linked to independent evidence,
22 shape components, the C4 comparison, seven rejection controls, library
hashes, and selected light/dark text pairings at or above 5.15:1. Browser
interaction checks and independent review follow before publication.

Completed browser checks at 1280 px, 390 px, and 344 px widths. Canvas selection
and shape taps, zoom/fit/reset buttons, keyboard selection, empty filters, and
entry focus transfer work. Narrow layouts have no document overflow. Dark-mode
review found two trailing CSS overrides on claim cards and focus outlines;
replaced them with theme tokens and checked the computed browser colors. A
deliberately blocked library request leaves the native selector and evidence
navigation usable, with the unavailable visual controls disabled. Restored the
library after the test.

Independent AI review confirmed the corrected styles, graph meanings, stable
identities, explicit minimum-rule scope, keyboard alternatives, and claim
freshness, with no remaining substantive findings. The 23 atlas/query unit tests,
existing atlas UI and explorer checks, recorded evidence check, map checks, and
`git diff --check` pass. Publication follows the repository CI checks.

The maintainer supplied a proposed progression from certificate checking to
executable testing and binary verification. Compared it with the existing Lean
definitions and concrete proofs, checked the Lean trust FAQ and primary seL4
and Alive2 sources, and recorded a scoped next milestone in
`docs/CHECKER_FOUNDATION.md`. The plan distinguishes preservation of one grouping
from exact-family verification and search completeness. Its proposed 16-bit
pilot is not an implemented checker or a completed binary-verification result.
Independent review of this plan confirmed its encoding and assurance boundaries;
clarified that existing N5/B3 graph proofs do not transfer to atlas entries merely
because they share a shape name.

Publication completed after all final CI checks passed on
`cf8b2eaadc62e8bc0d33008d98683f22bebbb51a` (PR run `39195004759`). PR #3 merged as
`dc16e2693a7db63e325c1e65ea965e249c827a7c`. The public Hugging Face atlas was updated
to Space commit `072bd00372de01c7c1a67c0d71ff48e1049ac91a`; all 31 uploaded files
were downloaded and byte-verified. The live Cytoscape map was inspected in the
browser after publication.

## 2026-10-18 — Specify the first checker input contract

After the Cytoscape update passed all CI jobs and was published, the maintainer
requested a tighter pre-implementation contract. Adopted four two-bit operation
outputs plus four two-bit group labels, replacing the draft relation-pair format.
All 65,536 in-range words are now valid payloads; repeated encodings of a
partition remain separate test inputs. Specified decoding, invalid boundary
handling, the exact acceptance equivalence, and a machine-readable contract
with planned result fields and two explicitly unverified example records.
No executable checker, source proof, or binary correctness claim is introduced.

Specification sanity checks confirmed that bits 0–15 occur exactly once, the
domain count is 256 × 256, the 256 label arrays represent 15 distinct partitions,
and both example words decode to the documented fields and expected behavior.
This checked the proposed format and fixtures, not a compiled checker.
Independent AI review independently confirmed the example arithmetic and found
one missing machine-readable requirement: specification artifact hash validation.
Added mandatory exact-byte SHA-256 matching for future evidenced results, along
with separate preservation and comparison outcomes and an explicit requirement
to cover every distinct word before claiming complete bounded agreement.
Final targeted review found no remaining substantive issue. The result schema,
Lean checker theorem, and binary comparison remain future implementation work.

## 2026-10-18 — Implement the generic grouping checker

Implemented the frozen four-object input contract in a separate Lean module.
Proved exact bit-field decoding, both encode/decode round trips, integer-range
rejection and value preservation, label equivalence, acceptance iff preservation,
and soundness/existence of a returned violating pair. Local compilation and
bundled kernel replay succeeded; all 11 axiom reports use only the allowed
standard axioms. Independent AI source review found no substantive gaps and
confirmed that parsing, native compilation, and repair remain separate boundaries.

An independent reference was written from the contract before its author read
the Lean implementation. It checks block image sets and has exhaustive tests
against the literal pair condition, plus repair checks for all 65,536 inputs.
Added a native JSON Lines wrapper, an exhaustive comparison runner retaining
binary/transcript hashes and compiler traces, an isolated compiled output fault
control, a versioned result schema, and a local evidence admission tool.

The demonstration uses rule [0,2,2,3]. It rejects grouping [0,0,1,2] with pair
(0,1), then checks repair [0,0,0,2], keeping object 3 separate. The repair policy
is deterministic and unproved; acceptance requires another native invocation.
The saved replay is an agent-usable protocol demonstration, not an LLM benchmark.
Full run results and publication details are recorded below after execution.

The first native pilot had zero mathematical disagreements but remained failed
because WSL could not locate Git for source provenance. Added and tested a
Windows Git fallback with explicit path conversion. The final run from committed
source `5f3a65f3b9ad29c13a822e3a781476fcc5867be0` passed with complete coverage,
zero disagreements, 28,672 preserved cases, and 36,864 rejected cases. The isolated
compiled output mutation produced exactly 65,536 detected Boolean mismatches.

Evidence admission review identified two consistency improvements: compare all
recorded binary digests and verify archive bytes when present, and fail when an
explicitly configured receipt is missing. Also tied source revision/clean-tree
flags back to retained Git logs. Applied the corrections and regression controls;
the reviewer reported no remaining blocking issues. All 31 grouping tests passed
on Linux and Windows, with no skipped receipt tests. Existing evidence integrity,
Lean table correspondence/export, and all 13 bridge controls also passed.

Saved the final receipt, full compressed native transcript, compiler traces,
logs, mutation evidence, and actual two-call repair demonstration under
`evidence/grouping-checker-v1/`. Exact-byte Git attributes preserve log hashes.
Executable archives remain separate release assets, and offline validation
explicitly reports whether those bytes were available.

## 2026-10-18 — Constrained repair benchmark and local Codex connection

The user refined the next experiment to allow merges only, require a designated
pair to stay separated, and include impossible tasks. This excludes both the
universal-grouping and singleton-grouping shortcuts. The independent oracle
enumerates all 15 partitions instead of trusting a model's impossibility claim.
Development and test tasks use disjoint operation conjugacy families, and the
main test set uses three-block inputs in both classes to avoid a block-count
shortcut. On four objects, every solvable rejected input under these constraints
has just one valid repaired partition; this makes ceiling effects likely.

The user prefers existing Codex access to separately funded API calls. Verified
local `codex login status` reports ChatGPT authentication and a real ephemeral
`codex exec` call succeeded. The runner uses this supported local interface,
without copying credentials. Model calls consume the user's Codex allowance and
are excluded from repository CI. The chosen model and effort match the user's
local configured values (gpt-6-astra, ultra).

Connection probes revealed that global AGENTS.md instructions still enter the
CLI context despite ignoring user configuration and disabling project docs.
Record their hash and size, retain requested settings, reject any tool activity
in the event log, and describe this as a controlled local harness pilot rather
than a completely isolated model evaluation. Fresh conversations receive only
one trial's public task and feedback from this experiment. Test prompts, model
answers, native claim records, process status, and usage will be retained; results
are pending execution and independent review.

The development pilot completed eight live calls: both arms answered all four
development cases correctly on their first decision. These development results
were used to check the harness, not counted as held-out results. Review found
the initial counterexample is inferable from every sampled task, because there
is exactly one distinct same-group pair. Added that limitation to the protocol.
Before freezing, added checks for unique conversation IDs, complete artifact
manifests, seeded trial order, binary identity, and a clean test source tree.
All 24 repair tests and all 31 existing grouping tests pass. Synthetic replay
controls reject altered grades, feedback, prompts, token reports, native inputs,
and reused threads even when artifact hashes are recomputed. Independent agent
review found no blocking defect; this is AI-assisted review, not external review.

Committed the frozen implementation and protocol as
`cda3ac79a481c5631c1480471e46f665c8bde288` before running the test split. The
24 live held-out trials completed with distinct conversation IDs, one decision
each, no retries, and no recorded tool activity. Both arms scored 12/12, split
6/6 on repairable tasks and 6/6 on impossible tasks. There were no constraint
violations or false impossibility claims. The observed paired accuracy
difference is zero; these results do not demonstrate a counterexample benefit.

Offline replay passed before copying the exact run bytes into
`evidence/repair-pilot-v1/`. Added CI replay without live model calls, a readable
results table, an actual repaired-group diagram, and precise claim-ledger rows.
The existing 65,536-input checker evidence remains bound to its original source
and binary. A larger task domain needs a matching specification and checker
assurance; no six-object verification is claimed by this milestone.

Final independent agent review replayed the saved run and separately enumerated
all 256 label assignments per task without importing the benchmark's mathematical
functions. It confirmed all 12 repair answers and all 12 impossibility answers
across both arms, distinct conversation IDs, matched prompts except for the
assigned witness, and the four source hashes against the frozen Git objects.
No blocking publication issue was found. This remains AI-assisted review.

The first GitHub scan flagged a deliberately fake oracle-leakage test marker
as a generic high-entropy secret. It was a literal dummy phrase, with no
authentication use. Renamed the fixture and replaced it with descriptive text;
the test still checks exclusion from the model prompt. Frozen benchmark sources
and recorded model evidence are unchanged by this test-only correction.

## 2026-10-18 — Archive review and next-domain scope

Resolved GitGuardian incident 38378566 as a false positive (Not a secret) for
the literal dummy test marker. Reran the check for PR #6 head ba467ab; all checks
passed and the PR merged as 4086d2b9788fc7c09058d1a6fac748e72e493104.
No history rewrite or scanner bypass was used.

Inspected the three supplied archives/CSV without executing their code and
recorded original hashes in docs/ARCHIVE_REVIEW.md. Independent agent review
confirmed the lexical limitations of formal-audit and the older Snaky checker's
610 table entries plus six base rows, distinct from the 728-card theorem.
The Turing-machine source is absent from those tarballs. Inspected its separate
pinned upstream definition and checked the cached file against the GitHub blob.
Earlier local Python benchmark logs exist; this new archive review did not
rerun them or prove port equivalence.

Added a proposed two-machine halt example with exact input, theorem, trace,
and retrieval obligations. Proposed a harder six-object repair protocol while
requiring matching checker assurance before claiming verified feedback. The
completed grouping checker, frozen benchmark sources, and saved results remain
the foundation. The original attachments and requested message are packaged
locally for handoff; executable uploads are not added to the public source tree.

Independent agent review found no blocking issue in the source semantics,
archive scope, or proposed six-object constraints. Local Markdown targets resolve,
git diff whitespace checks pass, and all four frozen benchmark blob hashes
still match cda3ac79a481c5631c1480471e46f665c8bde288. The handoff package is
checked against the three original upload hashes and a complete payload manifest.
This is documentation validation and AI-assisted review, not a new Lean proof.

## 2026-10-18 — Full TM bundle, repairs, and compiled comparison

Located the supplied complete bundle and preserved its original bytes and
SHA-256 (4ec4960fcac8c6901a68cfa66c4b3690d80831c1528f80793c05cafff578005d).
Independent reruns reproduced the original fuel-zero off-by-one, invalid domain
acceptance, and full-configuration differences in the benchmark encodings.
The earlier local repaired package already fixed fuel and basic domains; its
sources and historical receipts were preserved. The maintained scripts/tm_port.py
builds on those repairs with immutable snapshots of caller-owned containers.

Added a separate lean/tm project so the grouping foundation and frozen repair
experiment remain unchanged. It preserves the complete pinned upstream source
and Apache-2.0 license and verifies exact extraction of lines 10–66. Five generic
source step lemmas compile and pass leanchecker; elaborated axiom reports contain
only propext and Quot.sound. The executable observation adapter is outside those
proofs and observes complete finite tape support for finite initial words.

Review found and corrected executable/source binding, unintentional blank lines
in corruption controls, bool/int equality in replayed inputs, and crash exits
being counted as validation rejections. The runner now owns the build, derives
the binary path, retains its compressed bytes and hash, captures build/proof logs,
and checks input/output identities and unchanged sources. Independent tests
also reject stale receipts, altered artifacts, incomplete proof reports, and
unapproved axioms. Test fixtures are explicitly synthetic admission controls.

Recorded native run: 2,857/2,857 complete configurations agree; zero disagreements;
34 malformed inputs rejected with the expected adapter diagnostic; seven output
corruptions rejected. The 1,960 exhaustive snapshots cover only the explicitly
stated one-state/two-symbol domain. The other 897 snapshots are named or sampled.
All 45 TM unit tests pass. Saved native evidence replays on Windows. The prior
finite-experiment evidence check and constrained-repair replay still pass;
the original grouping and frozen benchmark files have no diff.

Updated the claim ledger, roadmap, and plain-language explanation with the
exact evidence boundary. Full configuration comparison validates the tested
translation cases; no general Python/Lean equivalence, binary refinement, or PDE
verification is inferred. Pair-specific theorem records and agent retrieval
remain the next steps. New CI repeats the native build and preserves its evidence.

## 2026-10-18 — Pair-specific TM atlas evidence

Started the requested small second-domain atlas integration from PR #8's
recorded native evidence. Four pairs on blank input receive independent claims
for first halting step, entire finite-support tape, and head position. The
existing claim fields and JSON-pointer/hash citations are reused. Derived JSON
traces retain the source JSONL line identities; first-halt evidence includes
the complete prefix. Qualified Lean lemma references explain source steps and
do not promote the observations to pair theorems or Python equivalence proofs.

Prepared six retrieval questions before running an evaluator: three property
comparisons, one source-lemma applicability question, a proposed universal
equivalence claim, and an absent BB5 pair. Structured checks and independent
prose review will be recorded separately. The grouping checker, original
TM native evidence, and frozen repair experiment are unchanged.

Completed four pairs and twelve claims from 272 exact saved configurations.
Each native locator and source-lemma link pins the existing source commit;
fixed source hashes prevent v1 IDs from silently acquiring changed inputs.
Review prompted complete-prefix citations for first halt, exact pair/side/step
lemma citations, and separate left/right lemma application anchors. The browser
shows explicit zero cells and head positions, opens exact trace rows, and clears
stale evidence fragments when a user changes the selected pair.

Fresh-context evaluator: six first answers pass structured checks, and a separate
agent review accepts all six explanations and lemma hypotheses. Ten CLI queries
are retained, including the expected unknown-BB5 rejection. Prompt, first answers,
transcript, score, review and source hashes are saved in evidence/tm-retrieval-v1.
No answer was revised after grading. This is one guided same-session exercise,
with no control arm, enforced file-access isolation, or general capability claim.

Validation: 50 atlas tests pass, including 27 TM data/retrieval tests; 33 root
tests pass. The full bounded experiment reproduces 143,685 candidates, 217
witnesses and 22 classes without differences. The 39-entry atlas rebuild and
independent review agree. Browser logic checks pass for 12 TM claims, 272 trace
rows and 120 citations, alongside the existing atlas and Cytoscape map checks.
Narrow-screen browser inspection confirms the BB4 tape difference at -10,
distinct heads, source/trace navigation and the pair-switch fragment repair.
