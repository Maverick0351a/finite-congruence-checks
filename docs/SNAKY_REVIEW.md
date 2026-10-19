# Independent review of the finite-board Snaky proof

Review completed 19 October 2026. Verdict: **approve the reviewed implementation**.
This is an independent AI-assisted review within the implementation chat, not
external peer review. The completed proof, exact bindings, recorded verification,
illustrated execution, and presentation have been inspected. Protected-branch
CI and public-link availability remain separate release gates.

## Source and claim boundary

The review uses OpenAI's math corpus at commit
`1581d4cbdd69a0faf34b2089614fe2a814316a6a`.
Its [scope note](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/docs/187.md)
describes a formal 21-Maker-move strategy on the infinite integer lattice and
explicitly excludes the smaller finite-board restriction. The paper's
[strategy argument](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Snaky-in-21-Maker-moves-September-25-2026/build/strategy.tex)
already proves finite-board corollaries for the 251-cell final envelope and
the square `{0,...,16} × {0,...,16}`. This milestone aims to formalize that
existing argument; it does not improve the move bound or establish novelty.

The relevant certificate has 728 cards, indexed 0 through 727, including six
bases and 722 further numbered lines. The older uploaded 616-row comparator
certificate is a different object. Exact references and transformations are
part of the certificate's identity.

## Mathematical obligations

- Every claimed Maker or Breaker move lies in the chosen finite board and is
  previously unoccupied. Ownership remains disjoint.
- A prescribed pivot already owned by Maker requires a fresh replacement;
  that replacement consumes an actual Maker move.
- Before Maker move 21, at most 40 cells are occupied. This supports finite
  replacement availability; an infinite-board fresh-cell theorem alone does
  not establish it.
- A win may finish immediately after Maker's move. No Breaker reply after
  victory is required.
- A recursive move must not win vacuously because there are no legal Breaker
  replies. The reviewed design includes an explicit legal-reply existence
  obligation.
- Quantification over Breaker replies on the square includes replies outside
  the 251-cell envelope. Nested envelopes preserve the required avoidance of
  all earlier Breaker cells.
- A finite-board strategy cannot be globally fresh on arbitrary exhausted
  states. Availability assumptions belong in the exact game interface.
- Board containment and the root's height, requirements, and certificate
  identity must be bound to the theorem, not merely to a diagram or file hash.

## Checks completed

- Read the pinned paper's strategy and certificate-proof arguments, the
  upstream game constructors and composition proof, the exact root card, and
  the certificate summary.
- Confirmed that the paper distinguishes actual Maker moves, replacement
  moves, and the absence of a required final Breaker reply.
- Confirmed that upstream `WinsIn.move`, used without further conditions on a
  finite carrier, can have an empty universal-reply premise. The proposed
  finite semantics strengthens this with explicit reply availability and an
  immediate-win constructor.
- Independently reconstructed the literal certificate with a separate
  transient parser, without importing the implementation's checker. All
  728 required sets, envelopes, and heights agree with the pinned Lean card
  literals: 2,184 comparisons with no discrepancies. The root has empty
  requirements, a 251-cell envelope inside the stated square, and height 21.
  The parser traversed 898 inline combinations and 4,089 numbered references.
- Read the independent reconstruction implementation and its malformed-input
  controls. Re-ran all 24 focused Python tests and the saved computational
  receipt replay successfully. Checked the paper's signed-coordinate order
  separately from the upstream model's different symmetry numbering.
- Read the board-chart generator, checked generated-data freshness, and
  inspected its rendered output. Coordinate axes, root pivot, sample target,
  and replacement arithmetic are legible; the image explicitly identifies
  the sample target as an illustration rather than an execution trace.
- Checked all 94 vendored files against their raw-byte manifest. Ninety-two
  also agree byte-for-byte with the earlier pinned local source snapshot;
  the two remaining modules, `Policy.lean` and `Replies.lean`, agree with
  separate downloads from the same immutable upstream commit.
- Read the finite game, composition, transport, and concrete-board statements.
  The composition proof preserves board containment and disjoint ownership,
  charges a fresh replacement as an actual Maker claim, and carries the
  occupied-cell budget through each reply. The explicit reply witness rules
  out empty-response-set victories. The additional `false_impossible` and
  `zero_iff` statements address impossible targets and exhausted move budgets.
- Checked the generated finite proof source: 86 modules and 3,246 semantic
  derivations match the generator. This is a source-freshness check; successful
  Lean compilation and kernel replay remain separate obligations.
- Read the typed binding, receipt validator, query integration, CI changes,
  and draft walkthrough. Re-ran four input/audit validation tests successfully,
  including altered vendor/dependency pins and setup errors that must not be
  classified as mathematical rejection.
- Inspected the completed native development build: all 9,103 jobs passed,
  including the finite semantics, complete certificate adaptation, concrete
  boards, and literal claim binding. The proof source was then frozen at
  `f205fe504af726f57a3fc52e84c0b7fa962137f6` for the recorded verification run.
- Read the actual axiom log from that run. All 19 requested declarations have
  reports, using only `propext`, `Classical.choice`, and `Quot.sound`; no missing
  proof or extra axiom appears.
- Inspected the completed 12-stage receipt and all seven actual negative
  logs. The 179-module kernel command exited successfully in 1,631.946 seconds.
  Changed target, envelope, square, move bound, card number, initial ownership,
  and theorem substitutions failed on false propositions or incompatible
  mathematical types, not unavailable imports or resource exhaustion. The
  copied receipt replays against all 194 source hashes. All 15 proof/query
  tests passed independently, including altered logs, forged controls,
  missing stages, wrong kernel commands, and wrong execution settings.
- Reviewed the Hugging Face corpus banner's wording and source changes. Its
  reference to independent checks and formal extensions of selected corpus
  results is appropriately scoped. Visual browser checks were performed by
  the implementation agent; this review adds a wording check, not a second
  browser inspection.
- Read the illustrative-play adapter and its separate replay checker. The
  checker reconstructs certificate geometry using separate coordinate
  formulas, composes placements through basis-point images, and verifies
  fresh claims, child requirements and envelopes, actual move counts, and the
  complete winning target. It shares the pinned certificate grammar, not the
  move generator. All 23 play tests, saved replay, and generator freshness
  checks passed when rerun independently.
- Reconstructed the play's ownership history with a separate transient
  calculation importing none of the implementation modules. Enumeration of
  signed coordinate permutations confirms eight legal Maker claims, seven
  legal Breaker replies, no earlier win, and one complete six-cell target at
  move eight. These are checks of one chosen execution, not a better universal
  move bound. The replacement test is an isolated fixture, not a position
  asserted to occur in that illustrated play.
- Checked the initial play choices against the pinned paper's
  [worked continuation](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Snaky-in-21-Maker-moves-September-25-2026/build/certificate-proof.tex#L184).
  Its two displayed Breaker replies and first three Maker pivots match. The
  example then uses its explicitly declared deterministic reply choices.
- Re-ran five presentation-anchor controls using actual temporary Git
  commits, plus the explicit example-only renderer check. They check committed
  bytes, all eight rendered ownership states, surviving-envelope outlines,
  the final target, links, and navigation. The renderer check uses a DOM stub;
  browser layout and native keyboard behavior require separate inspection.
  Full publication tests intentionally require the actual proof receipt,
  source anchor, and generated packet instead of skipping missing inputs.
- Reviewed the stable viewer and presentation exporter sources. The export
  requires a supported exact claim and independently validated execution,
  checks their common board and claim ID, and binds published evidence links
  to committed bytes. The page separates the eight-claim illustration, the
  21-claim strategy guarantee, and the absence of a verified policy extraction.
  It displays actual claims and both remaining bounds separately, with a
  complete textual move list alongside the diagram.
- Reviewed the completed illustrated-play walkthrough against the saved
  execution: all eight Maker cells, seven Breaker replies, card bounds, and
  six final target cells match. The prose explains child survival, replacement
  accounting, and the distinction between an execution checker and a verified
  policy. Reviewed the final atlas navigation, CI publication gates, and
  corrections to stale N5/Turing claim summaries; no correctness issue was
  found in those changes.
- Re-ran the complete focused suite with the real receipt and presentation:
  all 73 tests passed (24 certificate, 23 play, 11 presentation, and 15
  proof/query tests). The presentation freshness command and the default full
  renderer check both pass. The source anchor binds 219 inputs to commit
  `767294d63b5cf0c3a4c664aa62c46d8dcbe3b65a`; the JSON download, browser script,
  exact query record, and immutable evidence links agree. These tests include
  actual temporary Git history and rejection of changed claims, proofs,
  execution states, and incomplete winning targets.
- Reviewed the completed-status documentation against the actual receipt.
  It correctly reports the local warmed-cache run and does not describe it as
  a fresh hosted build. The final mobile styling preserves board-label size
  through a keyboard-focusable horizontal scrolling region, while retaining
  the full move table as a textual alternative.
- Reviewed the mobile overflow correction (`min-width: 0` and a constrained
  grid column) and independently inspected the resulting 390-pixel screenshot.
  The board remains inside the page with readable controls and a visible focus
  outline. The implementation agent reports equal page scroll/client widths,
  a 321-pixel board viewport over 468-pixel content, native ArrowRight scrolling,
  Enter advancing to move two, and End selecting the eighth and final move
  with Next disabled. Those interaction checks are reported browser evidence,
  separate from this reviewer's screenshot and source inspection.
- Independently inspected the final desktop screenshot: all six winning cells,
  both additional Maker cells, the seven Breaker cells, and the separately
  labeled claim counts match the record. The implementation agent also reports
  native Space activation of Previous, expansion of all eight text-table rows
  using Enter, no page overflow with the table open, and an empty browser
  warning/error log. This reviewer did not independently repeat those browser
  actions.

No correctness finding remains open in the reviewed implementation. The finite game
constructors permit immediate victory; they do not require every strategy-tree
derivation to syntactically stop at its first winning position. A winning
position can use `done`, and a winning fresh move can use `finish`. Explanations
should preserve this distinction from an extracted executable policy.

## Approval scope and release gates

The approval covers the mathematical source, exact claim binding, completed
local verification receipt, finite replay checks, and reviewed presentation.
The proof source is fixed at `f205fe504af726f57a3fc52e84c0b7fa962137f6`;
the proof-and-play evidence links use
`767294d63b5cf0c3a4c664aa62c46d8dcbe3b65a`. The recorded proof run uses
Git-archived committed sources with an existing dependency/build cache. It
does not constitute a clean build or an attestation of every cached dependency.

Hosted CI must pass before merge. Public HTTP evidence links must be checked
after the referenced commit is pushed, and the published demo must be checked
after deployment. Their local source bytes and URLs have passed the anchor
checks; this review does not claim that those later release actions are complete.
Subsequent mathematical or evidence changes require renewed review. No model
benchmark, reserved task, API session, or training job was run for this review.

## Operational follow-up after hosted compilation timeout

The first hosted PR run (`39267847727`, job `118112018126`) reached the former
2,400-second compilation limit at 15:07:55 UTC on 19 October 2026. The downloaded
failed receipt records successful version and dependency stages; the build's
buffered output was not saved. This is a verification-infrastructure failure,
not a rejected mathematical claim or a completed hosted reproduction.

The operational code review is **approved**. Only compilation receives the
3,600-second allowance; every other stage retains 2,400 seconds. The hosted
job allowance is 120 minutes, with the mathematical and negative-binding
checks retained. Logs stream to files, and an atomic checkpoint records the
stage before execution and after completion or failure. The receipt excludes
itself and its temporary file from the artifact hashes. Replay requires each
stage to have passed, no failure classification, and the exact timeout policy.

Review found one cleanup gap in the first draft: a terminated direct child
could leave a live helper in its process group. The final code cleans that
owned POSIX group on every stage failure while preserving the direct child's
original exit code. A regression test exercises a parent terminated by SIGTERM
and its live descendant. POSIX group cleanup applies to Linux/WSL; native
Windows cleanup terminates the direct child only.

This reviewer independently ran all 11 synthetic runner tests on WSL/Linux;
all passed in 10.265 seconds. They exercise partial output, timeouts,
interruption, launch failure, owned-group cleanup, preservation of an unrelated
process, actual completed rejection, and rejection of incomplete or failed
stage records. In particular, a timeout after printing a type-error message
and a process terminated by a signal cannot become successful mathematical
rejection evidence. The fixtures run short Python processes and do not execute
Lean or establish the Snaky theorem.

The earlier mathematical approval remains limited to its recorded source and
receipt. The updated runner still requires its own completed 12-stage receipt
and publication anchor before renewed full approval. Those evidence checks
are **pending**; code approval is sufficient to freeze and run the candidate.

## Renewed receipt and publication review

**Approved** after inspection of the completed replacement receipt. This
supersedes the pending evidence gate immediately above. The renewed run used
source commit `5fa1b81550a1841a3b2b91a0c48a7cc5b4380448`, and the receipt is
committed at `f516abb4e98696cc61003de55518961245416a40`. This reviewer checked
all 194 recorded source hashes against the source commit's Git blobs and
confirmed that the Lean project, exact claim, and certificate are unchanged
from the original mathematical review.

All 12 recorded stages completed with status `passed`, no failure classification,
and the exact reviewed timeout policy. The kernel stage names 179 local modules
and records exit code 0 after 1,733.691 seconds. The 19 declaration reports
contain only the allowed standard axioms. All seven deliberate bad bindings
completed with exit code 1; their saved diagnostics identify false propositions
or the expected mathematical type mismatches. No timeout or interrupted process
is counted as a successful rejection. The 20 artifact hashes exclude the
receipt itself. The normalized receipt SHA-256 is
`f7548e47de85f73ff2b88ce6da23b007d531030cd979d1a285f0c7287b5ff581`.

This reviewer independently ran saved-receipt replay and all 84 focused tests
on WSL/Linux; all passed in 88.836 seconds with no skips. That total comprises
the earlier 73 certificate, play, presentation and proof/query tests plus 11
runner fixtures. Presentation freshness and the full renderer check also
passed. The renewed 219-input publication anchor identifies commit
`f516abb4e98696cc61003de55518961245416a40`; the generated JSON, JavaScript
wrapper, exact claim and evidence URLs agree. The updated walkthrough correctly
identifies the warmed-cache run and retains the original receipt in Git history.

This approval covers the revised runner, renewed local receipt and regenerated
presentation records. The reviewer did not start another Lean execution; saved
receipt validation remains distinct from the recorded kernel run. The local
build reused its existing cache, so it does not resolve the fresh hosted-build
gate. Hosted CI, HTTP checks for the newly pushed evidence commit, merge and
public deployment remain separate release gates. No model benchmark or training
was resumed.

## Hosted kernel-timeout recovery review

The subsequent hosted PR receipt (`39280967879`) records successful compilation
in 1,980.924 seconds followed by kernel timeout at 2,400.105 seconds. This
reviewer checked its diagnostic artifact hashes and independently audited its
19 axiom reports. The kernel failure is recorded as a timeout with exit -9
from cleanup; no negative controls ran. It is not an accepted proof receipt,
and the available evidence does not establish an out-of-memory failure.

The next operational candidate is **approved to freeze and execute**. Kernel
replay receives 7,200 seconds, compilation retains 3,600, and other stages
retain 2,400. The 210-minute CI job leaves time beyond the two long-stage caps
for setup, other proofs, controls and artifact upload. Host capacity and GNU
time measurements remain diagnostic sidecars outside the proof artifact set.

This reviewer independently inspected the pinned
[Lean checker source](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/LeanChecker.lean).
Its discovery loop scans the module search path for each selector. Nine exact
names or namespace prefixes preserve the same 179-module selection while
reducing those scans. The new runner checks selector coverage against the
local import closure, requests verbose output, and requires the exact complete
module inventory plus successful process exit in both execution and saved
replay. The announcement precedes waiting on a task; it alone does not certify
completion. The speed effect is still unmeasured at this review.

Review found and resolved a parsing gap: the first inventory parser ignored
unexpected module names containing apostrophes or Unicode. The final parser
collects every announced module suffix before exact comparison, so these extra
names and malformed suffixes fail validation. The reviewer independently ran
12 runner tests and six input tests on WSL/Linux; all 18 passed in 16.428
seconds. After that parsing correction, all six input tests passed again in
8.232 seconds, including the added naming controls. No Lean execution was
started by this review.

The theorem sources, exact claim, axiom policy and seven negative bindings
remain unchanged. The preceding receipt stays preserved in Git history, with
its original runner identity and command list. This updated runner requires a
new actual completed receipt, exact verbose inventory, and renewed publication
anchor before full evidence approval. Those gates and hosted reproduction are
pending. No benchmark or training was resumed.

## Final recovery receipt and publication review

**Approved** after independent inspection of the completed replacement receipt
and publication anchor. This closes the pending local evidence gates in the
preceding section. The run used frozen source commit
`c3af350005f413554aea03db8cbf2c4c2d09e31b`; its receipt is committed at
`3bd96caa445c459371128e882fe420479084924e`. This reviewer matched all 194 source
hashes to the frozen commit's Git blobs and confirmed that the Lean project,
exact claim, certificate, computational record, saved play, independent
checkers and query implementation remain unchanged from the prior approval.

All 12 recorded stages passed with no failure classification and the reviewed
timeout policy. The kernel stage completed with exit code 0 in 1,303.713 seconds;
its verbose log contains each of the required 179 modules exactly once and no
additional module. The 19 declaration reports use only the allowed standard
axioms. All seven negative bindings completed with exit code 1, with diagnostics
for the expected false propositions or mathematical type mismatches. The 20
artifact hashes exclude the receipt itself. Its normalized SHA-256 is
`9e2f9fafa6882ca21a89775671fe58bb21850faecf96f3c4916f8a7957e2079d`.
The measured kernel duration describes this warmed-cache run; it is not a
controlled measurement of the discovery optimization's speed benefit.

This reviewer independently ran saved-receipt replay and the complete focused
`test_snaky*.py` suite on WSL/Linux. All **88 tests passed in 105.372 seconds**,
with no skips. This includes the exact kernel-inventory controls, failed-stage
and process-cleanup fixtures, actual receipt replay, theorem/claim mutations,
and checks of the generated presentation against its 219-input Git anchor at
`3bd96caa445c459371128e882fe420479084924e`. The implementation agent separately
reported passing presentation-freshness and full-renderer checks. This review
started no new Lean execution and did not repeat the earlier browser review;
the mathematical and viewer sources are unchanged by this recovery.

No additional actionable finding remains for the local candidate. Successful
fresh hosted CI is still required before merge. HTTP checks of the new immutable
evidence links follow pushing the anchor commit, and the public demo requires
its deployment check. The locally warmed build and receipt inspection do not
establish completion of those release gates. Model benchmarks, reserved tasks
and training remain paused.

## Process-observation test race follow-up

**Approved** the narrow test-only correction following push run `39316093274`,
Python 3.10 job `118277828681`. The saved traceback shows `ProcessLookupError`
(errno 3) during the read of `/proc/<pid>/stat` in the child-cleanup assertion.
A process can disappear after the file is opened. The helper now accepts that
exception alongside `FileNotFoundError`; it continues to propagate permission
errors and reject a live process at its deadline.

This reviewer independently ran the two new deterministic WSL/Linux tests;
both passed in 0.002 seconds. They cover both disappearance exceptions,
unreadable process status, and a still-live sleeping process. The reviewed code
delta changes only `scripts/test_snaky_runner.py`. That file is absent from
both the receipt's 194-source hash set and the publication anchor's 219 inputs,
so the production runner, mathematical sources, receipt and evidence anchor
retain their prior identities. No proof execution was started for this review.
Hosted checks for the corrected candidate remain the release gate.
