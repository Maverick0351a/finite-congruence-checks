# Independent review of the finite-board Snaky proof

Review started 19 October 2026. Status: **in progress**. This is an independent
AI-assisted review within the implementation chat, not external peer review.
No approval is implied before the completed proof, bindings, and recorded
verification have been inspected. Protected-branch CI is a separate merge gate.

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
  proof or extra axiom appears. The complete kernel/negative-control receipt
  remains a separate pending gate.
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

No correctness finding is open in the source reviewed so far. The finite game
constructors permit immediate victory; they do not require every strategy-tree
derivation to syntactically stop at its first winning position. A winning
position can use `done`, and a winning fresh move can use `finish`. Explanations
should preserve this distinction from an extracted executable policy.

## Pending review

Kernel replay, actual negative-control logs, saved receipt validation, full
query tests, and the final user-facing explanation remain to be assessed as
they become available. The recorded run uses Git-archived committed sources
with an existing dependency/build cache; it must not be described as a clean
build. Source changes made after the checks above will receive a final review.
