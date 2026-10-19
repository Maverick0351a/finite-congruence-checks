---
title: Finite Congruence Checks
emoji: 🔬
colorFrom: blue
colorTo: purple
sdk: static
app_file: atlas.html
pinned: true
license: apache-2.0
short_description: Explore independent graph-criterion checks from OpenAI math
tags:
  - openai-math
  - openai
  - mathematics
  - formal-verification
  - lean4
  - graph-theory
  - lattice-theory
  - universal-algebra
  - reproducible-research
  - interactive-visualization
  - cytoscape
---

# Finite Congruence Checks

**Independent checks and formal extensions of selected results from
[OpenAI's math corpus](https://github.com/openai/math).**
Explore concrete examples, Lean proofs, and [evidence for each exact claim](https://github.com/Maverick0351a/finite-congruence-checks/blob/main/docs/CLAIMS.md).

An interactive companion to [the research repository](https://github.com/Maverick0351a/finite-congruence-checks).
Maintained by [Travis Johnson](https://www.linkedin.com/in/travis-johnson-606207379).
Explore independent validation of the **finite congruence graph criterion** from
OpenAI's math corpus, family 206.

Start with the readable atlas: a three-object lesson, 39 grouping-family
representatives through four objects, and 22 abstract lattice shapes. Explore
objects, rules, consistent groupings, and a comparison of two C4 constructions.
The Cytoscape map connects each construction to its abstract shape. Filter by
shape and object count, inspect claim IDs, then open the selected rules and
evidence. A midnight, teal, and violet palette follows light/dark preferences.
The catalog has its own complete classification and independent checker.
See [the atlas method](https://github.com/Maverick0351a/finite-congruence-checks/blob/main/docs/ATLAS.md).
The N5 story at `context-n5.html` explains the exact saved two-rule construction,
lets readers test all 15 partitions, and links the original question, comparator
target, completed proof, and concrete Lean bridge. Its source map labels each
relationship. The atlas's N5 entry has different operation tables; the story
shows the checked grouping correspondence without transferring formal evidence.
Its proof-reuse panel adds two explicitly proved label transformations, including
one that keeps the rule names. Follow corresponding objects and groups, inspect
the exact Lean theorem, and distinguish a failed grouping, a wrong rule mapping,
and an unsupported proof reference. The downloads are the same records returned
by the local query interface; browsing the page does not run Lean.
Technical entry details expose individual claim records with assumptions and
limits. A [local query tool](https://github.com/Maverick0351a/finite-congruence-checks/blob/main/docs/ATLAS_QUERY.md)
reads the same versioned records for research applications and agents.

The Turing comparison panel adds four exact machine pairs. Compare first
halting step, complete final tape, and head position independently, then inspect
the cited trace and applicable source lemma. These are bounded observations on
blank input. [Turing evidence guide](https://github.com/Maverick0351a/finite-congruence-checks/blob/main/docs/TM_ATLAS.md).

The Snaky walkthrough at `snaky-play.html` follows one checked execution on the
exact 251-cell board. It shows fresh Maker claims, legal Breaker replies,
surviving continuation envelopes, and the complete six-cell winning witness.
Its eight-claim example is separate from the formal guarantee within 21 claims
against every legal reply. It links the finite-board theorem, saved verification
receipt, and independently replayed play record. The paper already states the
finite-board result; this is a checked formalization and explanation of it.

The original graph explorer remains available at `index.html`.
Choose one of eight lattices, inspect colored graphs and equivalence classes,
compare passing and failing examples, and download the exact certificates.
The recorded bounded experiment examined **143,685 candidate colorings** on
carriers of **one through four points**, finding **217 full witnesses** in
**22 classes under vertex relabeling**.

## Evidence and scope

- [Source code and reproduction commands](https://github.com/Maverick0351a/finite-congruence-checks#quick-start)
- [Exact claims](https://github.com/Maverick0351a/finite-congruence-checks/blob/main/docs/CLAIMS.md)
- [Lean verification record](https://github.com/Maverick0351a/finite-congruence-checks/blob/main/docs/LEAN_VERIFICATION.md)
- [Research release v0.1.0](https://github.com/Maverick0351a/finite-congruence-checks/releases/tag/v0.1.0)

This static interface displays precomputed evidence. Changing controls does not
rerun the exhaustive search or check Lean proofs. Its small browser computation
checks whether rules preserve a selected grouping. The original graph explorer
also filters edges and groups connected points for display.

Concrete N5/B3 proofs and targeted upstream Lean modules compiled and passed
bundled kernel replay. The original upstream theorem passed its official
comparator, including two rejection controls. The full corpus was not verified.
A formal correspondence between the Python connectivity implementation and
the upstream Lean predicate remains unproved.

M4 has no witness on at most four points in this search; larger carriers are
outside its scope. Minimum operation counts fix the saved carrier and exact
congruence relations. Failing examples are derived demonstrations replayed by
the independent checker, not newly added search results.

This project is independent and does not imply OpenAI affiliation, endorsement,
external peer review, or mathematical novelty.

## Maintaining the demo

The canonical sources live in `space/` in the GitHub research repository.
Run `python scripts/build_space_data.py` there to regenerate the data, or add
`--check` to confirm freshness. For the atlas, also run
`python scripts/build_atlas_data.py --check`,
`python scripts/check_atlas.py --check-receipt evidence/atlas-review.json`, and
`python scripts/query_atlas.py build-claims --check`, followed by
`node scripts/check_atlas_ui.cjs` and `node scripts/check_atlas_map.cjs`.
For the saved N5 context, run `python scripts/build_n5_context.py --check`,
`python -m unittest discover -s scripts -p 'test_n5_context.py' -v`, and
`node scripts/check_n5_context.cjs`. The builder checks fixed source hashes
against its pinned revision before regenerating the sidecar record.
The downloadable `data.json` lists source hashes
and the pinned upstream revision. Publish only the contents of `space/`.
For Snaky, run `python scripts/build_snaky_play.py --check`,
`python scripts/check_snaky_play.py`,
`python scripts/build_snaky_presentation.py --check`, and
`node scripts/check_snaky_play_ui.cjs`. The presentation exporter replays the
saved formal receipt and checks its linked inputs against an immutable Git
revision. These commands do not start a new Lean proof execution.

The app uses native HTML, CSS, JavaScript, SVG, and a local pinned Cytoscape.js
build with its MIT license. It needs no package install, CDN, external font,
telemetry, server, model, or GPU service.
