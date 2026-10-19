---
title: Finite Congruence Checks
emoji: 🔬
colorFrom: blue
colorTo: green
sdk: static
app_file: index.html
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
---

# Finite Congruence Checks

An interactive companion to [the research repository](https://github.com/Maverick0351a/finite-congruence-checks).
Maintained by [Travis Johnson](https://www.linkedin.com/in/travis-johnson-606207379).
Explore independent validation of the **finite congruence graph criterion** from
OpenAI's math corpus, family 206.

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
filters graph edges and groups connected points for display.

Concrete N5/B3 proofs and targeted upstream Lean modules compiled and passed
bundled kernel replay. The full corpus and official comparator workflow were not
run. A formal correspondence between the Python connectivity implementation and
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
`--check` to confirm freshness. The downloadable `data.json` lists source hashes
and the pinned upstream revision. Publish only the contents of `space/`.

The app uses native HTML, CSS, JavaScript, and SVG. It has no runtime package,
external font, telemetry, server, model, or GPU dependency.
