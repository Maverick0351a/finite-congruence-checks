# Upstream Snaky formalization

`OAI/GameTheory/SnakyTwentyOne/` is an exact byte copy from
[openai/math commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a](https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GameTheory/SnakyTwentyOne).
The corresponding upstream Apache-2.0 license is retained as `UPSTREAM_LICENSE`.
The file list and SHA-256 hashes are in `vendor-manifest.json`.

`FiniteCards/` contains mechanically adapted semantic derivations from those
upstream proof scripts. They replace the infinite-board template semantics with
this project's finite-board strategy semantics. The original upstream files are
unchanged. The generator is not trusted evidence; Lean checks its output.

`SnakySemantics.lean` adapts the upstream composition and transport arguments
with an explicit finite board, a fresh-cell budget, immediate victory, and a
nonempty legal Breaker response requirement. It retains the same Apache-2.0
origin notice; the finite-board changes are described in its source header.
