# Sharing draft — not sent

We built Finite Congruence Checks, an independent reproducible experiment around
the finite colored-graph criterion in OpenAI's math corpus.

The release exhausts 143,685 labeled colorings across eight specified lattices
and carrier sizes 1–4. A separate verifier reproduces the search, and a direct
algebra calculation recovers the intended congruence lattices for seven saved
witnesses. The repo includes compact unary operations, inspectable certificates,
charts, and an offline evidence gallery. Lean 4.34.1 compiled the concrete N5/B3
congruence certificates and the actual pinned upstream graph-criterion proof;
both projects passed bundled kernel replay for their target modules. The Lean
record documents the imported-dependency trust boundary and remaining work.

One useful regression result: 1,242 candidates pass the four structural
conditions but fail the required connectivity condition. These cases help test
whether an implementation checks the entire predicate.

This is bounded computational evidence, with no claim of mathematical novelty
or validation of the corpus as a whole. We'd value independent reruns and
criticism of the definitions, certificates, and verification boundary.

Repository: https://github.com/Maverick0351a/finite-congruence-checks

Before sharing, make the repository public intentionally, link the successful
release checks, and check that this wording still matches the verified scope in
LEAN_VERIFICATION.md. Share where such posts are welcome;
start with a focused question or reproducible example relevant to the audience.
