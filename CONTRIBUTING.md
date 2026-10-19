# Contributing

Start with a small, reproducible discrepancy, a new checked example, or a clearer
explanation. Read [METHOD.md](METHOD.md) before changing the quantifiers.

1. Create a branch and describe the mathematical claim being changed.
2. Run `python -m unittest discover -v`.
3. Run `python run_experiment.py --out runs/my-change`.
4. Run `python scripts/check_evidence.py --evidence runs/my-change`.
5. Compare with the recorded release using
   `python scripts/check_evidence.py --evidence runs/my-change --compare evidence`.
   Explain any intended mathematical difference; never update expected results
   merely to make a failing check pass.
6. Include a small failing example and regression check when fixing a defect.

The two graph implementations and algebra verifier deliberately use different
algorithms. Preserve their independence when refactoring. Prefer explicit
resource limits over silently truncated enumeration. A failed or interrupted
check must not become a positive certificate.

Run `python scripts/build_charts.py` after changing accepted evidence (optional
chart dependencies are in `requirements-charts.txt`). Commit the source data,
generated figures, and the reason for the change together. Lean changes have
their own reproduction steps in [docs/LEAN_VERIFICATION.md](docs/LEAN_VERIFICATION.md).

Claims about novelty need primary literature references. Scope every negative
result by the exhausted carrier bound, and scope operation minima to the exact
congruence embedding. Passing software tests does not prove arbitrary Python
programs correct or establish the general theorem.

Contributions are provided under Apache-2.0. Disclose substantial AI assistance
and distinguish computational replication, AI review, and external peer review.

Use the issue templates for reproduction problems and research proposals, and
the pull request template to record evidence and scope. See [SUPPORT.md](SUPPORT.md)
for questions. Discuss claims and code respectfully, welcome good-faith questions,
and keep criticism specific to the work. Harassment and disclosure of another
person's private information are not acceptable in project discussions.

## Explain the math for people seeing it for the first time

For explanations and showcase material, start with a small concrete example,
then a simple diagram, then the mathematical name or notation. Say what each
node, line, color, and direction means. In particular, distinguish carrier
objects from lattice nodes, which represent whole congruences. Show both a
passing and a failing case when explaining a check.

Connect each result to why it matters. Distinguish an example, a bounded
exhaustive result, a conjecture, and a formal theorem. State which carrier and
relations are fixed when discussing operation minima. Use the
[illustrated introduction](docs/PLAIN_LANGUAGE_GUIDE.md) as a starting point.

## Preserve the query contract

Atlas data changes must preserve the meanings of versioned identifiers or
introduce a documented new identity version. Read [the query contract](docs/ATLAS_QUERY.md)
before changing response fields, relation enumeration, or shape canonicalization.
Regenerate claim records with `python scripts/query_atlas.py build-claims` after
rebuilding and independently checking the atlas. Run the commands in
[ATLAS.md](docs/ATLAS.md), including the query tests, before submitting changes.
Include evidence and limits for each added claim; a display name is not a citation.
