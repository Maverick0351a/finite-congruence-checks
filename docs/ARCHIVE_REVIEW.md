# Archive review and evidence boundaries

This is a source-text review, not an execution receipt or a new Lean proof.
It informs the [roadmap](ROADMAP.md) and the proposed
[Turing-machine halt pilot](TM_HALT_PILOT.md). The completed
[grouping checker](GROUPING_CHECKER.md) remains the verified foundation.

## Inputs inspected

The three original uploads were inspected without executing archive contents.
Their exact bytes are retained in a local handoff bundle; they are not imported
as executable dependencies or verified evidence in this repository.

| File | Bytes | SHA-256 |
|:--|--:|:--|
| `formal-audit.tar.gz` | 80,069 | `b12e749e839e5e22d080cd587a42ed68d1785d05081c7af194ab3985af502cb4` |
| `snaky-plane-check.tar.gz` | 31,795 | `af9078cbca6e68541cd48b976b92c6bf1ffc3cb1d87b9d50cedff59249198f87` |
| `review_priority.csv` | 54,467 | `e75b43766cba7d18e9f28e8710473b527c40a622b341b4b87c61aa5f08ed9c7b` |

The CSV contains 372 rows: 130 labeled A, 49 B, and 193 C. These are outputs of
the uploaded screening workflow, not independently verified proof categories.
Neither tarball contains the Turing-machine source files. A separate older
local bundle contains a Python port and historical validation logs; those are
distinct artifacts, not contents of these uploads.

## Formal-audit is a screening tool

Its useful role is prioritizing source review. It does not ask Lean to elaborate
declarations, replay proofs, or resolve identifiers.

| Location in the archive | Finding and consequence |
|:--|:--|
| `formal-audit/src/formal_audit/corpus.py:125` | A catalogue link supplies the `has_lean` flag. That flag does not establish file existence or successful proof checking. |
| `formal-audit/src/formal_audit/scope.py:23–34` | Regular expressions classify selected prose phrases. They are screening heuristics, not semantic checks of theorem scope. |
| `formal-audit/src/formal_audit/burden.py:35–38` | A restricted declaration regex does not parse the full Lean language. |
| `formal-audit/src/formal_audit/burden.py:73–89` | A dictionary keyed by unqualified names can overwrite declarations; matching unparsed bodies can count comments and shadowed names as dependencies. |
| `formal-audit/src/formal_audit/burden.py:102–128` | Traversal begins from theorem bodies, including proof text. The count is not an exact measure of statement assumptions or mathematical difficulty. |
| `formal-audit/src/formal_audit/risk.py:65–88` | The chosen burden threshold contributes to a review ranking; it does not establish a proof defect. |

The archive's `burden.py` has SHA-256
`1173c6da708ab908ff15a3b42b7575ec01dba7423c273ac9ea1a61dfdbed38be`.
Its README's claims of exactness and immunity to lexical ambiguity should not
be imported as assurance. The referenced `elaborate.py` is absent from this
archive. The existing tests do not demonstrate immunity to actual name
shadowing or namespace collisions.

For future proof-dependency claims, extract fully qualified constant references
from Lean's elaborated declaration types and bodies, distinguish direct from
transitive dependencies, and record the relevant axioms and pinned environment.
Even an exact elaborated dependency graph does not by itself establish that a
formal theorem faithfully captures an English claim.

## Two different Snaky certificates

The archive uses the directory name `snaky/`. Its `check.py:15–54` targets
**610 table entries plus six base rows, totaling 616 comparator rows**. The six
base rows are supplied in `snaky.py:145–149`. Its load path is hardcoded, and
`snaky.py:111–129` reads a Lean input file that is missing from the archive.
The `snaky.py` SHA-256 is
`8dde1b4ce3969f2bbf811e14cbf9e146d29b7ef3ce95ca739fb3497c6edf5ba9`.

The checker also prints a mismatch without necessarily exiting unsuccessfully
(`check.py:58–61`). An apparently successful process exit is therefore not a
reliable certificate-acceptance signal for this uploaded version.

The separate 21-move theorem uses **728 cards**. At the pinned upstream commit,
[family 187's documentation](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/docs/187.md)
distinguishes the 21-move strategy from the older comparator material.
The [theorem certificate summary](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GameTheory/SnakyTwentyOne/Certificate/Summary.lean#L94-L109)
and [main theorem](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GameTheory/SnakyTwentyOne/Main.lean#L12-L38)
identify that different object. Inspecting these source texts is not a fresh
kernel replay of the theorem.

Evidence for the 616-row comparator cannot be transferred to the 728-card
theorem. Every accepted record must identify its exact source revision, object,
certificate, checker, and claim. A shared family name is insufficient.

## Turing-machine semantics inspected

The source is the `OAI.AlternatingNS` machine definition in
[`ComparatorChallenges/NavierStokesAlternating.lean`, lines 11–64](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/NavierStokesAlternating.lean#L11-L64).
The inspected file matches the pinned upstream blob:

- Upstream commit: `1581d4cbdd69a0faf34b2089614fe2a814316a6a`.
- Git blob: `0260ba9ba848f8a8b9869a46cf99242b4e9f7232`.
- SHA-256: `0166c40c57bd9eb6ede9e25bda09650b859c81c0d801de9faa3875f195e003fc`.

In `step`, a missing instruction changes the state to the designated halting
sentinel while preserving the head and tape. An explicit instruction updates
the tape and head while entering its target state, which may be a halting state.
An already-halting configuration is left unchanged. Thus two encodings can
agree on eventual halting while disagreeing on final tape contents.

This behavior was independently inspected in the source. The reported Python
benchmark was **not rerun as part of this archive review**. Earlier local logs
from a separate repaired package do record benchmark runs; this statement must
not erase that historical evidence. Neither the older logs nor this inspection
prove a general equivalence between the Python port and Lean definitions.

**Subsequent full-bundle follow-up:** the missing TM code later arrived in
`openai-math-audit-bundle.tar.gz`. The [new rerun record](../evidence/tm-original-review.json)
reproduces its helper and domain bugs and compares complete benchmark configurations.
The [maintained translation check](TM_TRANSLATION_CHECKS.md) documents the repairs,
pinned Lean extraction, source lemmas, and native differential test. These are
new evidence records; the preceding paragraph describes the earlier review's scope.

The filename's reference to Navier–Stokes does not make the proposed pilot a
fluid simulation or a verification of the surrounding PDE claims. The pilot
uses only the small machine definitions and explicitly stated observations.
