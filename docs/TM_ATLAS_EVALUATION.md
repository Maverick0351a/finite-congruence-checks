# Can an agent choose the right Turing evidence?

In one fresh-context Codex retrieval exercise, the agent's first submission
passed all **six structured checks**. It selected the requested pair and
property records, copied the exact observations and citations, identified the
missing-instruction lemma's applicability, and declined both an unsupported BB5
claim and a general Python/Lean equivalence claim.
The separate same-session reviewer accepted all six explanations and the stated
lemma hypotheses, with no substantive findings.

This tests a small, guided retrieval workflow. It does not measure an improvement
over another system, demonstrate a feedback advantage, or establish general
reasoning ability.

## Questions and results

| Question | First response | Structured check |
|:--|:--|:--|
| Are BB2's stopping time, tape, and head all equal? | Time and tape match; heads are -1 and 0 | Pass |
| Are BB4's final tape and head identical? | Tape differs at -10; heads are -10 and -9 | Pass |
| Do equal time and head imply equal tape for tiny-stay? | No: empty support versus `[[0,1]]` | Pass |
| Why does tiny-stay's missing-instruction step preserve tape? | Exact source lemma, active configuration, missing table entry | Pass |
| Do 2,857 matching snapshots prove equivalence for every machine/input? | Unsupported by bounded execution evidence | Pass |
| Can this atlas establish the BB5 tape claim? | Unknown exact pair ID; no supporting record | Pass |

The first question illustrates why separate records matter:

```text
BB2, blank input
  first halt:  6  =  6       same stopping time
  final tape:  four identical nonzero cells
  final head: -1  ≠  0       different final configurations
```

An agent that reports only “both halt in six steps” has not answered the tape
or head questions. An agent that cites BB2 cannot establish a BB5 claim.

## Protocol and retained evidence

The six [tasks](../benchmarks/tm-evidence-v1/tasks.json) and
[structured scorer](../scripts/check_tm_retrieval.py) were written before the
evaluation. A new collaboration subagent was started with `fork_turns=none`.
It received the [saved prompt](../evidence/tm-retrieval-v1/prompt.txt), task
contract, workspace location, and public query command. It was instructed not
to inspect the scorer, tests, documentation summaries, or other agents' output.
The implementation team's earlier context was not forked into this agent.

The agent made ten queries: one discovery query, eight property queries, and
the absent BB5 query. It also read the cited trace document and Lean lemma
source. The [transcript](../evidence/tm-retrieval-v1/transcript.json) retains exact
arguments, exit codes, stdout, stderr, and its declared additional file reads.
The [first answers](../evidence/tm-retrieval-v1/answers.json) were saved before
grading and were not revised after feedback.

The [score report](../evidence/tm-retrieval-v1/summary.json) binds the answers,
tasks, scorer, and atlas dataset by normalized SHA-256. Structured checks require
the exact claim selection, exact property values, all supporting citations,
explicit scope, and no general-equivalence assertion. First-halting claims must
cite complete prefixes. The lemma answer must cite its exact pair/side/step
applicability record; mentioning the theorem somewhere in a large document is
insufficient.

The scorer checks structure and evidence identities. A separate
[AI-assisted review](../evidence/tm-retrieval-v1/review.json) checks the written
explanations and lemma hypotheses. The [run manifest](../evidence/tm-retrieval-v1/run.json)
binds these retained files. Synthetic rejection tests are separate from the
six agent answers: they test altered values, wrong pairs/properties, incomplete
prefix citations, forged hashes, overbroad lemma citations, fabricated claims,
and unsupported equivalence assertions.

## Reproduce the admission checks

From the repository root, using Python 3.10+:

```sh
python scripts/query_atlas.py build-tm --check
python scripts/check_tm_retrieval.py evidence/tm-retrieval-v1/answers.json
python -m unittest discover -s scripts -p 'test_atlas_tm*.py' -v
```

These commands recheck the saved evidence and answers. They do not make a new
model call. The transcript records the original query results; a rerun of those
queries should use the pinned repository version accompanying this record.

## What this establishes

The shared JSON claim format and local query interface were sufficient for this
agent to answer these six guided questions with supporting records. The first
version covers four exact encoding pairs on blank input. Generic Lean step
lemmas explain source behavior under their stated hypotheses; the pair outcomes
remain saved execution observations.

The exercise has one evaluator run, six purpose-built questions, explicit
instructions about scope, and no control arm. The agent shared the local
workspace: its requested reading boundary was not an enforced sandbox, so this
is not a blinded evaluation. The platform did not expose an immutable model
snapshot identifier for this subagent run; settings were inherited from the
calling session. The transcript is a retained local record, not a provider-signed
attestation. Same-session AI review is not outside peer review.

Before expanding the claim, test independently authored questions and repeat
across fresh runs with a fixed evaluation protocol. Formal preservation theorems
and proof of the Python translation are separate work.
