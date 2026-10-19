# Semantic-context pilot: packet preparation and dummy preflight

**Result: packets prepared; live preflight blocked before inference. The four
benchmark answering sessions remain paused and require separate user approval.**
No comparison answers, scores, improvements, ties, or regressions were measured.

Recorded 2026-10-19 UTC (2026-10-18 Pacific). This is an addendum to the
[direct-answer protocol](SEMANTIC_CONTEXT_PILOT.md). The user approved temporary
restrictions for up to two dummy inference sessions, each limited to 180 seconds
and a 12,000 reported-token soft threshold, using the existing ChatGPT login.
That approval did not authorize real benchmark answers, paid API calls, new
credentials, or persistent security changes.

## Check results

| Check | Result | Evidence and limit |
| --- | --- | --- |
| Frozen atlas | Pass | All 46 source/data anchors match pinned Git objects and the worktree. |
| Matched packet contents | Pass for mechanical parity and preparation review | 5,912 matching reference IDs; 28 pinned input files; 5,744 shared raw units are identical across conditions. This does not establish preserved meaning in an answer. |
| Source provenance and reconstruction | Pass | Exact file-identity keys retained; all four machine pairs reconstruct to their original values; raw JSONL uses line references, JSON records use pointers. |
| Shared discovery interface | Pass offline | Same index, deterministic ranking, IDs, titles, pagination, limits, and source metadata in both conditions. |
| Forbidden reference access | Pass at the broker boundary | Negative controls cover key, scorer, other presentation, prior output, host path, traversal, URL, and guessed IDs. This does not establish native-tool or OS isolation. |
| Usage accumulator | Pass on synthetic events | Rejects missing, malformed, foreign, and decreasing usage; preserves cumulative totals without adding cached/reasoning subsets twice. No live usage event was received. |
| Native child-process startup | Fail | Three setup attempts exited before initialization completed; retained diagnostics report `Error: invalid transport`. |
| Fresh native model context and exclusive tools | Unverified; blocks inference | No native thread was established. Installed schemas do not establish an exclusive two-tool boundary. |
| Actual model usage capture and asynchronous budget interruption | Unverified; blocks inference | Zero model turns started. There is no live telemetry or interruption demonstration. |
| Saved user configuration | Pass for file integrity | Its before/after hash matched in all three native setup attempts. No saved settings or credentials were written. |

The focused suite passes **21 tests in 1.350 seconds**. The code, tests,
[packet manifest](../benchmarks/semantic-context-v1/packet-manifest.json), and
[machine-readable preflight record](../benchmarks/semantic-context-v1/preflight-result.json)
are available for inspection. A separate AI preparation reviewer assessed
packet parity and probe behavior. This is neither blind outcome scoring nor
external peer review.

## What the two packets contain

The builder reads Git blobs from
`cddf9cf1c2d06df36bc516fb0b461daf6365920e`, never a changing working copy.
It renders the same selected facts as ordinary documentation or compact JSON.
Grouping records include 39 constructions and 106 claims. Machine records
include four pairs, 12 property claims, and four lemma records. Both conditions
retain the same authoritative source and proof references.

An author-only fact map records source pointers, value hashes, text spans, and
reconstruction rules. Source code, execution rows, and complete machine prefixes
are shared raw evidence. Repeated provenance within prefixes is factored
losslessly: every original row and reference can be reconstructed. No execution
step is dropped to fit a budget.

Search uses a common index independent of presentation: title-token overlap,
logical records before raw execution rows, inverse-document-frequency body
score, then stable reference ID. It returns at most five IDs and titles, without
answer snippets. Reads include the same pinned source metadata in both
conditions. The 48,000-byte budget counts UTF-8 content plus provenance and
control metadata; JSON escaping of content is logged separately as transport
bytes. Read pages reserve headroom for metadata inside the 12,000-byte ceiling.
Independent review checked every page; the largest accounted page is 11,474 bytes.

No benchmark task labels, answer key, earlier answers, retrieval reviews, or
new task-specific conclusions enter either packet. Information parity is a
property of this preparation; whether a model uses that information correctly
is still unanswered. The documentation is a mechanically rendered field/prose
reference, not an independently authored tutorial. This comparison would test
that specific presentation contrast.

Review found and corrected two packet defects before any answering session:
formatting changed underscores/case in source filename keys, and repeated
context plus raw rows buried the relevant machine pair in search. A later
offline run detected the ranking regression (one failure out of 18 checks);
the title/ranking implementation was restored and rechecked. Native reporting
controls now reject absent inventory fields and mark failed/incomplete MCP
discovery unverified. Previously those cases could appear as empty inventories.
Those reporting bugs did not affect the retained native attempts, which failed
before returning any inventory.

## Actual preflight activity and usage

Native setup used CLI `0.163.0-alpha.10.2`:

| Attempt | Requested transport | Measured probe duration | Last operation | Outcome |
| --- | --- | ---: | --- | --- |
| 01 | `--listen stdio://` | 0.031 s | `initialize` request | Process closed stdout before response |
| 02 | `--listen stdio://` | 0.031 s | `initialize` request | Same; diagnostic `Error: invalid transport` retained |
| 03 | `--stdio` | 0.032 s | `initialize` request | Same diagnostic |

The summed **0.094 seconds** covers measured probe blocks; it excludes version
and login checks, packet construction, tests, preparation, and review. All three
reports are preserved under
[preflight-records](../benchmarks/semantic-context-v1/preflight-records).
They are process setup attempts, not three dummy answering sessions. There were
**zero dummy inference turns, zero benchmark answering sessions, and zero paid
API calls**. Native token usage is **null/unavailable**, not a measured zero.
Preparation and review model usage is not metered by this runner and must not
be inferred from these counts.

A separate scripted exercise used only fictional lamp observations. Each
condition performed one search, two allowed reads, five denied reads, and a
ninth invocation blocked before returning content:

| Scripted condition | Attempted calls | Returned responses | Budgeted bytes | Transport bytes | Measured broker duration |
| --- | ---: | ---: | ---: | ---: | ---: |
| Documentation | 9 | 8 | 649 | 689 | 0.000174 s |
| Atlas | 9 | 8 | 623 | 671 | 0.000114 s |

These timings use `time.perf_counter` and cover Python broker execution only.
An earlier scripted run's coarse monotonic clock reported zero-duration blocks;
that record is retained too. No answering model produced a lamp answer. These
byte and timing differences are not evidence of model efficiency or an atlas
advantage. Calls, responses, denials, and limit errors are preserved.

The **66,000–190,000-token** planning estimate remains **uncalibrated**:
44,000–136,000 for four answers plus 22,000–54,000 for four blind reviews.
It excludes preparation and preflight. No bill, price quote, or measured token
total can be derived from these tests. A successful live dummy preflight is
needed before revising it from actual usage.

## Why execution stopped

The installed app-server schema describes `dynamicTools` as additional tools.
Its `disabledPluginIds` description says the list does not itself filter
capabilities. No exhaustive pre-inference tool/prompt manifest or exclusive
dynamic-tool gate was established in this inspection. Config flags, an empty
MCP listing, and a fresh thread ID would each be insufficient alone. Startup
failure additionally prevented observing effective runtime settings.

The current setup probe intentionally has no `turn/start` implementation; it
cannot submit a question. Only native login status confirmed the existing
ChatGPT route. The probe did not complete its own `account/read`, resolve a
model, or receive usage notifications. Requested settings in its logs must not
be interpreted as settings whose enforcement was observed.

Next, establish a dedicated runner with a verifiable exclusive search/read
boundary, inspect its actual instructions and tool surface, and use fresh dummy
contexts to test forbidden access and live usage. A controller watchdog must
interrupt while the model makes no tool calls: checking elapsed time only when
the broker is called is insufficient. Verify token-threshold handling and
retain overshoot and every failure. Paid API usage, new credentials, or further
security-setting changes need user approval before use.

The private key, final scorer/reviewer package, and complete per-task resource
feasibility checks remain execution gates. A future reserved task's two largest
complete prefixes alone occupy 49,743 bytes before discovery and source metadata,
exceeding today's 48,000-byte ceiling; resolve that budget openly before
scheduling it. The four reserved task definitions have not changed or been used
for answering trials. Handoffs and repetitions remain deferred.

## Reproduce preparation without model calls

Use Python 3.11+ and Git. Each output path must be new so prior artifacts survive.

```sh
python scripts/semantic_packets.py --out runs/semantic-packets-reproduction
python -m unittest discover -s scripts -p test_semantic_preflight.py -v
python scripts/semantic_dummy_preflight.py --out runs/semantic-dummy-reproduction.json
python scripts/check_semantic_freeze.py --worktree
```

The generated manifest's status describes its build stage. This report records
subsequent review and the blocked runtime result separately. Reproducing hashes
and tests does not verify mathematical claims or model reasoning.
