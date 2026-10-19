# Native preflight gate review — 19 October 2026

**Decision: stop before inference.** Source review has not established an
enforceable search/read-only answering session with the installed native
runtime. The user's instruction requires a pause if isolation or usage reporting
cannot be enforced. Fixing transport startup would not by itself satisfy that
condition. No new native startup or dummy inference was performed in this review.

The prepared [PR #13](https://github.com/Maverick0351a/finite-congruence-checks/pull/13)
packets remain separate from this gate review. The original four answering
sessions, four reserved task families, explanation handoffs and model training
remain paused. No private answer key or reserved task prompt was read here.

## Evidence and results

The original runner, records and launch plan were inspected at commit
`a16a9da5cd84c7c4b87326badeff7750a53f56f2` in
[PR #10](https://github.com/Maverick0351a/finite-congruence-checks/pull/10).
The installed binary reports `codex-cli 0.163.0-alpha.10.2` and the same version's
saved generated protocol schema was inspected. Help and version commands are
local inspection, not native sessions or model inference.

| Check | Result | Evidence / limitation |
| --- | --- | --- |
| Historical transport startup | Failed | All three attempts closed stdout during `initialize`; attempts 02/03 recorded `Error: invalid transport`. |
| Invalid-flag explanation | Unsupported | Installed help accepts both `--listen stdio://` and `--stdio`; the root cause remains undetermined. |
| New root context / prior history | Unverified | No original thread was created. An empty `thread/start.thread.turns` is not independent history evidence. |
| Exclusive search/read access | Unverified; blocks inference | Dynamic tools add tools, but the inspected interface does not establish an exclusive capability boundary. |
| Effective restrictions and instruction inventory | Unverified | Original code records several fields without asserting the required values; hooks and skills inventories are not queried. |
| Host filesystem exclusion | Unverified | The installed read-only sandbox shape does not supply a restricted readable-root list. Read-only access alone does not hide the controller files. |
| Actual usage capture | Unverified; blocks comparison | No live usage event was captured. Counts remain `null`, not a measured zero. |
| Live watchdog and final usage | Unverified | The old source has no live turn dispatcher or independent inference watchdog. |
| Benchmark / reserved-task exposure in this review | None | Engineering inspection only; no answering session or private-key access. |
| Main branch protection | Passed by API readback | Nine app-bound required checks, PR workflow and administrator enforcement; see [governance](REPOSITORY_GOVERNANCE.md). |

The saved setup durations were 0.031, 0.031 and 0.032 seconds. These are failed
startup durations, not model response times. The source intentionally contains
no `turn/start` implementation and always blocks before inference.

Original artifacts:

- [Setup runner](https://github.com/Maverick0351a/finite-congruence-checks/blob/a16a9da5cd84c7c4b87326badeff7750a53f56f2/scripts/preflight_semantic_runner.py)
- [Approved launch plan](https://github.com/Maverick0351a/finite-congruence-checks/blob/a16a9da5cd84c7c4b87326badeff7750a53f56f2/benchmarks/semantic-context-v1/preflight-launch-plan.json)
- [Third startup receipt](https://github.com/Maverick0351a/finite-congruence-checks/blob/a16a9da5cd84c7c4b87326badeff7750a53f56f2/benchmarks/semantic-context-v1/preflight-records/native-probe-03.json)

## Corrections to the proposed diagnostic

A new local initialization-only prototype passed eight synthetic subprocess
tests. Independent engineering review then found three gaps those tests missed:

1. A root process could exit while descendants retained its pipes. Cleanup could
   leave descendants running or block while closing a reader stream.
2. Synchronous denial writes could block if the child stopped reading stdin,
   defeating the apparent deadline.
3. Any dictionary result could count as successful initialization, although the
   version-specific response requires typed `codexHome`, `platformFamily`,
   `platformOs` and `userAgent` fields.

The prototype was not launched against Codex and is not shipped as a usable
runner. It is retained locally with its tests and review for follow-up. Passing
eight fixtures does not establish isolation, a working preflight, or accurate
usage capture. The engineering reviewer was not a benchmark answering agent or
a blind outcome reviewer. Review was AI-assisted; no external human approval is
asserted.

## What must change before another dummy inference

Establish a supported, enforceable capability and instruction boundary first.
Use a runtime or isolated execution environment whose allowed tools and reads
can be inspected and constrained. A fresh working directory, a prompt saying
"only use these tools", disabled feature requests, or an empty MCP list cannot
substitute for that boundary. Do not silently substitute a newer online schema
for the installed runtime's schema.

Then validate the actual policy and fresh identity, typed handshake responses,
complete event capture, an independent wall-clock watchdog, final cumulative
usage, bounded cleanup and process lifetime containment. Test malformed
responses, unexpected capabilities, root exit with surviving descendants,
cleanup failures, silent timeouts and late usage. Preserve original failures.

The [official app-server documentation](https://learn.chatgpt.com/docs/app-server)
describes stdio transport, dynamic tools, token-usage notifications and turn
interruption. Those are useful components; their existence does not establish
the required isolation for this installed build.

Previously approved dummy limits remain at most two sessions, 180 seconds and
a 12,000 reported-token soft threshold per session, with eight broker calls and
48,000 returned UTF-8 bytes. Use fictional data only. No new credentials, paid
API route, global settings changes or relaxed security boundary are authorized
by this review. Ask before a change requiring additional authorization.

The original 66,000–190,000-token pilot estimate remains uncalibrated. This
review supplies no measured token figure from which to revise it. After all
gates pass, show the revised estimate and obtain the user's approval before
the four real answering sessions.
