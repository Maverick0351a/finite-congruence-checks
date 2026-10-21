# Preparation record — 19 October 2026

Eight public development tasks and matched Markdown/JSON reference packets are
prepared. This is a rendering feasibility design. No task subset has been
scheduled, and the original two-task pilot and its four reserved families remain
unchanged and paused.

The source snapshot is `5a6e46de73ed045e72149f4f912e2bbee0463086`.
The [freeze manifest](freeze.json) records source and generated-byte hashes.
The [numeric report](preparation-report.json) records offline retrieval counts.

| Check | Result | What it establishes |
| --- | --- | --- |
| Pinned source reconstruction | Pass | Selected records and trace rows reconstruct from identified Git objects |
| Fact parity | Pass | Both presentations contain the same eight records and 18 identical raw references |
| Shared search | Pass | Same inventory and search results in both conditions |
| Mutation controls | Pass | Altered facts and omitted reference units fail the freeze check |
| Broker denials | Pass | Key paths, other-condition paths and unknown tools are denied through this interface |
| Per-task prompts | Pass | Each common prompt contains one assigned task and the shared response contract |
| Saved packet hashes | Pass | All 12 packet/prompt files and the separate fact map match the manifest |
| Offline tests | 10 passed | Includes pagination, limits, scalar-type distinctions and source selection checks |
| Private key integrity | Pass | Hash, eight-task coverage and named-question/reference coverage agree |
| Live process isolation | Unverified | No restricted answering process was launched |
| Actual benchmark usage | Unavailable | No answering sessions or native preflight ran; token telemetry is null |
| Semantic key review and scoring calibration | Pending | Integrity checks do not establish correct semantic judgments |

The controller selected a reference path for each task, then added the same two
generic searches in both conditions. All 16 paths fit the proposed limits;
the largest required nine calls and 22,899 returned UTF-8 bytes, including broker
metadata. This is an existence check using privileged source choices, not
observed agent effort or a token estimate. The paths are not exposed to answerers.
Key holders can reproduce the counts using `check-paths --key PATH`.

The canonical local packet output is
`runs/evidence-applicability-packets-v1-reviewed/`. An earlier local `v1` output
was retained during authoring and is not the final packet. Ordinary source
`check` recomputes packet hashes; it does not inspect arbitrary existing output
directories. Before later execution, the controller must validate the actual
bytes it intends to serve against the manifest.

The private key is held separately under ignored `runs/`. It is not in the
public packets or Git history. A local ignored directory is not an isolation
boundary. The future answering process must have only its assigned prompt and
one condition's broker capabilities, with no access to controller files.

Preparation review covered source facts, mathematical applicability, packet
parity and code. Corrections clarified mixed-proposition answers, selected trace
rows and the limited Markdown/JSON comparison. The renderer now distinguishes
string labels from numbers; the broker is vendored with its previously verified
SHA-256 so ordinary reproduction does not depend on retaining an unmerged branch.
This is AI preparation review, not external peer review or blind outcome scoring.
The reviewer did not receive the private task key.

The remaining execution gates are in [protocol.json](protocol.json). Dummy-only
runtime isolation and actual usage capture must pass, the semantic key and scorer
must be reviewed, and a revised small-pilot estimate must be shown before the
user approves answering sessions. No performance advantage follows from these
preparation checks.
