# Evidence applicability development fixtures

Read [the preparation protocol](../../docs/EVIDENCE_APPLICABILITY.md).
Eight public development tasks; no answering sessions scheduled or run.
The earlier semantic-context pilot and four reserved families remain paused.

- `tasks.json`: common prompts, without task-specific answer labels.
- `answer-format.json`, `rubric.json`, `reviewer-prompt.txt`: response/review contract.
- `protocol.json`: conditions, candidate limits, gates and uncalibrated usage.
- `freeze.json`: pinned sources and reproducible packet hashes.
- `key-commitment.json`: hash of the separately held private controller key.
- `broker.py`: unchanged search/read implementation from the original pilot.
- `PREPARATION.md`, `preparation-report.json`: completed offline checks and remaining gates.

Generated reference packets and the private key are not Git-tracked. The source
and prompt history is public, so this collection must not be described as held out.
