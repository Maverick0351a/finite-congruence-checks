# Proof-reuse review record

19 October 2026. This is an independent AI code and mathematics review, followed
by maintainer browser checks. It is not an external human approval or a blind
agent-performance evaluation.

## Source and mathematical review

The reviewer approved the implementation with no unresolved blocking findings:

- Read the sibling Lean theorem and the generated binding. The classification,
  order and distinctness concern the exact reverse-label construction.
- Replayed the saved 12-stage receipt, including 22 axiom reports and eight
  expected Lean rejections. Read the rejection logs to verify their causes.
- Independently enumerated all 15 partitions, recovered exactly five valid
  target groupings, and checked compatibility preservation.
- Ran 12 backend tests, 10 presentation tests, and the Node browser-data check.
- Checked the downloaded query envelope and all 11 cited file blobs at
  `3b75f858563b8c7d44a083a5be99ca9d41705e06`.
- Confirmed the original proof files, exporter and rotation receipts are
  unchanged from the base, and replayed the original nine-stage receipt.

Four findings were fixed before delivery: validate actual Git blobs behind
source links, make the CLI example write the file it subsequently checks,
restore keyboard focus after object selection, and document both registered
transfers in the query guide.

## Browser checks

The local page was exercised at a narrow 326-pixel viewport and at the desktop
1280-pixel breakpoint. Both transfer selectors, grouping choices, corresponding
object selection, rule routes, all three mistake explanations, theorem
selection, and download destinations were checked. Keyboard activation keeps
focus and selects matching objects on both sides. There is no horizontal
document overflow at either size.

The mobile evidence graph was changed to a vertical reading path after visual
review found that fitting the desktop arrangement made labels too small. The
native evidence selector supplies the same references without using the canvas.

Hosted CI reruns both original and reverse-label proof commands in the existing
required N5 job. The pull request's checks and merge record provide the delivery
status; this saved review describes the work inspected before those checks.

## Scope

The demonstration establishes an exact application of an existing transport
theorem and checks its presentation. The three deliberately constructed errors
are controls, not observed model mistakes. Browser calculations and Python
export/binding checks are distinct from Lean kernel checking. The compiler is
not verified by these tests. No benchmark answering sessions, reserved task
families, or training were run or changed.
