# Semantic-context preservation: preparation

Read the [pre-run proposal](../../docs/SEMANTIC_CONTEXT_PILOT.md) first.

* `freeze.json` pins the atlas commit and selected source/data artifacts.
* `tasks.json` contains six proposed task families and role-delivery rules.
* `rubric.json` defines eight separately reported scoring dimensions.
* `preparation.json` records completed checks and pending execution gates.

These are controller/author artifacts. **Do not expose this directory to an
answering agent.** The prompt dispatcher must extract only that agent's task
and common instructions. The key, task coverage tags, other roles' prompts,
smoke answers, and prior outputs are outside its capabilities.

The answer key, two matched presentations, and enforced runner are pending
review of this proposal. No comparison has run. The two-task first pilot is a
workflow check; the four reserved tasks broaden coverage after that review.
Neither phase can establish a general advantage on its own.

Verify the snapshot with Python 3.10+ and Git:

```sh
python scripts/check_semantic_freeze.py
python scripts/check_semantic_freeze.py --worktree
```

The first command verifies stored Git objects. The second additionally verifies
local files after the atlas's declared CRLF-to-LF normalization. The exact-byte
hashes in the manifest always refer to Git blob bytes. A trusted manifest and
commit are the inputs to this integrity check; it does not authenticate a run,
check a Lean theorem, or establish preservation of meaning.
