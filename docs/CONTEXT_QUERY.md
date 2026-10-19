# Query exact claims and their evidence

The context interface supports two exact N5 construction claims, their
comparison, two proved N5 renamings, and one existing Turing-machine tape claim.
It reads the website's records and separately identified proof supplements,
validates the relevant saved evidence, and returns JSON.
It runs locally using the Python standard library. No model, credentials,
network access, or new Lean run is needed.

```sh
python scripts/query_context.py explain context:family-206:saved-n5:classification:v1
python scripts/query_context.py explain construction:n4-E16709
python scripts/query_context.py compare
python scripts/query_context.py explain tm:tiny-stay:tape:v1
python scripts/query_context.py explain context:family-206:saved-n5:renaming:v1
python scripts/query_context.py explain context:family-206:saved-n5:reverse-labels:v1
```

| Claim ID | Construction ID | Evidence attached here |
| --- | --- | --- |
| `context:family-206:saved-n5:classification:v1` | `saved:family-206:n5:v1` | Exact local Lean classification with a recorded build and kernel replay |
| `construction:n4-E16709` | `atlas:n4-E16709:displayed-operations:v1` | Exhaustive computation with an independent finite check |
| `tm:tiny-stay:tape:v1` | `tm-pair:tiny-stay:v1` | Original execution evidence plus a separately identified exact-pair Lean proof |
| `context:family-206:saved-n5:renaming:v1` | `saved:family-206:n5:rotate-and-swap:v1` | Complete classification, inclusion order, and distinctness transported through a proved carrier bijection and rule permutation |
| `context:family-206:saved-n5:reverse-labels:v1` | `saved:family-206:n5:reverse-labels:v1` | The same three properties transported by reversing object labels while preserving rule order |

`n4-E16709` identifies a relation-family atlas entry. Its construction ID above
specifically names the displayed operation tables at this version. A lattice
shape name such as `N5` is not an accepted claim ID.

An N5 `explain` result includes:

- The exact claim and construction IDs, carrier, ordered operation tables,
  and complete grouping family.
- The compatibility predicate, its quantifiers, conclusion (`statement`),
  assumptions, scope, evidence status, and limits.
- Source paths, hashes, pinned revision references, and applicable Lean
  declarations with exact names, statements, roles, and line links.
- The hash of the website's context record and a description of the binding
  check's limits.

The saved construction uses `FiniteCongruenceChecks.N5.all_relations` for
completeness, `order_exact` for inclusion order, and `theta_injective` for
distinctness. These declarations refer to fixed saved definitions. The atlas
answer has an empty `applicable_lemmas` list and an explicit absence-of-proof
note for its different displayed tables. Its original atlas claim and
independent review references remain intact.

The correspondence is a small, finite calculation:

```text
Saved objects          Rename by [1,3,2,0]          Atlas objects
{0,1,2,3}  ------------------------------------>  {0,1,2,3}
five valid groupings   ------------------------>  same five groupings
inclusion order        ------------------------>  same N5 order
two operation tables   ------------------------>  DIFFERENT tables
```

`compare` includes both claim records and the page's exact correspondence.
It reports the point permutation, the index map between the grouping lists,
the conjugated saved operations, the atlas operations, and the independent
review references. The builder checks all 15 partitions for each construction
and checks the inclusion-order correspondence. The operation lists differ
under **this bijection**; the interface makes no claim about algebra
isomorphism under all possible permutations. It does not transport the saved
Lean proof to the other operation list.

## Two legitimate N5 transfers

The [rotation example](N5_RENAMING.md) and [reverse-label example](N5_PROOF_REUSE.md)
have separate construction and claim IDs. Rotation uses object map `[1,2,3,0]`
and swaps the rules with index map `[1,0]`. Reversal uses `[3,2,1,0]` and keeps
rule order with index map `[0,1]`.
Each record includes both operation tables and grouping families, both object-map
directions, the target-to-source rule index map, and the grouping index map.
These mapping fields are needed to express the new transfer claim. The query
envelope and existing claim records retain their meaning.

```sh
python scripts/query_context.py explain context:family-206:saved-n5:renaming:v1 --out renamed-n5.json
python scripts/query_context.py check renamed-n5.json
```

The record links the generic congruence transport theorem, the source N5
classification, and the instantiated target classification/order/distinctness
proofs. A generated Lean module checks the exact displayed tables and mapping
equations against those declarations. The export also contains a separate
receipt with source hashes and the elaborated axiom audit.

`check` still compares with the registered export. The mathematical permission
to reuse this source result comes from the linked transport proof and binding.
Other valid renamings need their own registration and evidence. A changed rule
map can preserve the congruence family while failing the declared correspondence;
the Lean run tests that case separately. The existing `compare` command still
compares the original saved N5 and `n4-E16709` and does not transfer this new
proof to the atlas's different operation tables.

## One Turing-machine claim

The second-domain example asks: **do these two particular machines leave the
same tape when they first stop on the specified blank input?**

```text
                                One step
Missing instruction       [0] ------------> [0]   stopped, head at 0
Write 1, stay, then halt   [0] ------------> [1]   stopped, head at 0

Stopping time agrees. Head position agrees. Tape contents differ.
```

Both start in state 0. On the left, the missing instruction sets a sentinel
state without writing or moving. On the right, the instruction writes `1`
and enters an explicitly declared halting state. Both final state numbers
happen to be `1`, but their roles are defined by different machine tables.

```sh
python scripts/query_context.py explain tm:tiny-stay:tape:v1 --out proposed-tm.json
python scripts/query_context.py check proposed-tm.json
```

The export preserves every field of the existing tape claim, including its
assumptions, scope, citations, evidence status, and qualified lemma records.
It adds the exact input, both complete machine tables, all saved snapshots
at steps 0, 1, and 2, first-halt configurations, and original input/output
JSONL line locators. Tapes are sorted `[position, nonzero symbol]` pairs;
every unlisted cell is zero. Thus `[]` and `[[0,1]]` describe the complete
final tapes in this example. The claim concerns **tape equality**; the other
properties provide context and retain their own claims in the original atlas.

The same envelope and `check` contract serve both domains. `construction_id`
names the exact machine pair here, while `context` identifies the pair and
claim inside the existing registry with JSON pointers and a registry hash.
No original atlas schema or evidence record is changed.

| Reference | Concrete use | Limit |
| --- | --- | --- |
| Saved native trace and input lines | Observe these exact machines at steps 0–2 | Bounded execution evidence for the recorded build and input |
| `TMOracle.Checks.missing_instruction` | Left transition 0→1: active machine with no instruction | Generic Lean theorem; hypotheses matched to this saved table and trace |
| `TMOracle.Checks.instruction_step` and `instruction_writes` | Right transition 0→1: execute the write/stay/halt instruction | Generic Lean theorems; `instruction_writes` alone describes the old head cell |
| `TMOracle.Checks.halted_fixed` | Both transitions 1→2: already halted | Does not apply to either active configuration at step 0 |

The separate `formal_supplement` now links
`TMOracle.TinyPair.exact_result` to these exact machines and `[]`. It proves
initial nonhalting, first halt at step one, both heads at zero, and both
complete tapes over every integer position. The original claim's limits
describe the original execution snapshot; they do not describe this new
supplement. The generic applicability records retain their original status.
See [the proof and fresh-checkout command](TM_PAIR_PROOF.md). This does not
prove Python or compiled implementation correctness, general translation
equivalence, or any fluid-dynamics result.

Each TM query reuses the existing loader's offline replay of the retained
2,857-configuration receipt and checks the canonical registry, traces, and
both browser copies. This executes Python over saved inputs and outputs; it
does not rebuild Lean or run the native binary. It verifies the existing
collection and replays the supplemental proof receipt before exporting this
one claim. N5 queries load only N5 evidence,
and `compare` remains the two-construction N5 comparison. Other TM claim IDs
remain available through `query_atlas.py tm`, outside this small interface pilot.

## Validate a proposed record

Export an answer directly to UTF-8 JSON, then check it:

```sh
python scripts/query_context.py explain context:family-206:saved-n5:classification:v1 --out proposed-n5.json
python scripts/query_context.py check proposed-n5.json
```

`check` compares the complete parsed export with the registered result for its
claim ID. Object-key ordering and JSON whitespace do not matter. List order,
field presence, values, and types do matter, including `true`, `1`, and `1.0`.
Unknown claim IDs never fall back to a shared shape name. Duplicate JSON keys
and nonstandard numeric constants are rejected.

| Outcome | Exit code | Output |
| --- | ---: | --- |
| Valid query or exact registered record match | 0 | JSON on stdout; `check` reports `supported` |
| Proposed record differs or names an unknown claim | 1 | JSON on stdout with `unsupported`, mismatch paths, and candidate hash |
| Malformed input, invalid query, missing/stale source, failed/timed-out replay, or I/O error | 2 | JSON error on stderr; stdout is empty |

The candidate hash is SHA-256 of canonical JSON (sorted object keys, compact
separators, UTF-8, no ASCII escaping). Registry and JSON citation hashes
normalize CRLF to LF; TM native-artifact references explicitly use raw-byte
hashes. These hashes identify data; they do not prove a mathematical claim.
`check` preserves the proposed file and does not silently repair it. It accepts
`explain` exports only, not comparison results or free-form English answers.

Here **supported means an exact registered record match**. Applicability is
manually curated as `curated_exact_binding`; the query does not ask Lean to
elaborate a supplied theorem or derive whether a different theorem applies.
Changing a fact makes the proposed record unsupported by this binding even
when that fact could be established by a separate argument. Equivalent wording
also needs review and a registered update. This is an evidence interface, not
a semantic-equivalence grader.

For example, replacing saved `g = [0,1,0,1]` with `f ∘ g = [1,0,1,0]` leaves
the five valid groupings unchanged. The current proof reference still names
the original tables. The test therefore requires an unsupported result; a
matching diagram alone cannot authorize that reference.

## Reproduce the controls

```sh
python scripts/build_n5_context.py --check
python -m unittest discover -s scripts -p 'test_n5_context.py' -v
python -m unittest discover -s scripts -p 'test_context_query.py' -v
python -m unittest discover -s scripts -p 'test_context_tm.py' -v
node scripts/check_n5_context.cjs
```

The controls include both valid exports, the exact comparison, changed rules
with unchanged groupings, swapped construction IDs, a real B3 theorem in the
same hashed proof file, removed evidence or assumptions, a broadened
conclusion, malformed JSON, incorrect numeric types, and stale page data.

The TM controls include an unused rule changed while all displayed snapshots
remain identical; input `[0]` substituted for `[]`, which represents the same
blank tape; a different pair or property; a real `halted_fixed` reference from
the same hashed Lean file applied to an active step; and a different pair's
trace pointer inside the same hashed JSON file. Every altered proposal must
be unsupported by the original binding. Additional controls cover missing
evidence, upgrading execution evidence to a proof, universal claims, stale
browser data, domain independence, and structured replay-failure errors.

This is deliberately strict: even the equivalent blank-input representation
requires its own reviewed binding. The interface detects differences from
the registered record; it does not independently discover the reason a
substituted theorem is inapplicable.

The interface is separate from `query_atlas.py`, so its claim registry and the
frozen semantic-context benchmark need no changes. This milestone tests
deterministic record binding. It does not measure improved agent reasoning or
meaning preservation in natural-language explanations; the four benchmark
answering sessions remain paused pending approval.

See [the N5 walkthrough](N5_SOURCE_CONTEXT.md) for the mathematical explanation,
source roles, general graph criterion, and recorded Lean trust boundary.
See [the Turing atlas](TM_ATLAS.md) for the original pair records and
[the translation checks](TM_TRANSLATION_CHECKS.md) for the native build evidence.

## Implementation record — 2026-10-19

Selected the existing `tiny-stay` tape claim for a small cross-domain check.
Added `tm_context.py` as a projection of the existing registry and routed it
through the unchanged explain/check envelope. Preserved every original claim
field and kept the complete input and transition traces alongside it.
Added eleven focused tests, including changes that preserve the observed
trace but invalidate its original binding. Local validation passed all 11
new TM tests, all 17 existing N5 context/query tests, all 50 atlas tests, and
the Node N5 browser-data check. Added the controls to CI and documented the
distinction between the observed tape inequality and the generic transition
proofs. CI and independent review results are recorded in
[PR #11](https://github.com/Maverick0351a/finite-congruence-checks/pull/11).
