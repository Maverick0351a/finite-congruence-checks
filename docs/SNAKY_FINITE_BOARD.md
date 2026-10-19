# Snaky on a finite board

The finite-board Lean extension, complete local-module kernel replay,
allowed-axiom audit and seven altered-claim rejections pass. The separate Python
checker reconstructs all 728 certificate cards. The [saved receipt](../evidence/snaky-finite-v1/proof/summary.json)
records exactly which sources and commands were checked.

Two players take turns claiming an empty square. Maker moves first and tries to
own a copy of this six-cell shape. Breaker tries to prevent that. Rotations,
reflections and translations of the shape count; resizing does not.

```text
               ■ ■
         ■ ■ ■ ■
         0 1 2 3 4   x
```

The bottom row is `y = 0`; the upper cells are `(3,1)` and `(4,1)`. The formal
definition is the pinned upstream [`snaky` and `HasSnaky`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GameTheory/SnakyTwentyOne/Model.lean).

The paper already gives a strategy that wins within 21 Maker claims on a
particular set of 251 squares, and therefore on the containing 17 by 17 square.
Its [finite-board argument](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Snaky-in-21-Maker-moves-September-25-2026/build/strategy.tex)
is the result this extension formalizes. The pinned upstream Lean
[scope note](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/docs/187.md)
selects the infinite-grid strategy. This project adds formal
coverage of that finite-board corollary, without asserting a new move bound or
mathematical novelty.

## How the certificate works

Think of a card as a small instruction with three parts:

- **Required cells:** cells Maker already owns.
- **Envelope:** cells Breaker has not yet claimed, where the plan can continue.
- **Height:** how many additional Maker claims suffice.

A card offers several smaller continuation cards. Maker claims its pivot. A
single Breaker reply cannot spoil all the continuations, so Maker chooses one
that survives. Heights decrease along this choice. A base card ends by claiming
the remaining cell of a Snaky copy.

Why must a continuation survive? Any cell shared by **every** child envelope is
already owned by Maker after the pivot claim. Breaker must choose a fresh cell,
so its reply cannot belong to every child envelope. At least one child envelope
therefore stays free of Breaker cells. That is the local condition checked at
each combination, including combinations nested inside a numbered card.

There are 728 cards, including six base cards. The final card is number 727;
it starts with no required Maker cells and has height 21. This is the exact
[certificate](../evidence/snaky-finite-v1/certificate.txt) used here. The older
616-card reconstruction has a different bound and does not support this claim.

## Why the board size matters

![The exact 251-cell envelope inside a square with coordinates 0 through 16; P marks the first pivot and S1 to S6 illustrate a target, not played moves](assets/snaky-board.svg)

Sometimes a card's suggested pivot is already owned by Maker. The proof can use
a fresh replacement cell and continue. An infinite grid always has such a cell.
A finite board needs a count: before Maker's 21st claim, at most 20 Maker cells
and 20 Breaker cells are occupied. That leaves at least `251 − 40 = 211` free
cells on the smaller board.

The formal resource condition carries both occupied cells and remaining moves:

```text
occupied cells + 2 × remaining Maker claims ≤ board size
```

After an ordinary Maker/Breaker round, occupancy rises by two and the remaining
claim budget falls by one. The inequality stays true. A winning Maker move
can end play immediately; it does not require another Breaker reply.

At the empty starting position, this budget asks for at least `2 × 21 = 42`
cells. The theorem also requires the board to contain the entire 251-cell
envelope, so it does not assert that a 42-cell board suffices.

The theorem covers every legal Breaker reply on the selected board.
In the square version, Breaker may also play outside the 251-cell envelope.
The finite game definition requires both players' moves to stay on the
board and use fresh cells. Its continuing case requires a legal Breaker reply
to exist, excluding a vacuous win from an exhausted board.

## Evidence and limits

The [independent reconstruction](../evidence/snaky-finite-v1/computational.json)
checks the certificate's finite sets, placements, heights and local combination
conditions. Its Python implementation does not itself prove the game theorem.
The [Lean theorem](../lean/snaky/SnakyFinite.lean),
[literal typed binding](../lean/snaky/SnakyBinding.lean) and
[proof receipt](../evidence/snaky-finite-v1/proof/summary.json) provide separate
formal evidence. Both `envelope_wins` and `square_wins` establish `FiniteWins`
for the stated target, empty initial ownership and bound 21.

The receipt records 194 source hashes, 179 explicitly replayed local modules,
19 declaration axiom reports, and all seven rejected bindings. Only
`propext`, `Classical.choice` and `Quot.sound` occur in the audited dependencies.
The local run used a committed-source export with a warmed build/dependency
cache. Its kernel stage took 1,631.946 seconds; the full 12-stage run took about
30 minutes. These are local measurements, not fresh hosted-build timings.

Stable claim ID: `context:family-187:snaky:finite-board-21:v1`.

## Reproduce the result

To run the complete verification from a fresh checkout:

```sh
python scripts/snaky_proof.py run --out runs/snaky-fresh
```

Use a fresh checkout with Python 3.10 or later, Git, and the pinned Lean 4.34.1
toolchain available through `lake`. The command downloads the pinned Mathlib
dependency cache on its first run. Allow time and disk space for that dependency
and the 728-card proof. The output directory must be new, so a run preserves its
own logs. CI runs the same command on Linux; Windows users can use WSL.
The runner records `LEAN_NUM_THREADS=1` to reduce concurrent compilation work.
This setting is not a strict memory or concurrency limit for `leanchecker`:
the pinned runtime may start another worker when a task waits on dependencies.
The initial local bulk replay reached roughly 14.3 GiB RSS. Allow substantial
memory and disk space; hosted CI has a 120-minute job allowance. Compilation
has a 60-minute stage allowance; the other stages each allow 40 minutes. A
timeout fails verification and preserves the partial stage log and receipt.
The first fresh hosted attempt reached the former 40-minute compilation limit;
it did not reach kernel replay or the negative controls. Its resource behavior
is assessed separately from the warmed local run.

The runner first checks the independent certificate reconstruction and exact
upstream bytes. It then builds the Lean proof, audits the theorem dependencies'
axioms, rechecks the proof modules with `leanchecker`, and compiles seven changed
claim bindings that must fail. Those changes alter the target, envelope, square,
move bound, card number, initial position, or theorem reference. A missing import
or exhausted compiler budget does not count as a successful rejection.

The exact binding checks a mathematical type involving both literal boards, the
literal six-cell target, empty initial sets and move bound 21. It does not rely
only on a filename, theorem name or hash. The original upstream files remain
byte-for-byte copies; sibling modules supply the finite-board argument.

The existing local query interface uses the saved proof receipt alongside
the independent computational record:

```sh
python scripts/query_context.py explain context:family-187:snaky:finite-board-21:v1 --out snaky.json
python scripts/query_context.py check snaky.json
python scripts/snaky_proof.py replay
```

`explain` and `check` replay the saved record and recompute the finite certificate
audit. They do not execute Lean. A changed record is **unsupported by this exact
registration**; that alone does not mean its mathematical conclusion is false.
For example, a smaller board would need its own argument. The three activities
have distinct meanings:

| Check | What it establishes |
| --- | --- |
| Lean build, kernel replay and axiom audit | The formal finite-board strategy statement follows from the displayed definitions under the recorded trust assumptions. |
| Independent Python reconstruction | The certificate's concrete finite calculations pass a separately implemented checker. |
| Record binding and offline replay | This saved atlas claim matches the exact proof statement and recorded artifacts. |

Hashes and saved logs support inspection; they are not authenticated attestations.
The runner pins the dependency manifest and Lean release. It rechecks the local
proof modules and audits their transitive axiom dependencies; it does not attest
every cached Mathlib artifact in the build environment. The hosted CI build
provides a separate reproduction from a fresh repository checkout.

The [interactive branch walkthrough](SNAKY_PLAY.md) adds one independently
checked execution, with eight Maker claims and a complete winning placement.
It shares the exact claim with the query interface. That chosen execution is
not a formally verified extraction of the strategy, nor an eight-move guarantee.

This milestone supplies a formal strategy guarantee. It does not formally extract
or benchmark a playable policy, prove that 21 is optimal, find a smallest board,
verify a general translator, or measure whether an AI reasons better. The model
benchmark and training remain paused.
