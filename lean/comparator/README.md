# Official upstream comparator check

The original OpenAI `FiniteCongruenceGraph` comparator challenge **passes** for
the unchanged upstream solution at revision
`1581d4cbdd69a0faf34b2089614fe2a814316a6a`. The comparator checks the statement
and its referenced definitions, allowed axioms, and acceptance by Lean's kernel.
The checked declaration is `OAI.FiniteCongruence.graph_criterion`.

This is a targeted check of the supporting graph-characterization theorem.
The concrete N5/B3 witness bridge, the Python algorithms, and the rest of the
OpenAI math corpus are separate checks. The original configuration disables
Nanoda; no external kernel was used.

## Recorded result

| Check | Expected result | Actual exit | Result |
| --- | --- | ---: | --- |
| Original challenge and solution | Accept | 0 | Pass |
| Use the placeholder challenge as a solution | Reject `sorryAx` | 1 | Pass |
| Change the challenge theorem statement to `True` | Reject statement mismatch | 1 | Pass |

The comparator printed `Lean default kernel accepts the solution` and
`Your solution is okay!`. The original challenge's intentional `sorry` warning
is expected. It is not permitted in the solution, as the first rejection
control confirms. Logs and hashes are in [evidence/](evidence/).

## Exact tools

All Lean tools below were compiled with the unchanged **Lean 4.34.1** runtime
(Lean commit `5045d0056413266e57c625dcd7c365b10e377c52`). Comparator's compatible
release tag is named `v4.34.0`; no source edits or toolchain-file edits were made.

| Component | Source revision |
| --- | --- |
| [Comparator](https://github.com/leanprover/comparator/tree/d03acab154d269c06e60e4de7e4cc85deebff94b) | `d03acab154d269c06e60e4de7e4cc85deebff94b` |
| [lean4export](https://github.com/leanprover/lean4export/tree/076e8e57707e813375e8f9da8bf989799ace9680) | `076e8e57707e813375e8f9da8bf989799ace9680` |
| [Landrun](https://github.com/Zouuup/landrun/tree/ec104f6edc1e14d7fec6d31146f1ec6f9c192c5a) | `ec104f6edc1e14d7fec6d31146f1ec6f9c192c5a` |
| Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` |

Landrun reports version `0.1.18` and was built with Go `1.24.0`. The separate
manifest pins all nine Mathlib dependencies. The runner requires clean source
checkouts at the recorded tool and dependency revisions and records the actual
binary hashes. Those hashes document this run; another compiler or build path
can produce different tool binary hashes.

## Reproduce on Linux

Prerequisites: an unprivileged Linux account, Landlock support, a working
`systemd --user` service manager, Git, Go 1.24 or later, Python 3.10 or later,
and the pinned Lean 4.34.1 `bin` directory at the front of `PATH`.

First prepare the nine Mathlib dependency checkouts and cache by following
[the targeted upstream instructions](../../docs/LEAN_VERIFICATION.md#upstream-graph-criterion).
Their `.lake/packages` directory can be reused: the runner verifies its pins
and clean source trees, then makes an independent copy. It does not reuse any
compiled OAI solution module. Allow roughly 2 GB of additional scratch space
for the tools and copied dependencies.

From the repository root, with the Lean 4.34.1 runtime already on `PATH`:

```bash
repo="$PWD"
scratch="$(mktemp -d)"
git clone --branch v4.34.0 https://github.com/leanprover/comparator "$scratch/comparator"
git -C "$scratch/comparator" checkout d03acab154d269c06e60e4de7e4cc85deebff94b
(cd "$scratch/comparator" && lake build lean4export comparator)
git clone https://github.com/Zouuup/landrun "$scratch/landrun"
git -C "$scratch/landrun" checkout ec104f6edc1e14d7fec6d31146f1ec6f9c192c5a
(cd "$scratch/landrun" && go build -o "$scratch/landrun-bin" ./cmd/landrun)
python3 lean/comparator/run.py \
  --packages "$repo/lean/upstream/.lake/packages" \
  --comparator "$scratch/comparator/.lake/build/bin/comparator" \
  --lean4export "$scratch/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export" \
  --landrun "$scratch/landrun-bin" \
  --landrun-source "$scratch/landrun" \
  --output-dir "$scratch/result"
```

The output directory must not already exist. It retains the isolated build,
three logs, and `receipt.json`. A runner exit of zero requires acceptance of the
original and rejection of both controls for their intended reasons. An unrelated
build failure does not satisfy a rejection control.

Each comparator invocation has the form recommended by its upstream README:

```text
systemd-run --user --pipe --wait --property=RestrictAddressFamilies=~AF_UNIX
  -E PATH=... -E COMPARATOR_LANDRUN=... -E COMPARATOR_LEAN4EXPORT=...
  --working-directory=... -- lake env .../comparator config.json
```

The real Landrun sandbox and the address-family restriction were both active in
the recorded WSL run. No fake-Landrun development wrapper was used. The trust
boundary includes the official Lean runtime, tool source/builds, OS/hardware,
and the trusted imported Mathlib cache. The comparator checks the selected
theorem's exported dependency closure; this is distinct from a full corpus run.

## Source provenance and license

`ComparatorChallenges/FiniteCongruenceGraph.lean` and `.json` are verbatim copies
from the pinned upstream revision. Their source URLs are
[challenge](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/FiniteCongruenceGraph.lean)
and [configuration](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/FiniteCongruenceGraph.json).
The upstream [Apache-2.0 license](../../reference/LICENSE) applies.
The solution sources come from `lean/upstream/OAI/` and are hash-checked before
copying. Rejection controls are generated only in the scratch project.
