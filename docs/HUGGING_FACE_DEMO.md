# Interactive explorer

[Open the public Hugging Face Space](https://huggingface.co/spaces/Maverick03511/finite-congruence-checks).

The explorer makes the recorded finite examples inspectable: eight lattices,
seven passing witnesses, four connectivity obstructions, equivalence classes,
and minimal unary operations for each saved positive representation. Its
canonical source is `space/` in this repository.

## Run and check locally

Python 3.10+ builds the data using only the standard library. Node.js 18+ runs
the browser-logic checks. Serve the directory over HTTP so the browser can load
the JSON data.

```sh
python scripts/build_space_data.py --check
node scripts/check_space.cjs
python -m http.server 8765 --bind 127.0.0.1 --directory space
```

Open `http://127.0.0.1:8765`. To regenerate the exported JSON and certificates,
run `python scripts/build_space_data.py` without `--check`.

## Evidence boundary

The exporter anchors 23 input files to commit
`355f6d3f0eba56969f3d2a2de2467706a5493db7` using a fixed manifest digest. It replays
all 11 displayed graph examples and all seven positive algebra and operation
minimum checks. It compares search counts against the recorded independent
replay. It does not rerun the complete bounded search.

Passing certificates are copied byte for byte. Failing certificates derive
from recorded first-connectivity-failure samples. For each, the exporter
enumerates admissible maps, constructs the seed-generated graph, and verifies
the disconnected required endpoints. These derived demonstrations do not add
new outcomes to the recorded search counts.

`space/data.json` records input paths, source URLs, SHA-256 hashes, exporter hash,
and the pinned OpenAI math revision. Updating mathematical inputs requires a
deliberate review of the source anchor and manifest digest.

The browser filters edges and computes connected components for display.
It does not execute the exhaustive checker or Lean. M4's negative result is
limited to carriers of at most four points; operation minima hold for each
saved carrier and exact relation family. The [claim ledger](CLAIMS.md) and
[Lean record](LEAN_VERIFICATION.md) define the full validation boundary.

## Review and checks

- Deterministic exporter output and byte-for-byte freshness checks.
- CI checks 31 positive recorded relations, four connectivity obstructions,
  and all 11 downloadable certificate hashes on Linux and Windows.
- A separate AI-assisted reviewer independently checked all 51 threshold views
  across the displayed positive and negative examples, including 708 point-pair
  comparisons and 77 admissible maps across the four failing examples.
- Review prompted clearer lattice-order wording, literal disconnected failure
  diagrams, dark edge-label text, and stacked diagrams on narrow screens.

This is same-session review and implementation testing, not external peer review.

## Publish

Publish only the contents of `space/` to the static Space
`Maverick03511/finite-congruence-checks`. Its README declares `sdk: static` and
`app_file: index.html`. Keep GitHub as the canonical source and record the source
commit alongside each publication. Use the Hugging Face Hub SDK or Git with an
existing authenticated account; never commit credentials.

The deployment contains HTML, CSS, JavaScript, SVG, JSON, and license notices.
It needs no model, GPU, backend, runtime package, external font, or telemetry.
The v0.1.0 research tag and archive remain a separate frozen release.

Maintainer: [Travis Johnson on LinkedIn](https://www.linkedin.com/in/travis-johnson-606207379).
