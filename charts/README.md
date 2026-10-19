# Figures and the evidence gallery

Run from the repository root:

```console
python -m pip install -r requirements-charts.txt
python scripts/build_charts.py
python scripts/build_charts.py --check
```

The `--check` mode needs only the Python standard library. The plotting dependency is optional for the mathematical checks.

Open [the offline evidence atlas](../docs/index.html) in a local browser. It uses local SVG images, system fonts, semantic tables and native HTML disclosure controls. No JavaScript, CDN, analytics or remote asset requests are needed. Outbound source links are ordinary links and load only when followed.

| Figure | What it shows | Interpretation |
|---|---|---|
| [Candidate attrition](candidate-attrition.svg) | Full candidate spaces and structural-survivor outcomes, summed over tested sizes | The candidate panel uses a logarithmic axis; the survivor panel uses a linear axis. The scale difference is labeled. |
| [Witness counts](witness-counts.svg) | Every lattice and carrier-size result, as exact annotated heatmaps | Zero denotes an exhausted search with no witness. The two color scales are linear and separately labeled. |
| [Operation minima](operation-minima.svg) | The full admissible map pool and the smallest basic unary signature for each saved representation | Carrier and exact target relations are fixed. Zero basic operations is allowed. |
| [Witness examples](witness-examples.svg) | N5 and B3 cover diagrams, color matrices and selected operation tables | Layout is illustrative; edges, element labels, colors and operations come directly from certificates. |

Each figure is also provided as a high-resolution PNG with the same basename. SVG text remains text, making the figures editable and searchable. Colors are supported by exact printed values and labels.

[chart-data.json](chart-data.json) contains every plotted quantity, all 32 per-size rows, operation records, example matrices, scope statements and SHA-256 digests of the 11 input JSON files. The build reads and reconciles those inputs before plotting. It verifies:

- The candidate-space formula and exhaustive-completion flags.
- Structural rejections, connectivity outcomes, class counts and class multiplicities.
- Numerical agreement with the separately implemented exhaustive replay.
- Certificate provenance and file hashes across the search, algebra and minimization records.
- Operation-pool sizes, selected-signature sizes and exact congruence counts.

`--check` detects stale plotted data after evidence changes and verifies that every figure asset and the gallery's source hashes are present. Regenerate the figures after replacing any evidence file, even when only provenance or run timestamps changed.

These charts describe bounded Python evidence. Their captions do not assert a universal theorem, global nonrepresentability for M4, or novelty. Formal-proof work is documented separately in the repository.
