# Evidence, formats, and reproduction

## Three kinds of records

- **`evidence/`** contains the recorded Python experiment: seven witnesses,
  exhaustive counts and classes, individual checks, recovered algebras, operation
  minima, and execution logs. `run-evidence.json` binds the core Python files and
  every output of that run by SHA-256.
- **`charts/chart-data.json`** contains the values plotted in each figure and the
  exact input-file hashes used to generate the gallery. It can be rebuilt from
  the recorded evidence.
- **`lean/`** contains its own proof source, data correspondence check, and
  verification records. Its verification boundary is described separately in
  [LEAN_VERIFICATION.md](LEAN_VERIFICATION.md).

`evidence/operation-minima-audit.json` is an additional reviewer-authored audit,
run separately from the core experiment. It records its own script and minimizer
hashes. The archive manifest covers this supplementary record too.

## Certificate format

A `*-witness.json` file includes:

| Field | Meaning |
|:--|:--|
| `schema_version` | Certificate schema, currently 1 |
| `source` | Upstream repository, pinned revision, comparator path and hash |
| `lattice.name` | Nonempty string identifying the target |
| `lattice.elements` | Nonempty list of distinct string labels |
| `lattice.bottom` | Zero-based index of the bottom element |
| `lattice.leq` | Square Boolean order table; row `a`, column `b` means `a <= b` |
| `lattice.join` | Square table of zero-based least-upper-bound indices |
| `color` | Square matrix of lattice-element indices on the finite carrier |
| `primary_check` | Search implementation's check, independently recomputed |

Element indices are identifiers, not numerical order comparisons. A verifier
checks the order and lattice laws instead of trusting the name or supplied join
table. Every total self-map, including constant and noninjective maps, is eligible
for the admissibility test.

An operation is encoded by its image list: `[1,0,3,2]` sends vertex 0 to 1,
1 to 0, 2 to 3, and 3 to 2. A partition uses a canonical restricted-growth list:
`[0,0,1,1]` means `{0,1} | {2,3}`. Equal entries identify the same block.

## Reproduce and compare

```sh
python run_experiment.py --out runs/reproduction
python scripts/check_evidence.py --evidence runs/reproduction --compare evidence
python scripts/audit_operation_minima.py --out runs/operation-audit.json
```

The main runner refuses a nonempty output directory. It uses the search record's
certificate registry, checks hashes, propagates child failure, and records
`passed=false` when a stage fails. Its timestamps, Python version, platform,
timings, command arguments, and logs document the run. Machine-specific paths in
logs and arguments are replaced by `{python}`, `{repo}`, and `{out}`; this
normalization is explicitly recorded. Certificates and reports use relative
filenames. Text evidence uses LF line endings on every operating system.

The comparison ignores runtime timings while preserving every mathematical
field in the search, class representatives, multiplicities, and algebra results.
Timestamps and interpreter descriptions are observational metadata, so bitwise
identity of whole run directories is not required.

`check_evidence.py` checks the recorded outputs against the current source and
expected stage list. It detects missing outputs, stale code, changed certificate
bytes, and inconsistent outcomes. It does **not** rerun the mathematics. Hashes
are integrity checks, not cryptographic signatures or independent endorsements.

## Charts and review

```sh
python -m pip install -r requirements-charts.txt
python scripts/build_charts.py
python scripts/build_charts.py --check
```

The builder checks totals, stage attrition, replay agreement, certificate hashes,
and operation counts. The freshness command checks the plotted-data JSON,
gallery provenance, and expected figure files; it does not independently verify
rendered pixels. PNGs receive visual inspection during release preparation.

The original experiment review is retained in [INDEPENDENT_REVIEW.md](../INDEPENDENT_REVIEW.md).
The additional repository review is [RELEASE_REVIEW.md](RELEASE_REVIEW.md). Both
were produced by agents within the same AI session. External replication remains
a useful next step.

## What a certificate cannot say

A positive finite example does not prove a general equivalence theorem. A failed
bounded search does not rule out larger carriers. Minimum unary-operation counts
for one concrete family do not minimize over different embeddings or higher
arities. The [claim ledger](CLAIMS.md) and [method note](../METHOD.md) state those
boundaries beside the results.
