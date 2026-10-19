# Grouping checker v1 — recorded evidence

Recorded from committed source `5f3a65f3b9ad29c13a822e3a781476fcc5867be0`.
The source manifest binds exact bytes; later documentation/evidence commits can
retain this run without implying the executable was rebuilt from those commits.

| Check | Observed result |
| --- | --- |
| Lean source build and bundled kernel replay | Passed |
| Exact 11-declaration axiom audit | Passed; only permitted standard axioms |
| Native/reference comparison | 65,536 distinct inputs; 0 disagreements |
| Preservation outcomes | 28,672 true; 36,864 false with valid witnesses |
| Adapter probes | All four groups passed; separate from full word-domain coverage |
| Compiled output fault control | 65,536 intended Boolean mismatches detected |
| Proposal/repair demonstration | `ug4-v1:90e8` rejected with `(0,1)`; `ug4-v1:80e8` accepted |
| Python controls, including evidence admission | 31 passed on Linux and Windows |

- [`summary.json`](summary.json): exact source/binary hashes, toolchain, compiler
  target/settings, command logs, proof audit, coverage, and mutation result.
- [`native.jsonl.gz`](native.jsonl.gz): every native output, in exact stdout order.
- [`demo.json`](demo.json): deterministic propose/check/repair/recheck protocol.
- [`proposal.json`](proposal.json), [`repair.json`](repair.json): individually
  validated result records citing this receipt and the exact transcript case.
- `logs/` and `build-traces/`: byte-preserved command output, compiler traces,
  response files, and dynamic dependency report. Static link flags are in `.rsp`.
- `wrapper-mutation/`: the isolated altered wrapper, compile traces, native
  transcript, and every deliberate disagreement in `comparison.json.gz`.

The main executable SHA-256 is
`af15b1331866d4a3a0f8d8956d1629769d269e5e24ba9fc6534ae3bf46f985a6`.
The recorded platform is Linux x86-64 under WSL, Lean 4.34.1. Exact compiler
version and runtime dependencies are retained in the receipt and logs.

Large executable archives are distributed with the
[pilot prerelease](https://github.com/Maverick0351a/finite-congruence-checks/releases/tag/grouping-checker-v1):

| Release asset | Local run path | Purpose |
| --- | --- | --- |
| `grouping-checker-linux-x86_64.gz` | `binary.gz` | The correct tested executable |
| `grouping-wrapper-fault-linux-x86_64.gz` | `wrapper-mutation/binary.gz` | Deliberately wrong output wrapper, retained only as a rejection control |
| `grouping-checker-v1-evidence.zip` | This directory | Compact source/log/transcript evidence |
| `SHA256SUMS.txt` | Release directory | Compressed asset checksums |

Each binary archive's compressed and raw hashes are already in `summary.json`.
Offline result validation checks source/log/transcript consistency and reports
whether the executable archive was available. Live checking requires the actual
binary to match its recorded hash. Rebuild with the
[documented reproduction commands](../../docs/GROUPING_CHECKER.md).

This evidence supports the generic source theorem and bounded agreement for
this executable. It does not prove machine-code refinement, the compiler,
arbitrary runtime states, an entire congruence family, or search minimality.
The deterministic demo does not measure an LLM's repair capability. Independent
algorithms and AI review here are not external peer review.
