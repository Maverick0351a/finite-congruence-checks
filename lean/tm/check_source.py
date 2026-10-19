"""Check the pinned complete source, byte-for-byte extraction, and Lean wrapper."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
COMMIT = "1581d4cbdd69a0faf34b2089614fe2a814316a6a"
FULL_SHA256 = "0166c40c57bd9eb6ede9e25bda09650b859c81c0d801de9faa3875f195e003fc"
LICENSE_SHA256 = "c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4"
UPSTREAM_PATH = "lean/ComparatorChallenges/NavierStokesAlternating.lean"
FIRST_LINE, LAST_LINE = 10, 66
IMPORTS = ["Mathlib.Logic.Function.Iterate", "Mathlib.Data.Int.Basic"]
PREFIX = (
    "/- Extracted from pinned openai/math; see source/manifest.json.\n"
    "   Changes: narrow imports and namespace wrapper only. Machine definitions unchanged. -/\n"
    + "".join(f"import {module}\n" for module in IMPORTS)
    + "\nnamespace OAI.AlternatingNS\n\n"
).encode("utf-8")
SUFFIX = b"\nend OAI.AlternatingNS\n"


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def expected() -> tuple[bytes, bytes, dict]:
    source = (ROOT / "source/NavierStokesAlternating.lean").read_bytes()
    if sha256(source) != FULL_SHA256:
        raise ValueError("complete upstream source does not match pinned SHA-256")
    if sha256((ROOT / "source/LICENSE").read_bytes()) != LICENSE_SHA256:
        raise ValueError("upstream license does not match pinned SHA-256")
    lines = source.splitlines(keepends=True)
    extract = b"".join(lines[FIRST_LINE - 1:LAST_LINE])
    if not extract.startswith(b"abbrev Rule :=") or not extract.endswith(b"end Machine\n"):
        raise ValueError("pinned extraction boundaries do not contain the expected declarations")
    module = PREFIX + extract + SUFFIX
    manifest = {
        "schema_version": 1,
        "upstream_repository": "https://github.com/openai/math",
        "upstream_commit": COMMIT,
        "upstream_path": UPSTREAM_PATH,
        "upstream_url": f"https://github.com/openai/math/blob/{COMMIT}/{UPSTREAM_PATH}",
        "full_source_path": "source/NavierStokesAlternating.lean",
        "full_source_sha256": FULL_SHA256,
        "extraction": {
            "path": "source/Machine.definitions.txt",
            "first_line_inclusive": FIRST_LINE,
            "last_line_inclusive": LAST_LINE,
            "byte_start": sum(map(len, lines[:FIRST_LINE - 1])),
            "byte_end_exclusive": sum(map(len, lines[:LAST_LINE])),
            "sha256": sha256(extract),
        },
        "generated_module": {
            "path": "MachineExtract.lean",
            "sha256": sha256(module),
            "imports": IMPORTS,
            "prefix_utf8": PREFIX.decode("utf-8"),
            "suffix_utf8": SUFFIX.decode("utf-8"),
        },
        "license": "Apache-2.0",
        "license_path": "source/LICENSE",
        "license_sha256": LICENSE_SHA256,
        "scope": "Only the extracted machine definitions are compiled; the PDE source is preserved as provenance, not checked here.",
    }
    return extract, module, manifest


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate extraction and manifest from the hash-checked snapshot")
    args = parser.parse_args()
    extract, module, manifest = expected()
    if args.write:
        (ROOT / "source/Machine.definitions.txt").write_bytes(extract)
        (ROOT / "MachineExtract.lean").write_bytes(module)
        (ROOT / "source/manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8", newline="\n")
    else:
        if (ROOT / "source/Machine.definitions.txt").read_bytes() != extract:
            raise ValueError("machine definition extraction differs from pinned source slice")
        if (ROOT / "MachineExtract.lean").read_bytes() != module:
            raise ValueError("compiled Lean module differs from exact extraction and approved wrapper")
        if json.loads((ROOT / "source/manifest.json").read_text(encoding="utf-8")) != manifest:
            raise ValueError("source manifest differs from recomputed pinned provenance")
    print(f"PASS: full source {FULL_SHA256}; exact lines {FIRST_LINE}-{LAST_LINE}; module {sha256(module)}")


if __name__ == "__main__":
    main()
