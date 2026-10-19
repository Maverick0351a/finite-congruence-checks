"""Reproduce the concrete and upstream witness checks and save every result.

Requires the pinned Lean/Lake toolchain on PATH, Git, and network access for the
first dependency/cache fetch. The official comparator has its own Linux runner.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
CACHE_MODULES = ["Mathlib.Data.Fin.Tuple.Basic", "Mathlib.Data.Setoid.Basic",
                 "Mathlib.Order.Hom.Basic", "Mathlib.Data.Finset.Lattice.Fold",
                 "Mathlib.Data.Fintype.EquivFin", "Mathlib.Data.Fintype.Pi",
                 "Mathlib.Data.Fintype.Prod"]


def stages(lake: str, skip_cache: bool, out: Path) -> list:
    steps = [
        ("export", ROOT, [sys.executable, "lean/export_data.py", "--check"]),
        ("correspondence", ROOT, [sys.executable, "lean/check_data.py"]),
        ("export-tests", ROOT, [sys.executable, "-m", "unittest", "discover", "-s", "lean", "-p", "test_*.py", "-v"]),
        ("lean-version", ROOT / "lean", [lake, "env", "lean", "--version"]),
        ("core-build", ROOT / "lean", [lake, "build"]),
        ("core-replay", ROOT / "lean", [lake, "env", "leanchecker", "CertificateData", "FiniteCongruenceChecks"]),
    ]
    if not skip_cache:
        steps.append(("mathlib-cache", ROOT / "lean/upstream", [lake, "exe", "cache", "get", *CACHE_MODULES]))
    steps += [
        ("upstream-build", ROOT / "lean/upstream", [lake, "build"]),
        ("upstream-replay", ROOT / "lean/upstream",
         [lake, "env", "leanchecker", "-v", "OAI.Algebra.Universal", "UpstreamAudit", "ConcreteBridge"]),
        ("axioms", ROOT / "lean/upstream", [lake, "env", "lean", "VerificationAudit.lean"]),
        ("axiom-allowlist", ROOT, [sys.executable, "lean/check_axioms.py", str(out / "axioms.log")]),
        ("environment", ROOT, [sys.executable, "lean/check_environment.py"]),
    ]
    return steps


def source_hashes() -> dict:
    paths = []
    for folder, dirs, files in os.walk(ROOT / "lean"):
        dirs[:] = [d for d in dirs if d not in (".lake", "evidence", "comparator", "__pycache__")]
        paths += [Path(folder) / name for name in files
                  if Path(name).suffix in (".lean", ".py", ".toml", ".json")]
    paths += [ROOT / "lean/lean-toolchain", ROOT / "lean/upstream/lean-toolchain"]
    paths += [ROOT / "verify_witness.py"]
    paths += [ROOT / "evidence" / name for name in
              ("N5-witness.json", "B3-witness.json", "minimized-algebras.json")]
    return {p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(paths)}


def run(out: Path, lake: str, skip_cache: bool) -> bool:
    if out.exists() and (not out.is_dir() or any(out.iterdir())):
        raise ValueError("Choose a new or empty output directory")
    out.mkdir(parents=True, exist_ok=True)
    result = {"schema_version": 1, "passed": False,
              "scope": "N5/B3 concrete proofs and exact upstream graph witnesses; official comparator is separate",
              "started_utc": datetime.now(timezone.utc).isoformat(),
              "python": sys.version, "platform": platform.platform(),
              "cache_fetch_skipped": skip_cache, "source_sha256": source_hashes(), "commands": []}
    destination = out / "result.json"

    def save():
        destination.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")

    save()
    for name, cwd, command in stages(lake, skip_cache, out):
        print(f"Checking {name}...", flush=True)
        log = out / f"{name}.log"
        try:
            with log.open("w", encoding="utf-8", newline="\n") as stream:
                environment = dict(os.environ, MATHLIB_NO_CACHE_ON_UPDATE="1")
                completed = subprocess.run(command, cwd=cwd, stdout=stream, stderr=subprocess.STDOUT,
                                           env=environment, check=False)
            code = completed.returncode
        except OSError as error:
            log.write_text(str(error) + "\n", encoding="utf-8", newline="\n")
            code = -1
        result["commands"].append({"name": name, "cwd": cwd.relative_to(ROOT).as_posix(),
                                   "argv": command, "exit_code": code, "log": log.name,
                                   "log_sha256": hashlib.sha256(log.read_bytes()).hexdigest()})
        save()
        if code != 0:
            print(f"Failed {name}; see {log}", file=sys.stderr)
            return False
    after = source_hashes()
    result["sources_unchanged"] = after == result["source_sha256"]
    result["finished_utc"] = datetime.now(timezone.utc).isoformat()
    result["passed"] = result["sources_unchanged"]
    if not result["sources_unchanged"]:
        result["final_source_sha256"] = after
    save()
    print(f"{'Passed' if result['passed'] else 'Sources changed during checks'}: {destination}")
    return result["passed"]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True, help="New or empty directory for logs and result.json")
    parser.add_argument("--skip-cache", action="store_true", help="Use an already prepared Mathlib cache")
    args = parser.parse_args()
    lake = shutil.which("lake")
    if not lake:
        parser.error("lake is not on PATH; install the toolchain pinned by lean/lean-toolchain")
    try:
        success = run(args.out.resolve(), lake, args.skip_cache)
    except ValueError as error:
        parser.error(str(error))
    raise SystemExit(0 if success else 1)


if __name__ == "__main__":
    main()
