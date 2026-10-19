#!/usr/bin/env python3
"""Run the pinned upstream comparator and two rejection controls on Linux.

The output directory must be new. Source modules are copied into it and built
only by the real comparator, under Landrun and the recommended systemd guard.
Existing Mathlib packages are copied, never modified in place.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
from datetime import datetime, timezone


UPSTREAM = "1581d4cbdd69a0faf34b2089614fe2a814316a6a"
PINS = {
    "comparator": "d03acab154d269c06e60e4de7e4cc85deebff94b",
    "lean4export": "076e8e57707e813375e8f9da8bf989799ace9680",
    "landrun": "ec104f6edc1e14d7fec6d31146f1ec6f9c192c5a",
}
SOURCE_HASHES = {
    "OAI/Algebra/Universal/GraphCriterion.lean": "bd80c2bea95ee1b4f7118fc8dc272aebac7b23038ba93cdafd386dc1b688fb50",
    "OAI/Algebra/Universal/Congruence.lean": "30e9201344dcf4069ca9ace276c76dc3b1507d09f0f6bfbf5a7c5d693ac9716c",
}
CHALLENGE_HASHES = {
    "ComparatorChallenges/FiniteCongruenceGraph.json": "4527a9b96cf508c538af6e5c40654257f25bab583ac40fa5e88cb963ee56e66a",
    "ComparatorChallenges/FiniteCongruenceGraph.lean": "2ee495def2e1228bf13df520f6c66699ec22b2cd3bc1ae7383a30957aae9f967",
}


def capture(*args: str, cwd: Path | None = None) -> str:
    return subprocess.check_output(args, cwd=cwd, text=True).strip()


def sha256(path: Path) -> str:
    with path.open("rb") as stream:
        digest = hashlib.sha256()
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def git_root(path: Path) -> Path:
    for parent in path.resolve().parents:
        if (parent / ".git").exists():
            return parent
    raise ValueError(f"Cannot locate source Git checkout for {path}")


def check_checkout(path: Path, expected: str) -> dict:
    revision = capture("git", "-C", str(path), "rev-parse", "HEAD")
    status = capture("git", "-C", str(path), "status", "--porcelain")
    if revision != expected or status:
        raise ValueError(f"Expected clean checkout {expected}: {path}")
    return {"revision": revision, "tracked_and_untracked_tree_clean": True}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packages", type=Path, required=True,
                        help="Prepared lean/upstream/.lake/packages directory")
    parser.add_argument("--comparator", type=Path, required=True)
    parser.add_argument("--lean4export", type=Path, required=True)
    parser.add_argument("--landrun", type=Path, required=True)
    parser.add_argument("--landrun-source", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True,
                        help="New directory for isolated project, logs and receipt")
    args = parser.parse_args()
    if sys.platform != "linux" or os.geteuid() == 0:
        parser.error("Run as an unprivileged Linux user with systemd --user and Landlock.")
    lean_version = capture("lean", "--version")
    if "version 4.34.1," not in lean_version:
        parser.error("Put the pinned Lean 4.34.1 toolchain on PATH.")
    here = Path(__file__).resolve().parent
    upstream = here.parent / "upstream"
    tools = {name: getattr(args, name).resolve()
             for name in ("comparator", "lean4export", "landrun")}
    tool_records = {}
    for name, binary in tools.items():
        source = args.landrun_source.resolve() if name == "landrun" else git_root(binary)
        tool_records[name] = check_checkout(source, PINS[name])
        tool_records[name]["binary_sha256"] = sha256(binary)
    manifest = json.loads((here / "lake-manifest.json").read_text())
    dependencies = {entry["name"]: check_checkout(
        args.packages / entry["name"], entry["rev"])
        for entry in manifest["packages"]}
    for name, expected in SOURCE_HASHES.items():
        if sha256(upstream / name) != expected:
            raise ValueError(f"Pinned upstream source hash mismatch: {name}")
    for name, expected in CHALLENGE_HASHES.items():
        if sha256(here / name) != expected:
            raise ValueError(f"Pinned upstream challenge hash mismatch: {name}")

    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=False)
    project = output / "project"
    project.mkdir()
    shutil.copytree(args.packages, project / ".lake" / "packages", symlinks=True)
    shutil.copytree(upstream / "OAI", project / "OAI")
    shutil.copytree(here / "ComparatorChallenges", project / "ComparatorChallenges")
    shutil.copy2(here / "lake-manifest.json", project / "lake-manifest.json")
    shutil.copy2(upstream / "lean-toolchain", project / "lean-toolchain")
    shutil.copy2(here / "lakefile.toml", project / "lakefile.toml")

    official_config_path = project / "ComparatorChallenges" / "FiniteCongruenceGraph.json"
    official_config = json.loads(official_config_path.read_text())
    control_sorry = dict(official_config, solution_module=official_config["challenge_module"])
    (project / "sorry-control.json").write_text(json.dumps(control_sorry, indent=2) + "\n")
    challenge = (project / "ComparatorChallenges" / "FiniteCongruenceGraph.lean").read_text()
    expected_statement = "Representable Lat ↔ HasGraphWitness Lat := by\n  sorry"
    if challenge.count(expected_statement) != 1:
        raise ValueError("Unexpected original challenge theorem text")
    mismatch = challenge.replace(expected_statement, "True := by\n  trivial")
    (project / "ComparatorChallenges" / "MismatchControl.lean").write_text(mismatch)
    control_mismatch = dict(official_config, challenge_module="ComparatorChallenges.MismatchControl")
    (project / "mismatch-control.json").write_text(json.dumps(control_mismatch, indent=2) + "\n")

    receipt = {
        "started_at_utc": datetime.now(timezone.utc).isoformat(),
        "upstream_revision": UPSTREAM,
        "lean_version": lean_version,
        "lake_version": capture("lake", "--version"),
        "landrun_version": capture(str(tools["landrun"]), "--version"),
        "platform": platform.platform(),
        "unprivileged_user": True,
        "runner_sha256": sha256(Path(__file__)),
        "sandbox": {"implementation": "Landrun", "systemd_restrict_address_families": "~AF_UNIX"},
        "tools": tool_records,
        "dependencies": dependencies,
        "input_sha256": {name: sha256(project / name) for name in (
            *SOURCE_HASHES, "ComparatorChallenges/FiniteCongruenceGraph.lean",
            "ComparatorChallenges/FiniteCongruenceGraph.json", "lake-manifest.json",
            "lean-toolchain", "lakefile.toml")},
        "scope": "Original upstream graph_criterion supporting theorem only; no Nanoda or full-corpus check.",
        "checks": [],
    }
    passed = True
    for label, config, should_accept in (
        ("official", "ComparatorChallenges/FiniteCongruenceGraph.json", True),
        ("sorry-control", "sorry-control.json", False),
        ("mismatch-control", "mismatch-control.json", False),
    ):
        command = ["systemd-run", "--user", "--pipe", "--wait",
                   "--property=RestrictAddressFamilies=~AF_UNIX",
                   "-E", "PATH=" + os.environ["PATH"],
                   "-E", "COMPARATOR_LANDRUN=" + str(tools["landrun"]),
                   "-E", "COMPARATOR_LEAN4EXPORT=" + str(tools["lean4export"]),
                   "--working-directory=" + str(project), "--",
                   "lake", "env", str(tools["comparator"]), config]
        result = subprocess.run(command, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (output / f"{label}.log").write_text(result.stdout)
        # An unrelated build error is not a successful rejection control.
        if should_accept:
            ok = result.returncode == 0 and "Your solution is okay!" in result.stdout
        elif label == "sorry-control":
            ok = result.returncode != 0 and "Illegal axiom detected: 'sorryAx'" in result.stdout
        else:
            ok = result.returncode != 0 and "Challenge and solution theorem statement do not match" in result.stdout
        passed = passed and ok
        receipt["checks"].append({"name": label, "expected_acceptance": should_accept,
                                  "exit_code": result.returncode, "passed": ok,
                                  "log": f"{label}.log"})
        (output / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
        print(f"{label}: exit {result.returncode}; expected outcome {'PASS' if ok else 'FAIL'}")
    receipt["source_bytes_unchanged_after_checks"] = all(
        sha256(project / name) == expected for name, expected in receipt["input_sha256"].items())
    passed = passed and receipt["source_bytes_unchanged_after_checks"]
    receipt["completed_at_utc"] = datetime.now(timezone.utc).isoformat()
    receipt["passed"] = passed
    (output / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
