#!/usr/bin/env python3
"""Check the registered snapshot bytes. This is not a semantic/proof checker."""

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = ROOT / "benchmarks/semantic-context-v1/freeze.json"


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT, stderr=subprocess.PIPE)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def normalized(data):
    # Confirm UTF-8; preserve all bytes except CRLF, as existing citations do.
    data.decode("utf-8")
    return data.replace(b"\r\n", b"\n")


def verify(manifest, check_worktree=False):
    commit = manifest["atlas_commit"]
    if not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise ValueError("atlas_commit must be a full Git commit identity")
    actual_commit = git("rev-parse", f"{commit}^{{commit}}").decode().strip()
    if actual_commit != commit:
        raise ValueError("commit identity mismatch")
    if git("rev-parse", f"{commit}^{{tree}}").decode().strip() != manifest["git_tree"]:
        raise ValueError("Git tree mismatch")
    entries = manifest["files"]
    if not entries:
        raise ValueError("empty file manifest")
    seen = set()
    for item in entries:
        path = item["path"]
        parts = PurePosixPath(path).parts
        if (not parts or PurePosixPath(path).is_absolute() or ".." in parts
                or "\\" in path or ":" in path or path in seen):
            raise ValueError(f"unsafe or duplicate path: {path}")
        seen.add(path)
        blob = git("rev-parse", f"{commit}:{path}").decode().strip()
        if blob != item["git_blob"]:
            raise ValueError(f"blob identity mismatch: {path}")
        data = git("cat-file", "blob", blob)
        if len(data) != item["bytes"] or sha256(data) != item["sha256_exact"]:
            raise ValueError(f"frozen byte mismatch: {path}")
        if sha256(normalized(data)) != item["sha256_utf8_crlf_to_lf"]:
            raise ValueError(f"normalized hash mismatch: {path}")
        if check_worktree:
            local = ROOT / path
            if not local.is_file() or sha256(normalized(local.read_bytes())) != item["sha256_utf8_crlf_to_lf"]:
                raise ValueError(f"working file differs from snapshot: {path}")
    return len(entries)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--worktree", action="store_true", help="Also compare local files after CRLF-to-LF normalization")
    args = parser.parse_args()
    try:
        manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
        count = verify(manifest, args.worktree)
    except (OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as exc:
        print(json.dumps({"status": "failed", "error": str(exc)}))
        return 1
    print(json.dumps({"status": "ok", "atlas_commit": manifest["atlas_commit"],
                      "files_checked": count, "worktree_checked": args.worktree,
                      "boundary": "Snapshot integrity only; no semantic verification or model evaluation."}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
