"""Check the actual Lean toolchain and installed Git dependencies against pins."""
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT / "lean/upstream"


def capture(*command, cwd=PROJECT):
    return subprocess.check_output(command, cwd=cwd, text=True).strip()


def main():
    version = capture("lake", "env", "lean", "--version")
    if "version 4.34.1," not in version:
        raise ValueError(f"Expected Lean 4.34.1, got {version}")
    dependencies = []
    manifest = json.loads((PROJECT / "lake-manifest.json").read_text())
    for entry in manifest["packages"]:
        if entry["type"] == "path":
            actual = (PROJECT / entry["dir"]).resolve()
            if entry["name"] != "finiteCongruenceChecks" or actual != (ROOT / "lean").resolve():
                raise ValueError(f"Unexpected local dependency: {entry['name']}")
            continue
        path = PROJECT / ".lake/packages" / entry["name"]
        revision = capture("git", "rev-parse", "HEAD", cwd=path)
        status = capture("git", "status", "--porcelain", cwd=path)
        if revision != entry["rev"] or status:
            raise ValueError(f"Dependency differs from lock or has local changes: {entry['name']}")
        dependencies.append({"name": entry["name"], "revision": revision, "working_tree_clean": True})
    print(json.dumps({"passed": True, "lean": version, "lake": capture("lake", "--version"),
                      "dependencies": dependencies,
                      "local_dependency": "lean (covered by the runner source manifest)"}, indent=2))


if __name__ == "__main__":
    main()
