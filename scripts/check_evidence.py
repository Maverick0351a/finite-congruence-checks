"""Check evidence integrity, successful outcomes, and optional rerun agreement.

This is an integrity check. It does not rerun the mathematics. run_experiment.py
does that. Hashes detect inconsistency; they are not signatures or endorsements.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EXPECTED = {"C2", "C3", "C4", "B2", "M3", "N5", "B3", "M4"}
POSITIVE = EXPECTED - {"M4"}
LOGS = {"unit-tests.log", "search.log", "algebra-verification.log", "operation-minimization.log"} | {
    f"{name}-witness-verification.log" for name in POSITIVE}
OUTPUTS = LOGS | {f"{name}-witness{suffix}.json" for name in POSITIVE for suffix in ("", ".verification")} | {
    "search-results.json", "independent-review-results.json", "verified-algebras.json", "minimized-algebras.json"}


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text(encoding="utf-8"))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def member(folder, name):
    require(isinstance(name, str) and bool(name), "empty or invalid evidence filename")
    path = (folder / name).resolve()
    require(path.parent == folder.resolve(), f"evidence filename escapes directory: {name}")
    return path


def stable(value):
    """Ignore runtime observations; preserve every mathematical field."""
    if isinstance(value, dict):
        return {k: stable(v) for k, v in value.items() if k != "seconds"}
    if isinstance(value, list):
        return [stable(v) for v in value]
    return value


def check(folder, root=ROOT):
    run = read(folder / "run-evidence.json")
    require(run.get("passed") is True, "experiment did not pass")
    require(len(run["commands"]) == 11 and all(c["exit_code"] == 0 for c in run["commands"]),
            "missing or failed experiment stage")
    require({c["log"] for c in run["commands"]} == LOGS, "missing or duplicate experiment stage")
    require(set(run["output_sha256"]) == OUTPUTS, "incomplete or unexpected output hash registry")
    actual_code = {p.name: sha256(p) for p in sorted(root.glob("*.py"))}
    require(run["code_sha256"] == actual_code, "Python code differs from recorded run; reproduce again")
    for name, digest in run["output_sha256"].items():
        require(sha256(member(folder, name)) == digest, f"output hash mismatch: {name}")
    search = read(folder / "search-results.json")
    require(set(search["lattices"]) == EXPECTED and search["max_vertices"] == 4,
            "expected all eight lattices through four vertices")
    require(search["source_sha256"] == sha256(root / "search.py"), "search source hash mismatch")
    require(search["source"]["sha256"] == sha256(root / "reference/FiniteCongruenceGraph.lean"),
            "upstream comparator hash mismatch")
    totals = {"candidates": 0, "structurally_valid": 0, "witnesses": 0, "seed_connectivity": 0, "classes": 0}
    for name, lattice in search["lattices"].items():
        rows = lattice["sizes"]
        require([r["vertices"] for r in rows] == [1, 2, 3, 4], f"incomplete carrier range: {name}")
        for row in rows:
            counts = row["counts"]
            require(row["complete"] is True and counts["candidates"] == row["expected_candidates"],
                    f"incomplete enumeration: {name}")
            require(counts["candidates"] == sum(counts.get(k, 0) for k in
                    ("triangle", "order_separation", "structurally_valid")), f"attrition mismatch: {name}")
            require(counts.get("structurally_valid", 0) == counts.get("witnesses", 0) + counts.get("seed_connectivity", 0),
                    f"connectivity attrition mismatch: {name}")
            for key in totals:
                totals[key] += row["vertex_isomorphism_classes"] if key == "classes" else counts.get(key, 0)
    require(totals == dict(candidates=143685, structurally_valid=1459, witnesses=217, seed_connectivity=1242, classes=22),
            f"release totals changed: {totals}")
    registry = {e["path"]: e["sha256"] for e in search["certificates"]}
    require(len(registry) == len(search["certificates"]) == 7, "certificate registry is incomplete or duplicated")
    for name, digest in registry.items():
        require(sha256(member(folder, name)) == digest, f"certificate hash mismatch: {name}")
        v = read(folder / name.replace(".json", ".verification.json"))
        require(v["passed"] is True and v["certificate_sha256"] == digest, f"failed individual check: {name}")
        require(v["verifier_sha256"] == sha256(root / "verify_witness.py"), "individual verifier source mismatch")
    replay = read(folder / "independent-review-results.json")
    require(replay["all_expected_outcomes"] is True and len(replay["rows"]) == 32, "incomplete independent replay")
    require(all(all(row["matches_primary_record"].values()) for row in replay["rows"]), "a replay comparison failed")
    require(replay["search_record_file_sha256"] == sha256(folder / "search-results.json"), "replay binds a different search")
    require(replay["verifier_sha256"] == sha256(root / "verify_witness.py"), "replay source hash mismatch")
    for filename, key in (("verified-algebras.json", "sha256"), ("minimized-algebras.json", "certificate_sha256")):
        result = read(folder / filename)
        require(result["passed"] is True and result["self_check"]["passed"] is True, f"failed stage: {filename}")
        require(len(result["certificates"]) == 7, f"missing certificates: {filename}")
        require({r["certificate"] for r in result["certificates"]} == set(registry), f"wrong certificates: {filename}")
        for row in result["certificates"]:
            require(row["passed"] is True and row[key] == registry[row["certificate"]], f"failed or unbound algebra: {filename}")
    return totals


def compare(folder, baseline):
    left, right = read(folder / "search-results.json"), read(baseline / "search-results.json")
    for key in ("source", "max_vertices", "isomorphism", "lattices", "certificates"):
        require(stable(left[key]) == stable(right[key]), f"search differs from baseline: {key}")
    for filename in ("verified-algebras.json", "minimized-algebras.json"):
        require(stable(read(folder / filename)["certificates"]) == stable(read(baseline / filename)["certificates"]),
                f"algebra differs from baseline: {filename}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evidence", type=Path, default=ROOT / "evidence")
    parser.add_argument("--compare", type=Path)
    args = parser.parse_args()
    try:
        totals = check(args.evidence.resolve())
        if args.compare:
            compare(args.evidence, args.compare)
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print(f"FAIL: {exc}")
        return 1
    print(json.dumps({"passed": True, "totals": totals, "comparison": bool(args.compare)}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
