"""Compare complete finite-support Python and pinned Lean configurations.

The Lean executable is a separately built oracle, not a formal proof of this
Python port. Run with run --out NEW_DIR (the pinned Lake toolchain is required).
Use replay --out EVIDENCE_DIR to validate retained inputs and outputs offline.
"""
from __future__ import annotations

import argparse
import copy
from datetime import datetime, timezone
import gzip
import hashlib
import json
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys

import tm_cases
import tm_port as port

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def dump(path, value):
    Path(path).write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n",
                          encoding="utf-8", newline="\n")


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate key: {key}")
        result[key] = value
    return result


def parse_json(text):
    return json.loads(text, object_pairs_hook=unique_object,
                      parse_constant=lambda x: (_ for _ in ()).throw(ValueError(x)))


def from_case(case):
    m = case["machine"]
    return port.Machine(m["n_states_minus_one"], m["n_alphabet_minus_one"],
                        m["initial_state"], m["halting_states"],
                        [None if r is None else port.Rule(*r) for r in m["table"]])


def expected(case):
    m = from_case(case)
    cfg = port.run(m, case["input"], case["steps"])
    return {"id": case["id"], "steps": case["steps"], "state": cfg.state,
            "head": cfg.head, "halted": port.is_halting(m, cfg),
            "tape": [[k, v] for k, v in sorted(cfg.written().items())]}


def exact_record(record):
    if type(record) is not dict or set(record) != {"id", "steps", "state", "head", "halted", "tape"}:
        return False
    if type(record["id"]) is not str or type(record["halted"]) is not bool:
        return False
    if any(type(record[k]) is not int for k in ("steps", "state", "head")):
        return False
    if record["steps"] < 0 or record["state"] < 0 or type(record["tape"]) is not list:
        return False
    previous = None
    for pair in record["tape"]:
        if type(pair) is not list or len(pair) != 2 or any(type(x) is not int for x in pair):
            return False
        if pair[1] <= 0 or (previous is not None and pair[0] <= previous):
            return False
        previous = pair[0]
    return True


def compare(cases, raw):
    wanted = {case["id"]: expected(case) for case in cases}
    if len(wanted) != len(cases):
        raise ValueError("duplicate case IDs")
    seen = set()
    errors = []
    for lineno, line in enumerate(raw.splitlines(), 1):
        try:
            rec = parse_json(line)
        except ValueError as exc:
            errors.append({"line": lineno, "kind": "invalid-json", "error": str(exc)})
            continue
        if not exact_record(rec):
            errors.append({"line": lineno, "kind": "invalid-record", "actual": rec})
            continue
        name = rec["id"]
        if name in seen or name not in wanted:
            errors.append({"line": lineno, "kind": "duplicate-or-unknown-id", "id": name})
            continue
        seen.add(name)
        if rec != wanted[name]:
            errors.append({"line": lineno, "kind": "configuration-mismatch", "id": name,
                           "expected": wanted[name], "actual": rec})
    for missing in sorted(set(wanted) - seen):
        errors.append({"kind": "missing-record", "id": missing})
    return {"passed": not errors, "expected_records": len(wanted),
            "seen_records": len(seen), "disagreements": errors}


def source_hashes():
    paths = [ROOT / "scripts" / name for name in
             ("tm_port.py", "tm_cases.py", "run_tm_checks.py", "test_tm_port.py", "test_tm_checks.py")]
    paths += [p for p in (ROOT / "lean/tm").rglob("*") if p.is_file()
              and not any(x in p.parts for x in (".lake", ".work", "evidence", "__pycache__"))
              and (p.suffix in (".lean", ".py", ".toml", ".json")
                   or p.name in ("lean-toolchain", "LICENSE"))]
    return {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(paths)}


def check_source():
    subprocess.run([sys.executable, str(ROOT / "lean/tm/check_source.py")],
                   check=True, capture_output=True, text=True, timeout=30)


def helper_checks(cases):
    # Independent helper obligation: reported n and config agree with run(n),
    # and no earlier time was halting. This checks bounded-search bookkeeping.
    for case in cases:
        m = from_case(case)
        ok, n, cfg = port.halts(m, case["input"], case["steps"])
        if cfg != port.run(m, case["input"], n) or ok != port.is_halting(m, cfg):
            raise ValueError(f"bounded search inconsistent: {case['id']}")
        if n > case["steps"] or (not ok and n != case["steps"]):
            raise ValueError(f"bounded search count: {case['id']}")
        if any(port.is_halting(m, port.run(m, case["input"], k)) for k in range(n)):
            raise ValueError(f"bounded search not earliest: {case['id']}")


def rejection_controls(cases, raw):
    records = [parse_json(line) for line in raw.splitlines()]
    controls = {}
    for field, replacement in (("state", records[0]["state"] + 1),
                               ("head", records[0]["head"] + 1),
                               ("tape", [[0, 9]]), ("steps", records[0]["steps"] + 1)):
        modified = dict(records[0], **{field: replacement})
        bad = "\n".join(json.dumps(x) for x in [modified, *records[1:]])
        controls["altered-" + field] = not compare(cases, bad)["passed"]
    controls["missing-record"] = not compare(cases, "\n".join(raw.splitlines()[1:]))["passed"]
    controls["duplicate-record"] = not compare(cases, "\n".join([*raw.splitlines(), json.dumps(records[0])]))["passed"]
    controls["malformed-json"] = not compare(cases, "\n".join([*raw.splitlines(), "{"]))["passed"]
    return controls


BUILD_STAGES = (
    ("lean-version", ["env", "lean", "--version"]),
    ("build", ["build", "tmOracle", "MachineChecks"]),
    ("axioms", ["env", "lean", "MachineChecks.lean"]),
    ("kernel", ["env", "leanchecker", "MachineExtract", "MachineChecks"]),
)
BASE_ARTIFACTS = ("inputs.jsonl", "lean.jsonl", "stderr.log", "comparison.json", "binary.gz",
                  "input-rejections.json")


def validate_build_logs(out):
    version = (ROOT / "lean/tm/lean-toolchain").read_text().strip().split(":v")[-1]
    if not re.search(r"Lean \(version " + re.escape(version) + r"(?:,|\))",
                     (out / "build/lean-version.log").read_text(encoding="utf-8")):
        raise ValueError("compiled Lean version differs from pinned toolchain")
    axioms = (out / "build/axioms.log").read_text(encoding="utf-8")
    reports = re.findall(r"'TMOracle.Checks\.([^']+)' depends on axioms: \[([^\]]*)\]", axioms)
    names = {"halted_fixed", "missing_instruction", "instruction_step", "instruction_writes",
             "instruction_preserves_other_cells"}
    if len(reports) != len(names) or {name for name, _ in reports} != names:
        raise ValueError("missing source-lemma axiom reports")
    for name, body in reports:
        if not set(body.replace(" ", "").split(",")) <= {"", "propext", "Quot.sound", "Classical.choice"}:
            raise ValueError(f"unexpected source-lemma axiom: {name}")


def input_rejection_cases():
    base = {"id": "invalid-domain", "machine": tm_cases.machine(
        1, 2, 0, [], [[0, 1, 2], None]), "input": [], "steps": 1}
    cases = []
    paths = [("machine", key) for key in
             ("n_states_minus_one", "n_alphabet_minus_one", "initial_state")]
    paths += [("machine", "halting_states", 0), ("input", 0), ("steps",)]
    paths += [("machine", "table", 0, i) for i in range(3)]
    for index, path in enumerate(paths):
        for label, value in (("negative", -1), ("boolean", True), ("decimal", 1.0)):
            changed = copy.deepcopy(base)
            changed["machine"]["halting_states"] = [0]
            changed["input"] = [0]
            parent = changed
            for key in path[:-1]:
                parent = parent[key]
            parent[path[-1]] = value
            cases.append({"id": f"{index}-{label}", "input_json": json.dumps(changed)})
    for label, table in (("move-three", [[0, 1, 3]]), ("short-rule", [[0, 1]]),
                          ("long-rule", [[0, 1, 2, 0]]), ("object-rule", [{}]),
                          ("object-table", {})):
        changed = copy.deepcopy(base)
        changed["machine"]["table"] = table
        cases.append({"id": label, "input_json": json.dumps(changed)})
    cases.append({"id": "exponent", "input_json": json.dumps(base).replace('"steps": 1', '"steps": 1e0')})
    cases.append({"id": "malformed-json", "input_json": "{"})
    return cases


def validate_input_rejections(probes):
    expected_cases = input_rejection_cases()
    if len(probes) != len(expected_cases):
        raise ValueError("missing native input-rejection probes")
    for expected_case, probe in zip(expected_cases, probes):
        if (set(probe) != {"id", "input_json", "exit_code", "stdout", "stderr"} or
                any(probe[k] != v for k, v in expected_case.items()) or
                type(probe["exit_code"]) is not int or probe["exit_code"] != 1 or
                probe["stdout"] != "" or not isinstance(probe["stderr"], str) or
                not probe["stderr"].startswith("tmOracle: line 1: ")):
            raise ValueError(f"native input rejection failed: {expected_case['id']}")


def run(out, lake):
    check_source()
    if out.exists() and any(out.iterdir()):
        raise ValueError("choose a new or empty output directory")
    out.mkdir(parents=True, exist_ok=True)
    resolved_lake = shutil.which(lake)
    if not resolved_lake:
        raise ValueError("Lake is not on PATH; use the toolchain in lean/tm/lean-toolchain")
    cases = tm_cases.comparison_cases()
    data = "".join(json.dumps(c, separators=(",", ":")) + "\n" for c in cases)
    (out / "inputs.jsonl").write_text(data, encoding="utf-8", newline="\n")
    sources = source_hashes()
    receipt = {"format": "tm-differential-v1", "passed": False,
               "started_utc": datetime.now(timezone.utc).isoformat(),
               "scope": "bounded configuration agreement, not general Python/Lean equivalence",
               "source_sha256": sources, "python": sys.version, "platform": platform.platform(),
               "toolchain": (ROOT / "lean/tm/lean-toolchain").read_text().strip(),
               "build_project": "lean/tm", "build_commands": [],
               "resolved_lake": resolved_lake}
    dump(out / "summary.json", receipt)
    (out / "build").mkdir()
    for name, arguments in BUILD_STAGES:
        command = [resolved_lake, *arguments]
        completed = subprocess.run(command, cwd=ROOT / "lean/tm", capture_output=True,
                                   text=True, encoding="utf-8", timeout=600, check=False)
        log = "build/" + name + ".log"
        (out / log).write_text(completed.stdout + completed.stderr, encoding="utf-8", newline="\n")
        receipt["build_commands"].append({"name": name, "argv": ["lake", *arguments],
                                           "exit_code": completed.returncode, "log": log})
        dump(out / "summary.json", receipt)
        if completed.returncode != 0:
            raise ValueError(f"Lean {name} failed; see {out / log}")
    validate_build_logs(out)
    binary_relative = "lean/tm/.lake/build/bin/tmOracle" + (".exe" if sys.platform == "win32" else "")
    binary = ROOT / binary_relative
    receipt.update(binary_sha256=sha(binary), command=[binary_relative])
    with binary.open("rb") as src, (out / "binary.gz").open("wb") as dst:
        with gzip.GzipFile(filename="", mode="wb", fileobj=dst, mtime=0) as compressed:
            shutil.copyfileobj(src, compressed)
    result = subprocess.run([str(binary)], input=data, text=True, encoding="utf-8",
                            capture_output=True, timeout=180, check=False)
    (out / "lean.jsonl").write_text(result.stdout, encoding="utf-8", newline="\n")
    (out / "stderr.log").write_text(result.stderr, encoding="utf-8", newline="\n")
    comparison = compare(cases, result.stdout)
    dump(out / "comparison.json", comparison)
    receipt.update(exit_code=result.returncode, comparison=comparison)
    probes = []
    for case in input_rejection_cases():
        rejected = subprocess.run([str(binary)], input=case["input_json"] + "\n", text=True,
                                  encoding="utf-8", capture_output=True, timeout=30, check=False)
        probes.append(dict(case, exit_code=rejected.returncode,
                           stdout=rejected.stdout, stderr=rejected.stderr))
    dump(out / "input-rejections.json", probes)
    validate_input_rejections(probes)
    receipt["input_rejection_cases"] = len(probes)
    if result.returncode == 0 and comparison["passed"]:
        helper_checks(cases)
        controls = rejection_controls(cases, result.stdout)
        receipt["rejection_controls"] = controls
        receipt["helper_cases"] = len(cases)
        receipt["passed"] = all(controls.values())
    receipt["sources_unchanged"] = source_hashes() == sources
    receipt["passed"] &= receipt["sources_unchanged"] and sha(binary) == receipt["binary_sha256"]
    receipt["artifacts"] = {name: sha(out / name) for name in
                            (*BASE_ARTIFACTS, *("build/" + name + ".log" for name, _ in BUILD_STAGES))}
    receipt["finished_utc"] = datetime.now(timezone.utc).isoformat()
    dump(out / "summary.json", receipt)
    print(json.dumps({"passed": receipt["passed"], "records": len(cases), "out": str(out)}))
    return receipt["passed"]


def replay(out):
    check_source()
    receipt = parse_json((out / "summary.json").read_text(encoding="utf-8"))
    if receipt["source_sha256"] != source_hashes():
        raise ValueError("recorded sources differ from current sources")
    artifact_names = {*BASE_ARTIFACTS, *("build/" + name + ".log" for name, _ in BUILD_STAGES)}
    if set(receipt["artifacts"]) != artifact_names:
        raise ValueError("incomplete artifact manifest")
    for name, digest in receipt["artifacts"].items():
        if sha(out / name) != digest:
            raise ValueError(f"artifact mismatch: {name}")
    expected_build = [{"name": name, "argv": ["lake", *args], "exit_code": 0,
                       "log": "build/" + name + ".log"} for name, args in BUILD_STAGES]
    if (receipt["format"] != "tm-differential-v1" or receipt["build_commands"] != expected_build or
            receipt["build_project"] != "lean/tm" or receipt["toolchain"] !=
            (ROOT / "lean/tm/lean-toolchain").read_text().strip() or
            receipt["command"] not in (["lean/tm/.lake/build/bin/tmOracle"],
                                      ["lean/tm/.lake/build/bin/tmOracle.exe"])):
        raise ValueError("build provenance mismatch")
    with gzip.open(out / "binary.gz", "rb") as stream:
        digest = hashlib.sha256()
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    if digest.hexdigest() != receipt["binary_sha256"]:
        raise ValueError("binary identity mismatch")
    validate_build_logs(out)
    probes = parse_json((out / "input-rejections.json").read_text(encoding="utf-8"))
    validate_input_rejections(probes)
    if receipt["input_rejection_cases"] != len(probes):
        raise ValueError("input-rejection count mismatch")
    cases = tm_cases.comparison_cases()
    saved = [parse_json(line) for line in (out / "inputs.jsonl").read_text(encoding="utf-8").splitlines()]
    if json.dumps(saved, sort_keys=True) != json.dumps(cases, sort_keys=True):
        raise ValueError("recorded inputs differ from frozen case generator")
    raw = (out / "lean.jsonl").read_text(encoding="utf-8")
    comparison = compare(cases, raw)
    controls = rejection_controls(cases, raw)
    helper_checks(cases)
    if (not comparison["passed"] or comparison != receipt["comparison"] or
            comparison != parse_json((out / "comparison.json").read_text(encoding="utf-8")) or
            controls != receipt["rejection_controls"] or not all(controls.values()) or
            receipt["exit_code"] != 0 or receipt["passed"] is not True or
            receipt["sources_unchanged"] is not True or receipt["helper_cases"] != len(cases)):
        raise ValueError("recorded outcome does not replay")
    print(f"Replayed {len(cases)} configurations and bounded helper checks; saved execution evidence, not a fresh Lean run.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("run", "replay"))
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--lake", default="lake", help="Lake executable; binary path is derived from its build")
    args = parser.parse_args()
    try:
        if args.action == "replay":
            replay(args.out)
        else:
            if not run(args.out, args.lake):
                raise SystemExit(1)
    except (ValueError, OSError, KeyError, subprocess.SubprocessError) as exc:
        parser.exit(1, f"TM comparison failed: {exc}\n")


if __name__ == "__main__":
    main()
