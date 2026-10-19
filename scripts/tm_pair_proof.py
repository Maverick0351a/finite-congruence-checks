"""Reproduce or inspect the exact tiny-stay proof and its atlas binding.

run uses Lean and leanchecker; replay checks saved artifacts without Lean.
Saved receipts are reproducibility records, not authenticated attestations.
"""
from __future__ import annotations

import argparse
import copy
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

import run_tm_checks
import tm_atlas

ROOT = Path(__file__).resolve().parents[1]
PROJECT = "lean/tm-pair"
EVIDENCE = "evidence/tm-pair-proof-v1"
CLAIM = EVIDENCE + "/claim.json"
BINDING = PROJECT + "/TinyPairBinding.lean"
THEOREM = "TMOracle.TinyPair.exact_result"
PAIR = "tm-pair:tiny-stay:v1"
DECLARATIONS = [THEOREM, *["TMOracle.TinyPairBinding." + name for name in
                          ("left_definition", "right_definition", "input_definition", "checked_result")]]
LIMITS = [
    "This proves the two specified formal machines on exactly the input []; every integer tape position is covered.",
    "It does not prove that Python, the JSON decoder, the compiler, or the native executable implements those definitions. Their saved agreement tests remain separate.",
    "No general translation equivalence, other input, Busy Beaver optimality, or fluid-flow claim follows.",
    "Offline receipt replay checks saved records and hashes; rerun the Lean command for a fresh elaboration and kernel check.",
]


def require(ok, message):
    if not ok:
        raise ValueError(message)


def encode(value):
    return (json.dumps(value, indent=2, ensure_ascii=False, allow_nan=False) + "\n").encode("utf-8")


def read(path):
    return run_tm_checks.parse_json(Path(path).read_text(encoding="utf-8"))


def digest(path):
    return hashlib.sha256(Path(path).read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def expected_claim(root=ROOT, dataset=None):
    dataset = tm_atlas.load_dataset(root) if dataset is None else dataset
    index, pair = next((i, p) for i, p in enumerate(dataset["pairs"]) if p["id"] == PAIR)
    result = {
        "schema_version": 1, "namespace": "finite-congruence-atlas/tm-formal-pair-v1",
        "id": "tm:tiny-stay:formal-result:v1", "pair_id": PAIR,
        "property": "first_halt_head_and_complete_tape",
        "evidence_status": "lean_theorem_with_recorded_kernel_replay",
        "statement": "Both specified machines first halt after one transition on []; both heads are at zero. The left tape is zero everywhere; the right tape is one at zero and zero everywhere else. The complete tapes differ.",
        "scope": "One exact pair and one exact input; all integer tape positions.",
        "assumptions": ["Machine.run uses the pinned extracted OpenAI family 376 definitions.",
                        "Lean's kernel and the standard axioms reported in the receipt are trusted."],
        "limits": LIMITS,
        "values": {"input": pair["input"], "left": pair["left"]["machine"], "right": pair["right"]["machine"]},
        "conclusion": {"initial_halted": [False, False], "first_halt": [1, 1], "head": [0, 0],
                       "tape": {"quantifier": "every i : Int", "left": [], "right": [[0, 1]], "unlisted_symbol": 0},
                       "tapes_equal": False},
        "theorem": THEOREM,
        "definitions": {"left": "TMOracle.TinyPair.leftMachine", "right": "TMOracle.TinyPair.rightMachine",
                        "input": "TMOracle.TinyPair.blankInput", "run": "OAI.AlternatingNS.Machine.run"},
        "citations": [
            {"path": "lean/tm-pair/TinyPair.lean", "declaration": THEOREM},
            {"path": BINDING, "declarations": DECLARATIONS[1:]},
            {"path": tm_atlas.DATA_PATH, "json_pointer": f"/pairs/{index}", "sha256": digest(root / tm_atlas.DATA_PATH)},
            {"path": "lean/tm/source/manifest.json", "sha256": digest(root / "lean/tm/source/manifest.json")},
        ],
        "separate_execution_evidence": {"claim_id": "tm:tiny-stay:tape:v1", "path": tm_atlas.DATA_PATH,
            "status": "saved_native_execution_cross_checked_with_python",
            "note": "The original snapshot's limits describe its original evidence. This supplemental formal proof does not change that snapshot or its native receipt."},
    }
    result["citations"][0]["sha256"] = digest(root / "lean/tm-pair/TinyPair.lean")
    result["citations"][1]["sha256"] = hashlib.sha256(binding(result).encode()).hexdigest()
    return result


def nat(value):
    require(type(value) is int and value >= 0, "expected natural number")
    return str(value)


def nat_list(values):
    require(type(values) is list, "expected list")
    return "[" + ", ".join(map(nat, values)) + "]"


def machine_literal(machine):
    # Independently type-check the JSON domain before emitting Lean syntax.
    run_tm_checks.from_case({"machine": machine})
    rules = []
    for rule in machine["table"]:
        rules.append("none" if rule is None else "some (" + ", ".join(map(nat, rule)) + ")")
    return "(" + ", ".join([nat(machine[k]) for k in
        ("n_states_minus_one", "n_alphabet_minus_one", "initial_state")] +
        [nat_list(machine["halting_states"]), "[" + ", ".join(rules) + "]"]) + ")"


def target():
    # Deliberately expressed independently of the proof's helper propositions.
    return " ∧\n    ".join([
        "leftExpected.isHalting (leftExpected.run inputExpected 0) = false",
        "rightExpected.isHalting (rightExpected.run inputExpected 0) = false",
        "leftExpected.isHalting (leftExpected.run inputExpected 1) = true",
        "rightExpected.isHalting (rightExpected.run inputExpected 1) = true",
        "(leftExpected.run inputExpected 1).head = 0",
        "(rightExpected.run inputExpected 1).head = 0",
        "(∀ i : Int, (leftExpected.run inputExpected 1).tape i = 0)",
        "(∀ i : Int, (rightExpected.run inputExpected 1).tape i = if i = 0 then 1 else 0)",
        "(leftExpected.run inputExpected 1).tape ≠ (rightExpected.run inputExpected 1).tape"])


def binding(claim):
    name = claim["theorem"]
    require(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)+", name), "invalid theorem identifier")
    values = claim["values"]
    return f"""-- Generated by scripts/tm_pair_proof.py generate; checked without rewriting.
import TinyPair
namespace TMOracle.TinyPairBinding
open OAI.AlternatingNS
private abbrev leftExpected : Machine := {machine_literal(values['left'])}
private abbrev rightExpected : Machine := {machine_literal(values['right'])}
private abbrev inputExpected : List Nat := {nat_list(values['input'])}
theorem left_definition : TMOracle.TinyPair.leftMachine = leftExpected := rfl
theorem right_definition : TMOracle.TinyPair.rightMachine = rightExpected := rfl
theorem input_definition : TMOracle.TinyPair.blankInput = inputExpected := rfl
theorem checked_result :
    {target()} :=
  {name}
end TMOracle.TinyPairBinding
"""


def source_hashes(root=ROOT):
    paths = [p for p in (root / PROJECT).rglob("*") if p.is_file() and ".lake" not in p.parts]
    paths += [root / p for p in (CLAIM, "scripts/tm_pair_proof.py", "scripts/tm_atlas.py", tm_atlas.DATA_PATH,
                               "lean/tm/MachineExtract.lean", "lean/tm/MachineChecks.lean",
                               "lean/tm/lakefile.toml", "lean/tm/lake-manifest.json", "lean/tm/lean-toolchain",
                               "lean/tm/source/manifest.json", "lean/tm/check_source.py")]
    return {p.relative_to(root).as_posix(): digest(p) for p in sorted(set(paths))}


def check_binding(root=ROOT, dataset=None):
    validate_project(root)
    claim = expected_claim(root, dataset)
    # JSON serialization preserves bool/int distinctions; no Python loose equality.
    require(json.dumps(read(root / CLAIM), sort_keys=True) == json.dumps(claim, sort_keys=True), "formal claim differs from exact registered claim")
    require((root / BINDING).read_text(encoding="utf-8") == binding(claim), "generated Lean binding is stale")
    return claim


def validate_project(root):
    manifest = read(root / PROJECT / "lake-manifest.json")
    local = [p for p in manifest["packages"] if p["type"] != "git"]
    require(local == [{"type": "path", "scope": "", "name": "tmTranslationOracle",
                       "manifestFile": "lake-manifest.json", "inherited": False,
                       "dir": "../tm", "configFile": "lakefile.toml"}]
            and (root / PROJECT / local[0]["dir"]).resolve() == (root / "lean/tm").resolve(), "wrong local machine dependency")
    require({k: v for k, v in manifest.items() if k != "packages"} ==
            {"version": "1.2.0", "packagesDir": ".lake/packages", "name": "tmPairReference",
             "lakeDir": ".lake", "fixedToolchain": False}, "unexpected manifest layout")
    upstream = read(root / "lean/tm/lake-manifest.json")
    wanted = copy.deepcopy(upstream["packages"])
    for p in wanted:
        p["inherited"] = True
    require([p for p in manifest["packages"] if p["type"] == "git"] == wanted, "dependencies differ from pinned TM project")
    require((root / PROJECT / "lean-toolchain").read_text(encoding="utf-8") ==
            (root / "lean/tm/lean-toolchain").read_text(encoding="utf-8"), "toolchain differs from pinned TM project")
    config = '''name = "tmPairReference"
version = "0.1.0"
defaultTargets = ["TinyPair", "TinyPairBinding"]

[[require]]
name = "tmTranslationOracle"
path = "../tm"

[[lean_lib]]
name = "TinyPair"

[[lean_lib]]
name = "TinyPairBinding"
'''
    require((root / PROJECT / "lakefile.toml").read_text(encoding="utf-8") == config, "unexpected proof project configuration")


def audit_axioms(log, names=DECLARATIONS):
    reports = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log)
    require(len(reports) == len(names) and sorted(n for n, _ in reports) == sorted(names), "missing or duplicate axiom reports")
    result = {}
    for name, body in reports:
        axioms = [a.strip() for a in body.split(",") if a.strip()]
        require(set(axioms) <= {"propext", "Quot.sound", "Classical.choice"}, f"unapproved axiom in {name}: {axioms}")
        result[name] = axioms
    return result


def controls(claim):
    result = {}
    changed = copy.deepcopy(claim)
    changed["values"]["right"]["table"][1] = [1, 0, 2]
    result["unused-rule"] = binding(changed)
    changed = copy.deepcopy(claim)
    changed["values"]["input"] = [0]
    result["different-input"] = binding(changed)
    changed = copy.deepcopy(claim)
    changed["theorem"] = "TMOracle.Checks.halted_fixed"
    result["unrelated-theorem"] = binding(changed)
    result["changed-tape"] = binding(claim).replace("then 1 else 0)", "then 2 else 0)")
    # Correct but weaker theorems must not discharge the complete target.
    weak = "theorem weak : (TMOracle.TinyPair.rightMachine.run TMOracle.TinyPair.blankInput 1).tape 0 = 1 := by decide\n"
    result["sampled-cell-only"] = binding(claim).replace("theorem checked_result", weak + "theorem checked_result").replace("  " + THEOREM + "\n", "  weak\n")
    weak = "theorem weak : TMOracle.TinyPair.leftMachine.isHalting (TMOracle.TinyPair.leftMachine.run TMOracle.TinyPair.blankInput 1) = true := by decide\n"
    result["halting-without-firstness"] = binding(claim).replace("theorem checked_result", weak + "theorem checked_result").replace("  " + THEOREM + "\n", "  weak\n")
    result["sorry-admission"] = binding(claim).replace("  " + THEOREM + "\n", "  by sorry\n") + "#print axioms TMOracle.TinyPairBinding.checked_result\n"
    return result


def stages():
    return [
        ("source", ["{python}", "lean/tm/check_source.py"], "."),
        ("version", ["lake", "env", "lean", "--version"], PROJECT),
        ("cache", ["lake", "exe", "cache", "get", "Mathlib.Logic.Function.Iterate", "Mathlib.Data.Int.Basic"], PROJECT),
        ("build", ["lake", "build", "TinyPair", "TinyPairBinding"], PROJECT),
        ("axioms", ["lake", "env", "lean", "{out}/Audit.lean"], PROJECT),
        ("kernel", ["lake", "env", "leanchecker", "MachineExtract", "MachineChecks", "TinyPair", "TinyPairBinding"], PROJECT),
    ]


def plan(claim):
    return stages() + [(n, ["lake", "env", "lean", "{out}/" + n + ".lean"], PROJECT) for n in controls(claim)]


def dependencies(root):
    result = {}
    manifest = read(root / PROJECT / "lake-manifest.json")
    for package in manifest["packages"]:
        if package["type"] != "git":
            continue
        path = root / PROJECT / ".lake/packages" / package["name"]
        revision = subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()
        dirty = subprocess.check_output(["git", "-C", str(path), "status", "--porcelain", "--untracked-files=all"], text=True)
        require(revision == package["rev"] and not dirty, f"dependency is not clean at its pinned revision: {package['name']}")
        result[package["name"]] = {"url": package["url"], "revision": revision, "working_tree_clean": True}
    return result


def replay(out, root=ROOT, dataset=None):
    claim = check_binding(root, dataset)
    receipt = read(out / "summary.json")
    require(type(receipt["schema_version"]) is int and receipt["schema_version"] == 1 and receipt["status"] == "passed", "proof run did not pass")
    require(receipt["limits"] == LIMITS and receipt["hash_encoding"] == "SHA-256 with CRLF normalized to LF", "receipt interpretation differs")
    require(json.dumps(receipt["claim"], sort_keys=True) == json.dumps(claim, sort_keys=True), "receipt claim differs")
    require(receipt["source_hashes"] == source_hashes(root), "proof source changed since verification")
    expected_names = [name for name, _, _ in stages()] + list(controls(claim))
    require([s["name"] for s in receipt["stages"]] == expected_names, "missing proof stages")
    for actual, (name, command, cwd) in zip(receipt["stages"], plan(claim)):
        require(actual["command"] == command and actual["cwd"] == cwd, f"wrong command: {name}")
    pinned = {p["name"]: {"url": p["url"], "revision": p["rev"], "working_tree_clean": True}
              for p in read(root / PROJECT / "lake-manifest.json")["packages"] if p["type"] == "git"}
    require(receipt["dependencies"] == pinned, "dependency provenance differs")
    for name, sha in receipt["artifacts"].items():
        require(Path(name).name == name and digest(out / name) == sha, f"artifact mismatch: {name}")
    required = {"Audit.lean", *[name + ".log" for name in expected_names],
                *[name + ".lean" for name in controls(claim)]}
    require(set(receipt["artifacts"]) == required, "missing proof artifacts")
    for stage in receipt["stages"]:
        name = stage["name"]
        code = stage["exit_code"]
        require(type(code) is int, "invalid exit code")
        log = (out / (name + ".log")).read_text(encoding="utf-8")
        if name in controls(claim) and name != "sorry-admission":
            require(code != 0 and "error:" in log, f"mutation not rejected: {name}")
        else:
            require(code == 0, f"stage failed: {name}")
    require("Lean (version 4.34.1," in (out / "version.log").read_text(encoding="utf-8"), "wrong Lean version")
    require(receipt["axioms"] == audit_axioms((out / "axioms.log").read_text(encoding="utf-8")), "axiom audit differs")
    require((out / "Audit.lean").read_text(encoding="utf-8") == audit_source(), "audit source differs")
    for name, source in controls(claim).items():
        require((out / (name + ".lean")).read_text(encoding="utf-8") == source, f"control source differs: {name}")
    try:
        audit_axioms((out / "sorry-admission.log").read_text(encoding="utf-8"), [DECLARATIONS[-1]])
    except ValueError:
        require("sorryAx" in (out / "sorry-admission.log").read_text(encoding="utf-8"), "missing admission control evidence")
    else:
        raise ValueError("admitted proof was accepted")
    return receipt


def audit_source():
    return "import TinyPairBinding\n" + "".join("#print axioms " + n + "\n" for n in DECLARATIONS)


def run(out, root=ROOT):
    require(not out.exists(), "choose a new output directory; existing evidence is never overwritten")
    claim = check_binding(root)
    before = source_hashes(root)
    out.mkdir(parents=True)
    (out / "Audit.lean").write_bytes(audit_source().encode())
    mutations = controls(claim)
    for name, source in mutations.items():
        (out / (name + ".lean")).write_bytes(source.encode())
    receipt = {"schema_version": 1, "status": "running", "claim": claim,
               "hash_encoding": "SHA-256 with CRLF normalized to LF", "source_hashes": before,
               "stages": [], "artifacts": {}, "axioms": {},
               "limits": LIMITS, "started_utc": datetime.now(timezone.utc).isoformat(), "dependencies": {}}
    commands = plan(claim)
    try:
        for name, command, cwd in commands:
            actual_command = [arg.replace("{out}", str(out)).replace("{python}", sys.executable) for arg in command]
            print(f"Checking {name}", flush=True)
            started = time.perf_counter()
            proc = subprocess.run(actual_command, cwd=root / cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                  timeout=600, env={**os.environ, "MATHLIB_NO_CACHE_ON_UPDATE": "1"})
            (out / (name + ".log")).write_bytes(proc.stdout)
            receipt["stages"].append({"name": name, "command": command, "cwd": cwd, "exit_code": proc.returncode,
                                      "duration_seconds": round(time.perf_counter() - started, 3)})
            if name not in mutations or name == "sorry-admission":
                require(proc.returncode == 0, f"{name} failed; see {out / (name + '.log')}")
            else:
                require(proc.returncode != 0 and b"error:" in proc.stdout, f"{name} was not rejected")
            if name == "cache":
                receipt["dependencies"] = dependencies(root)
        receipt["axioms"] = audit_axioms((out / "axioms.log").read_text(encoding="utf-8"))
        require(before == source_hashes(root), "source changed while verification was running")
        require(receipt["dependencies"] == dependencies(root), "dependencies changed while verifying")
        receipt["finished_utc"] = datetime.now(timezone.utc).isoformat()
        receipt["artifacts"] = {p.name: digest(p) for p in sorted(out.iterdir()) if p.is_file()}
        receipt["status"] = "passed"
        (out / "summary.json").write_bytes(encode(receipt))
        replay(out, root)
    except BaseException:
        receipt["status"] = "failed"
        (out / "summary.json").write_bytes(encode(receipt))
        raise
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["generate", "run", "replay"])
    parser.add_argument("--out", type=Path, default=ROOT / EVIDENCE)
    args = parser.parse_args()
    if args.command == "run" and args.out == ROOT / EVIDENCE:
        parser.error("run requires --out NEW_DIRECTORY; the saved evidence is never overwritten")
    if args.command == "generate":
        claim = expected_claim()
        (ROOT / CLAIM).parent.mkdir(parents=True, exist_ok=True)
        (ROOT / CLAIM).write_bytes(encode(claim))
        (ROOT / BINDING).write_bytes(binding(claim).encode())
        print("Generated exact claim and Lean binding; proof still requires run.")
    else:
        receipt = run(args.out.resolve()) if args.command == "run" else replay(args.out.resolve())
        print(f"PASS: {receipt['claim']['id']}; {len(receipt['stages'])} stages; mode={args.command}")


if __name__ == "__main__":
    main()
