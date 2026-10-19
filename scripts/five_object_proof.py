"""Reproduce the exact five-object minimum proof and its atlas binding.

generate saves the claim and typed Lean binding; run invokes Lean and kernel
replay; replay checks a saved receipt without running Lean. No model is used.
"""
from __future__ import annotations

import argparse
import copy
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

import check_five_object as finite

ROOT = Path(__file__).resolve().parents[1]
PROJECT = "lean/five_object"
EVIDENCE = "evidence/five-object-v1"
CLAIM_PATH = EVIDENCE + "/claim.json"
RECEIPT = EVIDENCE + "/proof"
BINDING = PROJECT + "/FiveObjectBinding.lean"
CLAIM_ID = finite.CLAIM_ID
PREFIX = "FiniteCongruenceChecks.FiveObject."
BPREFIX = PREFIX + "Binding."
MODULES = ["FiveObjectBase", "FiveObjectData", "FiveObjectClassification", "FiveObjectObstructions",
           "FiveObjectMinimum", "FiveObjectBinding"]
BINDING_NAMES = ["a_operations", "b_operations", "a_groupings", "b_groupings", "mapping_exact",
                 "conclusion_counts", "checked_a", "checked_b", "checked_a_lower", "checked_b_lower",
                 "checked_a_distinct", "checked_b_distinct", "checked_order", "checked_bijection"]
DECLARATIONS = [PREFIX + name for name in (
    "table_complete", "relation_complete", "A.all_relations", "B.all_relations",
    "A.order_exact", "B.order_exact", "A.theta_injective", "B.theta_injective",
    "A.no_two_operations", "B.no_one_operation", "A.no_small_signature", "B.no_small_signature",
    "same_order", "correspondence_inverse", "le_is_partial_order")]
DECLARATIONS += [BPREFIX + name for name in BINDING_NAMES]
ALLOWED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
LIMITS = [
    "Minima concern each exact relation family on the fixed five-object carrier and total unary operations.",
    "The order correspondence matches groupings; it is not asserted to relabel the five objects or the rules.",
    "No minimum over all embeddings, larger carriers, or higher-arity operations is established.",
    "The Python enumeration and exporter are not formally verified implementations. Their checks are separate from the Lean proof.",
    "Offline receipt replay checks recorded bindings and hashes; it is not a new kernel check or an authenticated attestation.",
    "This formalizes an existing saved example. No mathematical novelty, complete five-object census, or agent-performance gain is claimed."
]
PREDICATE = "For every relation on Fin 5, it is an equivalence relation preserved by the displayed rules iff it equals one of the eight displayed equivalence relations; the exact families have the stated minimum unary signature sizes and isomorphic inclusion orders."
require, encode, read, digest = finite.require, finite.encode, finite.read, finite.digest


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False, allow_nan=False)


def expected_claim(root=ROOT):
    inputs = read(root / finite.INPUT)
    require(canonical(inputs) == canonical(finite.expected_input()), "registered inputs differ")
    claim = {
        "schema_version": 1, "namespace": "finite-congruence-atlas/five-object-v1",
        "id": CLAIM_ID, "kind": "exact_family_minima",
        "evidence_status": "lean_proof_with_recorded_kernel_replay",
        "statement": "These two five-object constructions each have eight congruences with isomorphic inclusion orders, but their exact families require respectively three and two unary rules.",
        "scope": inputs["scope"], "assumptions": inputs["assumptions"] + [
            "Lean's kernel and only the standard axioms reported by the receipt are trusted."],
        "limits": LIMITS, "values": copy.deepcopy(inputs["values"]),
        "conclusion": {"predicate": PREDICATE, "distinct_groupings_A": 8, "distinct_groupings_B": 8,
                       "minimum_A": 3, "minimum_B": 2, "inclusion_order_isomorphic": True},
        "theorems": {"classification_A": PREFIX + "A.all_relations", "classification_B": PREFIX + "B.all_relations",
                     "lower_A": PREFIX + "A.no_small_signature", "lower_B": PREFIX + "B.no_small_signature",
                     "order": PREFIX + "same_order"},
        "applicable_lemmas": [{"theorem": PREFIX + name, "role": role} for name, role in (
            ("A.all_relations", "complete exact A family"), ("B.all_relations", "complete exact B family"),
            ("A.no_small_signature", "exclude any signature of at most two rules"),
            ("B.no_small_signature", "exclude any signature of at most one rule"),
            ("A.theta_injective", "eight distinct A relations"), ("B.theta_injective", "eight distinct B relations"),
            ("same_order", "inclusion equivalence"), ("correspondence_inverse", "bijective grouping correspondence"))],
        "citations": [{"path": p, "sha256": digest(root / p)} for p in (
            finite.INPUT, PROJECT + "/FiveObjectBase.lean", PROJECT + "/FiveObjectData.lean", PROJECT + "/FiveObjectClassification.lean",
            PROJECT + "/FiveObjectObstructions.lean", PROJECT + "/FiveObjectMinimum.lean")],
        "upstream_context": {
            "family": "206", "revision": "1581d4cbdd69a0faf34b2089614fe2a814316a6a",
            "scope_url": "https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/docs/206.md",
            "role": "Research context for finite congruence representation; this new proof does not import or prove the full upstream theorem."
        },
    }
    claim["citations"].append({"path": BINDING, "sha256": hashlib.sha256(binding(claim).encode()).hexdigest()})
    return claim


def _nat(value, maximum):
    require(type(value) is int and 0 <= value <= maximum, "invalid finite natural")
    return str(value)


def _table(values):
    require(type(values) is list and len(values) == 5, "invalid five-object table")
    return "(" + ", ".join(_nat(x, 4) for x in values) + ")"


def _cases(values, render):
    require(type(values) is list and len(values) > 0, "invalid finite cases")
    return "match i.val with " + " ".join(f"| {i if i < len(values)-1 else '_'} => {render(v)}"
                                            for i, v in enumerate(values))


def binding(claim):
    """Render explicit mathematical types, with safe identifiers and finite data."""
    names, values, conclusion = claim["theorems"], claim["values"], claim["conclusion"]
    for name in names.values():
        require(type(name) is str and re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)+", name),
                "invalid theorem identifier")
    require(conclusion["predicate"] == PREDICATE, "unsupported predicate meaning")
    require(type(values["carrier"]) is list and canonical(values["carrier"]) == "[0,1,2,3,4]", "wrong carrier")
    mA, mB = (_nat(conclusion[k], 10) for k in ("minimum_A", "minimum_B"))
    nA, nB = (_nat(conclusion[k], 52) for k in ("distinct_groupings_A", "distinct_groupings_B"))
    require(type(conclusion["inclusion_order_isomorphic"]) is bool, "invalid order conclusion")
    require(type(values["A_to_B"]) is list and len(values["A_to_B"]) == 8, "invalid grouping map")
    pieces = ["-- Generated by scripts/five_object_proof.py generate; checked without rewriting.\n",
              "import FiveObjectMinimum\nnamespace FiniteCongruenceChecks.FiveObject.Binding\n"]
    for key, short, count in (("A", "a", 3), ("B", "b", 2)):
        ops, groups = values[key]["operations"], values[key]["groupings"]
        require(type(ops) is list and len(ops) == count, "wrong rule count")
        require(type(groups) is list and len(groups) == 8, "wrong grouping count")
        require(type(values[key]["minimum_unary_operations"]) is int and
                values[key]["minimum_unary_operations"] == conclusion["minimum_" + key], "minimum fields disagree")
        pieces += [f"private def {short}Ops (i : Fin {count}) : V → V := {_cases(ops, lambda v: 'table ' + _table(v))}\n",
                   f"private def {short}Theta (i : Fin 8) : Rel := {_cases(groups, lambda v: 'graph ' + _table(v))}\n",
                   f"theorem {short}_operations : ∀ i x, {key}.ops i x = {short}Ops i x := by decide\n",
                   f"theorem {short}_groupings : ∀ i x y, {key}.theta i x y = {short}Theta i x y := by decide\n",
                   f"private theorem {short}_ops_eq : {key}.ops = {short}Ops := funext fun i => funext ({short}_operations i)\n",
                   f"private theorem {short}_theta_eq : {key}.theta = {short}Theta := funext fun i => funext fun x => funext ({short}_groupings i x)\n",
                   f"theorem checked_{short} (r : V → V → Prop) : IsPropCongruence {short}Ops r ↔ ∃ i : Fin 8, ∀ x y, r x y ↔ {short}Theta i x y = true := by\n",
                   f"  rw [← {short}_ops_eq, ← {short}_theta_eq]\n  exact {names['classification_' + key]} r\n",
                   f"theorem checked_{short}_lower {{k : Nat}} (ops : Fin k → V → V) (hk : k < {conclusion['minimum_' + key]}) : ¬ Realizes ops {short}Theta := by\n",
                   f"  rw [← {short}_theta_eq]\n  exact {names['lower_' + key]} ops (by omega)\n",
                   f"theorem checked_{short}_distinct (i j : Fin 8) : Same ({short}Theta i) ({short}Theta j) → i = j := by\n",
                   f"  rw [← {short}_theta_eq]\n  exact {key}.theta_injective i j\n"]
    pieces += [f"private def groupMap (i : Fin 8) : Fin 8 := {_cases(values['A_to_B'], lambda v: _nat(v, 7))}\n",
               "theorem mapping_exact : ∀ i, correspondence i = groupMap i := by decide\n",
               "private theorem map_eq : correspondence = groupMap := funext mapping_exact\n",
               f"theorem conclusion_counts : (8 : Nat) = {nA} ∧ (8 : Nat) = {nB} ∧ (3 : Nat) = {mA} ∧ (2 : Nat) = {mB} ∧ ({str(conclusion['inclusion_order_isomorphic']).lower()} : Bool) = true := by decide\n",
               "theorem checked_order (i j : Fin 8) : Included (aTheta i) (aTheta j) ↔ Included (bTheta (groupMap i)) (bTheta (groupMap j)) := by\n",
               f"  rw [← a_theta_eq, ← b_theta_eq, ← map_eq]\n  exact {names['order']} i j\n",
               "theorem checked_bijection : (∀ i, inverseCorrespondence (groupMap i) = i) ∧ (∀ i, groupMap (inverseCorrespondence i) = i) := by\n",
               "  rw [← map_eq]\n  exact correspondence_inverse\n",
               "end FiniteCongruenceChecks.FiveObject.Binding\n"]
    return "".join(pieces)


def check_binding(root=ROOT):
    validate_project(root)
    claim = expected_claim(root)
    require(canonical(read(root / CLAIM_PATH)) == canonical(claim), "saved claim differs from exact registration")
    require((root / BINDING).read_text(encoding="utf-8") == binding(claim), "stale or altered Lean binding")
    return claim


def validate_project(root=ROOT):
    project = root / PROJECT
    require(not (project / "lakefile.lean").exists(), "unexpected executable Lake configuration")
    require((project / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.34.1", "wrong pinned toolchain")
    expected = ('name = "fiveObjectMinimum"\nversion = "0.1.0"\nmoreLeanArgs = ["-j1"]\n'
                'defaultTargets = ["FiveObjectMinimum", "FiveObjectBinding"]\n\n' +
                "\n".join('[[lean_lib]]\nname = "' + module + '"\n' for module in MODULES))
    require((project / "lakefile.toml").read_text().strip() == expected.strip(), "unreviewed Lake configuration")
    manifest = read(project / "lake-manifest.json")
    expected_manifest = {"version": "1.2.0", "packagesDir": ".lake/packages", "packages": [],
                         "name": "fiveObjectMinimum", "lakeDir": ".lake", "fixedToolchain": False}
    require(canonical(manifest) == canonical(expected_manifest), "unexpected dependencies or manifest")


def source_hashes(root=ROOT):
    paths = ["scripts/five_object_proof.py", finite.SOURCE, finite.INPUT, CLAIM_PATH,
             PROJECT + "/lean-toolchain", PROJECT + "/lakefile.toml", PROJECT + "/lake-manifest.json",
             PROJECT + "/generate_certificates.py"]
    paths += [PROJECT + "/" + name + ".lean" for name in MODULES]
    return {path: digest(root / path) for path in paths}


def controls(claim):
    changed = {}
    for name, mutate in (
        ("changed-operation", lambda c: c["values"]["A"]["operations"][0].__setitem__(0, 1)),
        ("changed-grouping", lambda c: c["values"]["A"]["groupings"][1].__setitem__(1, 1)),
        ("changed-map", lambda c: c["values"].__setitem__("A_to_B", list(range(8)))),
        ("wrong-count", lambda c: c["conclusion"].__setitem__("distinct_groupings_A", 7)),
        ("wrong-order", lambda c: c["conclusion"].__setitem__("inclusion_order_isomorphic", False)),
        ("unrelated-classification", lambda c: c["theorems"].__setitem__("classification_A", PREFIX + "B.all_relations")),
        ("unrelated-lower-bound", lambda c: c["theorems"].__setitem__("lower_A", PREFIX + "B.no_small_signature")),
    ):
        candidate = copy.deepcopy(claim)
        mutate(candidate)
        changed[name] = binding(candidate)
    candidate = copy.deepcopy(claim)
    candidate["conclusion"]["minimum_A"] = 4
    candidate["values"]["A"]["minimum_unary_operations"] = 4
    changed["wrong-minimum"] = binding(candidate)
    return changed


def audit_source():
    return "import FiveObjectBinding\n" + "".join("#print axioms " + n + "\n" for n in DECLARATIONS)


def audit_axioms(log):
    reports = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log)
    require(len(reports) == len(DECLARATIONS) and sorted(n for n, _ in reports) == sorted(DECLARATIONS),
            "missing or duplicate axiom report")
    result = {}
    for name, raw in reports:
        axioms = sorted(x.strip() for x in raw.split(",") if x.strip())
        require(set(axioms) <= ALLOWED_AXIOMS, "forbidden axiom for " + name + ": " + raw)
        result[name] = axioms
    return result


def plan(claim):
    return [("version", ["lake", "env", "lean", "--version"]),
            ("build", ["lake", "build", "FiveObjectBinding"]),
            ("axioms", ["lake", "env", "lean", "{out}/Audit.lean"]),
            ("kernel", ["lake", "env", "leanchecker", *MODULES])
            ] + [(name, ["lake", "env", "lean", "{out}/" + name + ".lean"]) for name in controls(claim)]


def replay(out=None, root=ROOT):
    root = Path(root)
    out = root / RECEIPT if out is None else Path(out)
    claim = check_binding(root)
    receipt = read(out / "summary.json")
    require(type(receipt["schema_version"]) is int and receipt["schema_version"] == 1 and receipt["status"] == "passed", "run did not pass")
    require(canonical(receipt["claim"]) == canonical(claim) and receipt["limits"] == LIMITS, "receipt claim differs")
    require(receipt["hash_encoding"] == finite.HASH_ENCODING, "wrong hash encoding")
    require(receipt["source_hashes"] == source_hashes(root), "source changed after verification")
    require(receipt["computational_evidence"] == {"path": finite.OUTPUT, "sha256": digest(root / finite.OUTPUT)},
            "computational evidence reference differs")
    finite.replay(root=root)
    expected, negative = plan(claim), controls(claim)
    require(len(receipt["stages"]) == len(expected), "missing stages")
    for actual, (name, command) in zip(receipt["stages"], expected):
        require(actual["name"] == name and actual["command"] == command and actual["cwd"] == PROJECT, "wrong verification command")
        code = actual["exit_code"]
        require(type(code) is int, "wrong exit code type")
        log = (out / (name + ".log")).read_text(encoding="utf-8")
        require((code != 0 and "error:" in log) if name in negative else code == 0, "stage failed: " + name)
    required = {"Audit.lean", *[name + ".log" for name, _ in expected], *[name + ".lean" for name in negative]}
    require(set(receipt["artifacts"]) == required, "artifact set differs")
    for name, sha in receipt["artifacts"].items():
        require(digest(out / name) == sha, "artifact mismatch: " + name)
    require((out / "Audit.lean").read_text(encoding="utf-8") == audit_source(), "audit source differs")
    for name, contents in negative.items():
        require((out / (name + ".lean")).read_text(encoding="utf-8") == contents, "control source differs")
    require("Lean (version 4.34.1," in (out / "version.log").read_text(encoding="utf-8"), "wrong Lean version")
    require(receipt["axioms"] == audit_axioms((out / "axioms.log").read_text(encoding="utf-8")), "axiom audit differs")
    return receipt


def run(out, root=ROOT):
    root, out = Path(root), Path(out).resolve()
    require(not out.exists(), "choose a new output directory")
    claim = check_binding(root)
    finite.replay(root=root)
    before = source_hashes(root)
    out.mkdir(parents=True)
    (out / "Audit.lean").write_bytes(audit_source().encode())
    negative = controls(claim)
    for name, contents in negative.items():
        (out / (name + ".lean")).write_bytes(contents.encode())
    receipt = {"schema_version": 1, "status": "running", "claim": claim, "limits": LIMITS,
               "hash_encoding": finite.HASH_ENCODING, "source_hashes": before,
               "computational_evidence": {"path": finite.OUTPUT, "sha256": digest(root / finite.OUTPUT)},
               "stages": [], "artifacts": {}, "started_utc": datetime.now(timezone.utc).isoformat()}
    try:
        for name, command in plan(claim):
            print("Checking " + name, flush=True)
            started = time.perf_counter()
            proc = subprocess.run([arg.replace("{out}", str(out)) for arg in command], cwd=root / PROJECT,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=900)
            (out / (name + ".log")).write_bytes(proc.stdout)
            receipt["stages"].append({"name": name, "command": command, "cwd": PROJECT, "exit_code": proc.returncode,
                                      "duration_seconds": round(time.perf_counter() - started, 3)})
            require((proc.returncode != 0 and b"error:" in proc.stdout) if name in negative
                    else proc.returncode == 0, "stage failed: " + name + "; see " + str(out))
        require(before == source_hashes(root), "source changed during proof run")
        receipt["axioms"] = audit_axioms((out / "axioms.log").read_text(encoding="utf-8"))
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


def explain(root=ROOT):
    receipt = replay(root=root)
    claim = copy.deepcopy(receipt["claim"])
    claim["proof_evidence"] = {"path": RECEIPT + "/summary.json", "sha256": digest(root / RECEIPT / "summary.json"),
                               "axioms": receipt["axioms"], "validation": "saved receipt replay; no Lean execution during query"}
    claim["computational_evidence"] = {"path": finite.OUTPUT, "sha256": digest(root / finite.OUTPUT),
                                       "validation": "independent exhaustive finite recomputation; Python correctness is not formally proved"}
    return {"id": CLAIM_ID, "path": CLAIM_PATH, "sha256": digest(root / CLAIM_PATH)}, claim


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["generate", "run", "replay"])
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    if args.command == "generate":
        claim = expected_claim()
        finite.write(ROOT / CLAIM_PATH, claim)
        (ROOT / BINDING).write_bytes(binding(claim).encode())
        print("Generated claim and binding; a fresh Lean proof run is still required.")
    else:
        if args.command == "run" and args.out is None:
            parser.error("run requires --out NEW_DIRECTORY")
        out = args.out.resolve() if args.out else ROOT / RECEIPT
        receipt = run(out) if args.command == "run" else replay(out)
        print(f"PASS: {CLAIM_ID}; {len(receipt['stages'])} stages; mode={args.command}")


if __name__ == "__main__":
    main()
