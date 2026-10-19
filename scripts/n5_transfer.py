"""One proved carrier renaming and rule permutation of the saved N5 algebra.

generate saves a claim/binding; run elaborates Lean; replay checks saved evidence.
The record checker accepts this registered transfer, not arbitrary conjectures.
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
import sys
import time

import build_n5_context as source
from tm_pair_proof import audit_axioms, encode, read, digest, require

ROOT = Path(__file__).resolve().parents[1]
PROJECT = "lean/renaming"
EVIDENCE = "evidence/n5-renaming-v1"
CLAIM_PATH = EVIDENCE + "/claim.json"
BINDING = PROJECT + "/N5RenamingBinding.lean"
CLAIM_ID = "context:family-206:saved-n5:renaming:v1"
CONSTRUCTION_ID = "saved:family-206:n5:rotate-and-swap:v1"
THEOREM = "FiniteCongruenceChecks.N5Renaming.all_relations"
PREFIX = "FiniteCongruenceChecks.N5RenamingBinding."
DECLARATIONS = [
    "FiniteCongruenceChecks.Renaming." + n for n in
    ("congruence_iff", "round_trip", "inclusion_iff", "swap_rules")
] + ["FiniteCongruenceChecks.N5Renaming." + n for n in
     ("transferred_congruence", "all_relations", "order_exact", "theta_injective")]
BINDING_NAMES = ("forward_exact", "backward_exact", "inverse_laws", "source_op1", "source_op2",
                 "target_op1", "target_op2", "source_groups", "target_groups",
                 "rule_correspondence", "grouping_correspondence", "checked_classification", "checked_order", "checked_distinct")
DECLARATIONS += [PREFIX + n for n in BINDING_NAMES]
LIMITS = [
    "This record instantiates a proved bijection on Fin 4 and a permutation of the two unary rule symbols. It is not a fixed-signature isomorphism that preserves each original rule name.",
    "The result covers all equivalence relations for the exact displayed source and target operations; it does not transfer operation minimality, a graph certificate, or a claim about a different atlas construction.",
    "The Python exporter and offline record comparison are not proved implementations. Rerun Lean to check the generated mathematical type; saved hashes and receipts alone are not proofs or authenticated attestations.",
    "No agent performance benefit is established; the model benchmark remains paused.",
]


def canonical(value):
    return json.dumps(value, sort_keys=True, ensure_ascii=False, allow_nan=False, separators=(",", ":"))


def permuted(operations, partitions, forward, target_to_source):
    require(type(forward) is list and len(forward) == 4 and
            all(type(v) is int for v in forward) and sorted(forward) == list(range(4)), "object map must be a permutation")
    require(type(target_to_source) is list and len(target_to_source) == 2 and
            all(type(v) is int for v in target_to_source) and sorted(target_to_source) == [0, 1], "rule map must be a permutation")
    backward = [forward.index(x) for x in range(4)]
    target_ops = [[forward[operations[i][backward[y]]] for y in range(4)] for i in target_to_source]
    target_groups = [list(source.normalize([p[backward[y]] for y in range(4)])) for p in partitions]
    return backward, target_ops, target_groups


def expected_claim(root=ROOT):
    original = source.build(root)["claims"][0]
    source_ops = original["values"]["operations"]
    source_groups = [g["partition"] for g in original["values"]["groupings"]]
    forward, rule_map = [1, 2, 3, 0], [1, 0]
    backward, ops, groups = permuted(source_ops, source_groups, forward, rule_map)
    claim = {
        "schema_version": 1, "namespace": "finite-congruence-atlas/n5-renaming-v1",
        "id": CLAIM_ID, "kind": "proved_transport", "construction_id": CONSTRUCTION_ID,
        "source_claim_id": source.SAVED_CLAIM_ID, "source_construction_id": source.SAVED_CONSTRUCTION_ID,
        "evidence_status": "lean_proof_with_recorded_kernel_replay",
        "statement": "Rotating the four object labels and swapping the two rule symbols transports precisely the saved N5 congruences, preserving their inclusion order and distinctness.",
        "scope": "One recorded carrier bijection and rule permutation of the exact saved N5 algebra.",
        "assumptions": ["The maps forward and backward are inverse bijections on Fin 4.",
                        "For every target rule j and source object x, target[j](forward(x)) = forward(source[target_to_source[j]](x)).",
                        "Groupings are equivalence relations; compatibility uses the existing IsPropCongruence definition.",
                        "Lean's kernel and the standard axioms listed in the receipt are trusted."],
        "limits": LIMITS,
        "values": {"carrier": [0, 1, 2, 3],
                   "source": {"operations": source_ops, "groupings": source_groups},
                   "target": {"operations": ops, "groupings": groups}},
        "mapping": {"object_forward_source_to_target": forward, "object_backward_target_to_source": backward,
                    "rule_target_to_source": rule_map, "grouping_source_to_target": [0, 1, 2, 3, 4]},
        "conclusion": {"quantifier": "every r : Fin 4 -> Fin 4 -> Prop",
                       "predicate": "IsPropCongruence target[0] target[1] r iff r is one of the five displayed target groupings",
                       "distinct_groupings": 5, "inclusion_order_preserved": True},
        "theorem": THEOREM,
        "applicable_lemmas": [
            {"theorem": "FiniteCongruenceChecks.Renaming.congruence_iff", "role": "compatibility_transport"},
            {"theorem": "FiniteCongruenceChecks.Renaming.swap_rules", "role": "signature_permutation"},
            {"theorem": "FiniteCongruenceChecks.N5.all_relations", "role": "source_classification"},
            {"theorem": THEOREM, "role": "target_classification"},
            {"theorem": "FiniteCongruenceChecks.N5Renaming.order_exact", "role": "inclusion_order"},
            {"theorem": "FiniteCongruenceChecks.N5Renaming.theta_injective", "role": "distinctness"}],
        "citations": [{"path": p, "sha256": digest(root / p)} for p in
                      ("lean/CertificateData.lean", "lean/FiniteCongruenceChecks.lean",
                       PROJECT + "/Renaming.lean", PROJECT + "/N5Renaming.lean")],
        "source_evidence": {"path": "lean/evidence/bridge-run/result.json",
                            "sha256": digest(root / "lean/evidence/bridge-run/result.json"),
                            "role": "separate saved source proof receipt"},
    }
    claim["citations"].append({"path": BINDING, "sha256": hashlib.sha256(binding(claim).encode()).hexdigest()})
    return claim


def table(values, size=4):
    require(type(values) is list and len(values) == size and
            all(type(v) is int and 0 <= v < 4 for v in values), "invalid finite table")
    return "fun x => match x.val with " + " ".join(
        f"| {i if i < size - 1 else '_'} => {v}" for i, v in enumerate(values))


def groups_table(groups):
    require(type(groups) is list and len(groups) == 5, "expected five grouping tables")
    return "fun a => match a.val with\n" + "\n".join(
        f"  | {i if i < 4 else '_'} => {table(p)}" for i, p in enumerate(groups))


def binding(claim):
    name = claim["theorem"]
    require(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)+", name), "invalid theorem identifier")
    values, mapping = claim["values"], claim["mapping"]
    rule_map = mapping["rule_target_to_source"]
    require(type(rule_map) is list and len(rule_map) == 2 and
            all(type(v) is int for v in rule_map) and sorted(rule_map) == [0, 1], "invalid rule permutation")
    pieces = ["-- Generated by scripts/n5_transfer.py generate; checked without rewriting.\nimport N5Renaming\nnamespace FiniteCongruenceChecks.N5RenamingBinding\n"]
    for name_part, vals in (("p", mapping["object_forward_source_to_target"]), ("q", mapping["object_backward_target_to_source"]),
                            ("f", values["source"]["operations"][0]), ("g", values["source"]["operations"][1]),
                            ("h", values["target"]["operations"][0]), ("k", values["target"]["operations"][1])):
        pieces.append(f"private def {name_part} : V → V := {table(vals)}\n")
    pieces += [f"private def srcGroup : Fin 5 → V → V := {groups_table(values['source']['groupings'])}\n",
               f"private def dstGroup : Fin 5 → V → V := {groups_table(values['target']['groupings'])}\n"]
    group_map = mapping["grouping_source_to_target"]
    require(type(group_map) is list and len(group_map) == 5 and all(type(v) is int for v in group_map)
            and sorted(group_map) == list(range(5)), "invalid grouping permutation")
    pieces.append("private def groupMap : Fin 5 → Fin 5 := fun a => match a.val with " +
                  " ".join(f"| {i if i < 4 else '_'} => {v}" for i, v in enumerate(group_map)) + "\n")
    for declaration, actual, expected in (("forward_exact", "N5Renaming.forward", "p"),
        ("backward_exact", "N5Renaming.backward", "q"), ("source_op1", "N5.op1", "f"),
        ("source_op2", "N5.op2", "g"), ("target_op1", "N5Renaming.op1", "h"), ("target_op2", "N5Renaming.op2", "k")):
        pieces.append(f"theorem {declaration} : {actual} = {expected} := funext (by decide)\n")
    pieces += ["theorem inverse_laws : (∀ x, q (p x) = x) ∧ (∀ x, p (q x) = x) := by decide\n",
               "theorem source_groups : ∀ a x y, (N5.theta a x y = true) ↔ srcGroup a x = srcGroup a y := by decide\n",
               "theorem target_groups : ∀ a x y, N5Renaming.theta a x y ↔ dstGroup a x = dstGroup a y := by\n  unfold N5Renaming.theta Renaming.relation\n  decide\n"]
    src_names = ["f", "g"]
    pieces.append(f"theorem rule_correspondence : (∀ x, h (p x) = p ({src_names[rule_map[0]]} x)) ∧ (∀ x, k (p x) = p ({src_names[rule_map[1]]} x)) := by decide\n")
    pieces.append("theorem grouping_correspondence : ∀ a x y, (dstGroup (groupMap a) (p x) = dstGroup (groupMap a) (p y)) ↔ (srcGroup a x = srcGroup a y) := by decide\n")
    pieces.append(f"""theorem checked_classification (r : V → V → Prop) :
    IsPropCongruence h k r ↔ ∃ a : Fin 5, ∀ x y, r x y ↔ dstGroup a x = dstGroup a y := by
  have proof := {name} r
  simpa only [target_op1, target_op2, target_groups] using proof
theorem checked_order (a b : Fin 5) :
    N5.le a b = true ↔ (∀ x y, dstGroup a x = dstGroup a y → dstGroup b x = dstGroup b y) := by
  simpa only [target_groups] using N5Renaming.order_exact a b
theorem checked_distinct (a b : Fin 5)
    (h : ∀ x y, (dstGroup a x = dstGroup a y) ↔ (dstGroup b x = dstGroup b y)) : a = b := by
  apply N5Renaming.theta_injective a b
  simpa only [target_groups] using h
end FiniteCongruenceChecks.N5RenamingBinding
""")
    return "".join(pieces)


def validate_project(root):
    # Pin both packages: a source-directory override can otherwise import an
    # unrecorded module while the receipt hashes the expected source path.
    for project in (root / "lean", root / PROJECT):
        require(not (project / "lakefile.lean").exists(), "unexpected alternate Lake configuration")
    manifest = read(root / PROJECT / "lake-manifest.json")
    require(canonical(manifest) == canonical({"version": "1.2.0", "packagesDir": ".lake/packages", "packages": [
        {"type": "path", "scope": "", "name": "finiteCongruenceChecks", "manifestFile": "lake-manifest.json",
         "inherited": False, "dir": "..", "configFile": "lakefile.toml"}],
        "name": "n5Renaming", "lakeDir": ".lake", "fixedToolchain": False}), "unexpected dependency manifest")
    require((root / PROJECT / "..").resolve() == (root / "lean").resolve(), "wrong source project")
    require(canonical(read(root / "lean/lake-manifest.json")) == canonical({
        "version": "1.2.0", "packagesDir": ".lake/packages", "packages": [],
        "name": "finiteCongruenceChecks", "lakeDir": ".lake", "fixedToolchain": False}),
        "unexpected source dependency manifest")
    core_config = '''name = "finiteCongruenceChecks"
version = "0.1.0"
defaultTargets = ["FiniteCongruenceChecks", "GroupingChecker", "grouping_checker"]

[[lean_lib]]
name = "FiniteCongruenceChecks"

[[lean_lib]]
name = "CertificateData"

[[lean_lib]]
name = "GroupingChecker"

[[lean_exe]]
name = "grouping_checker"
root = "GroupingMain"
'''
    require((root / "lean/lakefile.toml").read_text(encoding="utf-8") == core_config,
            "unexpected source project configuration")
    require((root / PROJECT / "lean-toolchain").read_text(encoding="utf-8").strip() ==
            (root / "lean/lean-toolchain").read_text(encoding="utf-8").strip() == "leanprover/lean4:v4.34.1", "wrong toolchain")
    config = 'name = "n5Renaming"\nversion = "0.1.0"\ndefaultTargets = ["Renaming", "N5Renaming", "N5RenamingBinding"]\n\n[[require]]\nname = "finiteCongruenceChecks"\npath = ".."\n'
    config += ''.join('\n[[lean_lib]]\nname = "' + n + '"\n' for n in ('Renaming', 'N5Renaming', 'N5RenamingBinding'))
    require((root / PROJECT / "lakefile.toml").read_text(encoding="utf-8") == config, "unexpected project configuration")


def check_binding(root=ROOT):
    validate_project(root)
    claim = expected_claim(root)
    require(canonical(read(root / CLAIM_PATH)) == canonical(claim), "transfer claim differs from registered binding")
    require((root / BINDING).read_text(encoding="utf-8") == binding(claim), "stale Lean binding")
    return claim


def source_hashes(root=ROOT):
    paths = [PROJECT + "/" + name for name in
             ("Renaming.lean", "N5Renaming.lean", "N5RenamingBinding.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain")]
    paths += ["lean/" + name for name in ("CertificateData.lean", "FiniteCongruenceChecks.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain")]
    paths += [CLAIM_PATH, "scripts/n5_transfer.py", "scripts/build_n5_context.py", "scripts/tm_pair_proof.py",
              "scripts/run_tm_checks.py", "scripts/tm_atlas.py"]
    return {path: digest(root / path) for path in sorted(set(paths) | set(source.PINNED_SOURCES))}


def controls(claim):
    result = {}
    for name, mutate in (
        ("inconsistent-rule", lambda c: c["values"]["target"]["operations"][0].__setitem__(0, 0)),
        ("inconsistent-grouping", lambda c: c["values"]["target"]["groupings"][1].__setitem__(2, 2)),
        ("inconsistent-object-map", lambda c: c["mapping"].__setitem__("object_forward_source_to_target", [0, 1, 2, 3])),
        ("unswapped-rule-map", lambda c: c["mapping"].__setitem__("rule_target_to_source", [0, 1])),
        ("unrelated-theorem", lambda c: c.__setitem__("theorem", "FiniteCongruenceChecks.B3.all_relations"))):
        changed = copy.deepcopy(claim)
        mutate(changed)
        result[name] = binding(changed)
    return result


def audit_source():
    return "import N5RenamingBinding\n" + "".join("#print axioms " + n + "\n" for n in DECLARATIONS)


def plan(claim):
    return [("version", ["lake", "env", "lean", "--version"]),
            ("build", ["lake", "build", "N5RenamingBinding"]),
            ("axioms", ["lake", "env", "lean", "{out}/Audit.lean"]),
            ("kernel", ["lake", "env", "leanchecker", "CertificateData", "FiniteCongruenceChecks", "Renaming", "N5Renaming", "N5RenamingBinding"])
            ] + [(n, ["lake", "env", "lean", "{out}/" + n + ".lean"]) for n in controls(claim)]


def replay(out=None, root=ROOT):
    out = root / EVIDENCE if out is None else Path(out)
    claim = check_binding(root)
    receipt = read(out / "summary.json")
    require(type(receipt["schema_version"]) is int and receipt["schema_version"] == 1 and receipt["status"] == "passed", "run did not pass")
    require(canonical(receipt["claim"]) == canonical(claim) and receipt["limits"] == LIMITS, "receipt claim differs")
    require(receipt["hash_encoding"] == "SHA-256 with CRLF normalized to LF", "wrong hash encoding")
    require(receipt["source_hashes"] == source_hashes(root), "source changed after verification")
    expected = plan(claim)
    require(len(receipt["stages"]) == len(expected), "missing stages")
    for actual, (name, command) in zip(receipt["stages"], expected):
        require(actual["name"] == name and actual["command"] == command and actual["cwd"] == PROJECT, "wrong verification command")
        code = actual["exit_code"]
        require(type(code) is int, "wrong exit code type")
        log = (out / (name + ".log")).read_text(encoding="utf-8")
        require((code != 0 and "error:" in log) if name in controls(claim) else code == 0, f"stage failed: {name}")
    required = {"Audit.lean", *[name + ".log" for name, _ in expected], *[name + ".lean" for name in controls(claim)]}
    require(set(receipt["artifacts"]) == required, "artifact set differs")
    for name, sha in receipt["artifacts"].items():
        require(digest(out / name) == sha, f"artifact mismatch: {name}")
    require((out / "Audit.lean").read_text(encoding="utf-8") == audit_source(), "audit source differs")
    for name, text in controls(claim).items():
        require((out / (name + ".lean")).read_text(encoding="utf-8") == text, "control source differs")
    require("Lean (version 4.34.1," in (out / "version.log").read_text(encoding="utf-8"), "wrong Lean version")
    require(receipt["axioms"] == audit_axioms((out / "axioms.log").read_text(encoding="utf-8"), DECLARATIONS), "axiom audit differs")
    return receipt


def run(out, root=ROOT):
    require(not out.exists(), "choose a new output directory")
    claim = check_binding(root)
    before = source_hashes(root)
    out.mkdir(parents=True)
    (out / "Audit.lean").write_bytes(audit_source().encode())
    for name, text in controls(claim).items():
        (out / (name + ".lean")).write_bytes(text.encode())
    receipt = {"schema_version": 1, "status": "running", "claim": claim, "limits": LIMITS,
               "hash_encoding": "SHA-256 with CRLF normalized to LF", "source_hashes": before,
               "stages": [], "artifacts": {}, "started_utc": datetime.now(timezone.utc).isoformat()}
    try:
        for name, command in plan(claim):
            print(f"Checking {name}", flush=True)
            started = time.perf_counter()
            proc = subprocess.run([arg.replace("{out}", str(out)) for arg in command], cwd=root / PROJECT,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300)
            (out / (name + ".log")).write_bytes(proc.stdout)
            receipt["stages"].append({"name": name, "command": command, "cwd": PROJECT, "exit_code": proc.returncode,
                                      "duration_seconds": round(time.perf_counter() - started, 3)})
            require((proc.returncode != 0 and b"error:" in proc.stdout) if name in controls(claim)
                    else proc.returncode == 0, f"stage failed: {name}; see {out}")
        require(before == source_hashes(root), "source changed during proof run")
        receipt["axioms"] = audit_axioms((out / "axioms.log").read_text(encoding="utf-8"), DECLARATIONS)
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
    claim["proof_evidence"] = {"path": EVIDENCE + "/summary.json", "sha256": digest(root / EVIDENCE / "summary.json"),
                               "axioms": receipt["axioms"], "validation": "saved receipt replay; no Lean execution during query"}
    return {"id": "context:n5-renaming:v1", "path": CLAIM_PATH, "sha256": digest(root / CLAIM_PATH)}, claim


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["generate", "run", "replay"])
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    if args.command == "generate":
        claim = expected_claim()
        (ROOT / EVIDENCE).mkdir(parents=True, exist_ok=True)
        (ROOT / CLAIM_PATH).write_bytes(encode(claim))
        (ROOT / BINDING).write_bytes(binding(claim).encode())
        print("Generated claim and binding; Lean proof run still required.")
    else:
        if args.command == "run" and args.out is None:
            parser.error("run requires --out NEW_DIRECTORY")
        out = args.out.resolve() if args.out else ROOT / EVIDENCE
        receipt = run(out) if args.command == "run" else replay(out)
        print(f"PASS: {CLAIM_ID}; {len(receipt['stages'])} stages; mode={args.command}")


if __name__ == "__main__":
    main()
