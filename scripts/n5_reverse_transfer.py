"""Prove and bind one N5 relabeling that preserves the two rule names.

generate writes the registered claim/binding; run invokes Lean and its kernel
checker; replay validates saved evidence without executing Lean or a model.
"""
from __future__ import annotations

import argparse
import copy
from datetime import datetime, timezone
import hashlib
from pathlib import Path
import re
import subprocess
import time

import build_n5_context as source
import n5_transfer as original
from n5_transfer import canonical, permuted, table, groups_table
from tm_pair_proof import audit_axioms, encode, read, digest, require

ROOT = Path(__file__).resolve().parents[1]
PROJECT = "lean/renaming_reverse"
EVIDENCE = "evidence/n5-reverse-labels-v1"
CLAIM_PATH = EVIDENCE + "/claim.json"
BINDING = PROJECT + "/N5ReverseLabelsBinding.lean"
CLAIM_ID = "context:family-206:saved-n5:reverse-labels:v1"
CONSTRUCTION_ID = "saved:family-206:n5:reverse-labels:v1"
THEOREM = "FiniteCongruenceChecks.N5ReverseLabels.all_relations"
PREFIX = "FiniteCongruenceChecks.N5ReverseLabelsBinding."
DECLARATIONS = ["FiniteCongruenceChecks.Renaming." + n for n in
                ("congruence_iff", "round_trip", "inclusion_iff")]
DECLARATIONS += ["FiniteCongruenceChecks.N5ReverseLabels." + n for n in
                 ("transferred_congruence", "all_relations", "order_exact", "theta_injective")]
BINDING_NAMES = (*original.BINDING_NAMES, "conclusion_exact")
DECLARATIONS += [PREFIX + n for n in BINDING_NAMES]
QUANTIFIER = "every r : Fin 4 -> Fin 4 -> Prop"
PREDICATE = "IsPropCongruence target[0] target[1] r iff r is one of the five displayed target groupings"
LIMITS = [
    "This record instantiates one proved bijection on Fin 4 with the identity permutation of the two unary rule symbols. It preserves each rule name.",
    "The result covers all equivalence relations for the exact displayed source and target operations; it does not transfer operation minimality, a graph certificate, or a claim about a different atlas construction.",
    "The Python exporter and offline record comparison are not proved implementations. Rerun Lean to check the generated mathematical type; saved hashes and receipts alone are not proofs or authenticated attestations.",
    "No agent performance benefit is established; the model benchmark remains paused.",
]


def expected_claim(root=ROOT):
    saved = source.build(root)["claims"][0]
    source_ops = saved["values"]["operations"]
    source_groups = [g["partition"] for g in saved["values"]["groupings"]]
    forward, rule_map = [3, 2, 1, 0], [0, 1]
    backward, ops, groups = permuted(source_ops, source_groups, forward, rule_map)
    claim = {
        "schema_version": 1, "namespace": "finite-congruence-atlas/n5-renaming-v1",
        "id": CLAIM_ID, "kind": "proved_transport", "construction_id": CONSTRUCTION_ID,
        "source_claim_id": source.SAVED_CLAIM_ID, "source_construction_id": source.SAVED_CONSTRUCTION_ID,
        "evidence_status": "lean_proof_with_recorded_kernel_replay",
        "statement": "Reversing the four object labels while preserving the two rule names transports precisely the saved N5 congruences, preserving their inclusion order and distinctness.",
        "scope": "One recorded carrier bijection with identity rule correspondence of the exact saved N5 algebra.",
        "assumptions": ["The maps forward and backward are inverse bijections on Fin 4.",
                        "For every target rule j and source object x, target[j](forward(x)) = forward(source[j](x)).",
                        "Groupings are equivalence relations; compatibility uses the existing IsPropCongruence definition.",
                        "Lean's kernel and the standard axioms listed in the receipt are trusted."],
        "limits": LIMITS,
        "values": {"carrier": [0, 1, 2, 3],
                   "source": {"operations": source_ops, "groupings": source_groups},
                   "target": {"operations": ops, "groupings": groups}},
        "mapping": {"object_forward_source_to_target": forward, "object_backward_target_to_source": backward,
                    "rule_target_to_source": rule_map, "grouping_source_to_target": [0, 1, 2, 3, 4]},
        "conclusion": {"quantifier": QUANTIFIER, "predicate": PREDICATE,
                       "distinct_groupings": 5, "inclusion_order_preserved": True},
        "theorem": THEOREM,
        "applicable_lemmas": [
            {"theorem": "FiniteCongruenceChecks.Renaming.congruence_iff", "role": "compatibility_transport"},
            {"theorem": "FiniteCongruenceChecks.N5.all_relations", "role": "source_classification"},
            {"theorem": THEOREM, "role": "target_classification"},
            {"theorem": "FiniteCongruenceChecks.N5ReverseLabels.order_exact", "role": "inclusion_order"},
            {"theorem": "FiniteCongruenceChecks.N5ReverseLabels.theta_injective", "role": "distinctness"}],
        "citations": [{"path": p, "sha256": digest(root / p)} for p in
                      ("lean/CertificateData.lean", "lean/FiniteCongruenceChecks.lean",
                       "lean/renaming/Renaming.lean", PROJECT + "/N5ReverseLabels.lean")],
        "source_evidence": {"path": "lean/evidence/bridge-run/result.json",
                            "sha256": digest(root / "lean/evidence/bridge-run/result.json"),
                            "role": "separate saved source proof receipt"},
    }
    claim["citations"].append({"path": BINDING, "sha256": hashlib.sha256(binding(claim).encode()).hexdigest()})
    return claim


def binding(claim):
    """Emit typed mathematical obligations; never execute a record as code."""
    theorem = claim["theorem"]
    require(type(theorem) is str and re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)+", theorem),
            "invalid theorem identifier")
    values, mapping, conclusion = claim["values"], claim["mapping"], claim["conclusion"]
    require(conclusion["quantifier"] == QUANTIFIER and conclusion["predicate"] == PREDICATE,
            "unsupported conclusion meaning")
    count, preserves = conclusion["distinct_groupings"], conclusion["inclusion_order_preserved"]
    require(type(count) is int and 0 <= count <= 15 and type(preserves) is bool, "invalid conclusion type")
    rule_map = mapping["rule_target_to_source"]
    require(type(rule_map) is list and len(rule_map) == 2 and
            all(type(v) is int for v in rule_map) and sorted(rule_map) == [0, 1], "invalid rule permutation")
    pieces = ["-- Generated by scripts/n5_reverse_transfer.py generate; checked without rewriting.\n"
              "import N5ReverseLabels\nnamespace FiniteCongruenceChecks.N5ReverseLabelsBinding\n"]
    for name, vals in (("p", mapping["object_forward_source_to_target"]), ("q", mapping["object_backward_target_to_source"]),
                       ("f", values["source"]["operations"][0]), ("g", values["source"]["operations"][1]),
                       ("h", values["target"]["operations"][0]), ("k", values["target"]["operations"][1])):
        pieces.append(f"private def {name} : V → V := {table(vals)}\n")
    pieces += [f"private def srcGroup : Fin 5 → V → V := {groups_table(values['source']['groupings'])}\n",
               f"private def dstGroup : Fin 5 → V → V := {groups_table(values['target']['groupings'])}\n"]
    group_map = mapping["grouping_source_to_target"]
    require(type(group_map) is list and len(group_map) == 5 and all(type(v) is int for v in group_map)
            and sorted(group_map) == list(range(5)), "invalid grouping permutation")
    pieces.append("private def groupMap : Fin 5 → Fin 5 := fun a => match a.val with " +
                  " ".join(f"| {i if i < 4 else '_'} => {v}" for i, v in enumerate(group_map)) + "\n")
    for declaration, actual, expected in (("forward_exact", "N5ReverseLabels.forward", "p"),
        ("backward_exact", "N5ReverseLabels.backward", "q"), ("source_op1", "N5.op1", "f"),
        ("source_op2", "N5.op2", "g"), ("target_op1", "N5ReverseLabels.op1", "h"), ("target_op2", "N5ReverseLabels.op2", "k")):
        pieces.append(f"theorem {declaration} : {actual} = {expected} := funext (by decide)\n")
    pieces += ["theorem inverse_laws : (∀ x, q (p x) = x) ∧ (∀ x, p (q x) = x) := by decide\n",
               "theorem source_groups : ∀ a x y, (N5.theta a x y = true) ↔ srcGroup a x = srcGroup a y := by decide\n",
               "theorem target_groups : ∀ a x y, N5ReverseLabels.theta a x y ↔ dstGroup a x = dstGroup a y := by\n"
               "  unfold N5ReverseLabels.theta Renaming.relation\n  decide\n"]
    names = ["f", "g"]
    pieces.append(f"theorem rule_correspondence : (∀ x, h (p x) = p ({names[rule_map[0]]} x)) ∧ (∀ x, k (p x) = p ({names[rule_map[1]]} x)) := by decide\n")
    pieces.append("theorem grouping_correspondence : ∀ a x y, (dstGroup (groupMap a) (p x) = dstGroup (groupMap a) (p y)) ↔ (srcGroup a x = srcGroup a y) := by decide\n")
    pieces.append(f"theorem conclusion_exact : (5 : Nat) = {count} ∧ ({str(preserves).lower()} : Bool) = true := by decide\n")
    pieces.append(f"""theorem checked_classification (r : V → V → Prop) :
    IsPropCongruence h k r ↔ ∃ a : Fin 5, ∀ x y, r x y ↔ dstGroup a x = dstGroup a y := by
  have proof := {theorem} r
  simpa only [target_op1, target_op2, target_groups] using proof
theorem checked_order (a b : Fin 5) :
    N5.le a b = true ↔ (∀ x y, dstGroup a x = dstGroup a y → dstGroup b x = dstGroup b y) := by
  simpa only [target_groups] using N5ReverseLabels.order_exact a b
theorem checked_distinct (a b : Fin 5)
    (h : ∀ x y, (dstGroup a x = dstGroup a y) ↔ (dstGroup b x = dstGroup b y)) : a = b := by
  apply N5ReverseLabels.theta_injective a b
  simpa only [target_groups] using h
end FiniteCongruenceChecks.N5ReverseLabelsBinding
""")
    return "".join(pieces)


def validate_project(root):
    # This validates both transitive packages, including their pinned manifests,
    # toolchains and exact Lake files, before any build command runs.
    original.validate_project(root)
    project = root / PROJECT
    require(not (project / "lakefile.lean").exists(), "unexpected alternate Lake configuration")
    packages = [{"type": "path", "scope": "", "name": name, "manifestFile": "lake-manifest.json",
                 "inherited": inherited, "dir": directory, "configFile": "lakefile.toml"}
                for name, inherited, directory in (("n5Renaming", False, "../renaming"),
                                                    ("finiteCongruenceChecks", True, "../renaming/.."))]
    require(canonical(read(project / "lake-manifest.json")) == canonical({"version": "1.2.0",
            "packagesDir": ".lake/packages", "packages": packages, "name": "n5ReverseLabels",
            "lakeDir": ".lake", "fixedToolchain": False}), "unexpected reverse dependency manifest")
    require((project / "lean-toolchain").read_text(encoding="utf-8").strip() == "leanprover/lean4:v4.34.1", "wrong toolchain")
    config = 'name = "n5ReverseLabels"\nversion = "0.1.0"\ndefaultTargets = ["N5ReverseLabels", "N5ReverseLabelsBinding"]\n\n[[require]]\nname = "n5Renaming"\npath = "../renaming"\n'
    config += ''.join('\n[[lean_lib]]\nname = "' + n + '"\n' for n in ("N5ReverseLabels", "N5ReverseLabelsBinding"))
    require((project / "lakefile.toml").read_text(encoding="utf-8") == config, "unexpected reverse project configuration")
    require((project / "../renaming").resolve() == (root / original.PROJECT).resolve(), "wrong renaming project")


def check_binding(root=ROOT):
    validate_project(root)
    claim = expected_claim(root)
    require(canonical(read(root / CLAIM_PATH)) == canonical(claim), "transfer claim differs from registered binding")
    require((root / BINDING).read_text(encoding="utf-8") == binding(claim), "stale Lean binding")
    return claim


def source_hashes(root=ROOT):
    paths = [PROJECT + "/" + name for name in
             ("N5ReverseLabels.lean", "N5ReverseLabelsBinding.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain")]
    paths += [CLAIM_PATH, "scripts/n5_reverse_transfer.py", "scripts/tm_cases.py", "scripts/tm_port.py"]
    # The imported helper implementation is pinned together with the complete
    # original source/dependency chain. It is never patched or overwritten.
    return {**original.source_hashes(root), **{p: digest(root / p) for p in paths}}


def controls(claim):
    result = {}
    for name, mutate in (
        ("inconsistent-rule", lambda c: c["values"]["target"]["operations"][1].__setitem__(0, 0)),
        ("inconsistent-grouping", lambda c: c["values"]["target"]["groupings"][1].__setitem__(2, 1)),
        ("inconsistent-object-map", lambda c: c["mapping"].__setitem__("object_forward_source_to_target", [0, 1, 2, 3])),
        ("wrong-rule-map", lambda c: c["mapping"].__setitem__("rule_target_to_source", [1, 0])),
        ("inconsistent-grouping-map", lambda c: c["mapping"].__setitem__("grouping_source_to_target", [1, 0, 2, 3, 4])),
        ("wrong-distinct-count", lambda c: c["conclusion"].__setitem__("distinct_groupings", 4)),
        ("wrong-order-conclusion", lambda c: c["conclusion"].__setitem__("inclusion_order_preserved", False)),
        ("unrelated-theorem", lambda c: c.__setitem__("theorem", "FiniteCongruenceChecks.B3.all_relations"))):
        changed = copy.deepcopy(claim)
        mutate(changed)
        result[name] = binding(changed)
    return result


def audit_source():
    return "import N5ReverseLabelsBinding\n" + "".join("#print axioms " + n + "\n" for n in DECLARATIONS)


def plan(claim):
    return [("version", ["lake", "env", "lean", "--version"]),
            ("build", ["lake", "build", "N5ReverseLabelsBinding"]),
            ("axioms", ["lake", "env", "lean", "{out}/Audit.lean"]),
            ("kernel", ["lake", "env", "leanchecker", "CertificateData", "FiniteCongruenceChecks", "Renaming", "N5ReverseLabels", "N5ReverseLabelsBinding"])
            ] + [(name, ["lake", "env", "lean", "{out}/" + name + ".lean"]) for name in controls(claim)]


def replay(out=None, root=ROOT):
    out = root / EVIDENCE if out is None else Path(out)
    claim = check_binding(root)
    receipt = read(out / "summary.json")
    require(type(receipt["schema_version"]) is int and receipt["schema_version"] == 1 and receipt["status"] == "passed", "run did not pass")
    require(canonical(receipt["claim"]) == canonical(claim) and receipt["limits"] == LIMITS, "receipt claim differs")
    require(receipt["hash_encoding"] == "SHA-256 with CRLF normalized to LF", "wrong hash encoding")
    require(receipt["source_hashes"] == source_hashes(root), "source changed after verification")
    expected, negative = plan(claim), controls(claim)
    require(len(receipt["stages"]) == len(expected), "missing stages")
    for actual, (name, command) in zip(receipt["stages"], expected):
        require(actual["name"] == name and actual["command"] == command and actual["cwd"] == PROJECT, "wrong verification command")
        code = actual["exit_code"]
        require(type(code) is int, "wrong exit code type")
        log = (out / (name + ".log")).read_text(encoding="utf-8")
        require((code != 0 and "error:" in log) if name in negative else code == 0, f"stage failed: {name}")
    required = {"Audit.lean", *[name + ".log" for name, _ in expected], *[name + ".lean" for name in negative]}
    require(set(receipt["artifacts"]) == required, "artifact set differs")
    for name, sha in receipt["artifacts"].items():
        require(digest(out / name) == sha, f"artifact mismatch: {name}")
    require((out / "Audit.lean").read_text(encoding="utf-8") == audit_source(), "audit source differs")
    for name, text in negative.items():
        require((out / (name + ".lean")).read_text(encoding="utf-8") == text, "control source differs")
    require("Lean (version 4.34.1," in (out / "version.log").read_text(encoding="utf-8"), "wrong Lean version")
    require(receipt["axioms"] == audit_axioms((out / "axioms.log").read_text(encoding="utf-8"), DECLARATIONS), "axiom audit differs")
    return receipt


def run(out, root=ROOT):
    out = Path(out).resolve()
    require(not out.exists(), "choose a new output directory")
    claim = check_binding(root)
    before = source_hashes(root)
    out.mkdir(parents=True)
    (out / "Audit.lean").write_bytes(audit_source().encode())
    negative = controls(claim)
    for name, text in negative.items():
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
            require((proc.returncode != 0 and b"error:" in proc.stdout) if name in negative
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
    return {"id": "context:n5-reverse-labels:v1", "path": CLAIM_PATH, "sha256": digest(root / CLAIM_PATH)}, claim


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
