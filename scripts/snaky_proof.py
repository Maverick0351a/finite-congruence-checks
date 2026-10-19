"""Build the finite-board Snaky theorem and bind it to exact atlas records.

generate writes the claim and mathematical binding. run checks Lean, the kernel,
axioms and deliberate errors. replay checks saved records without executing Lean.
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
import signal
import subprocess
import time

import check_snaky as finite

ROOT = Path(__file__).resolve().parents[1]
PROJECT = "lean/snaky"
EVIDENCE = "evidence/snaky-finite-v1"
CLAIM_PATH = EVIDENCE + "/claim.json"
RECEIPT = EVIDENCE + "/proof"
BINDING = PROJECT + "/SnakyBinding.lean"
CLAIM_ID = finite.CLAIM_ID
PREFIX = "FiniteCongruenceChecks.SnakyFinite."
BPREFIX = PREFIX + "Binding."
VENDOR_MANIFEST_SHA256 = "ca09b16a386355c5aa5a46c91fa87b6979cfc809ddc01b55743d6199e6e63c22"
DEPENDENCY_MANIFEST_SHA256 = "5dda7eda39168cec70584a4b94d61681a7838d3daf43d093f31f4c4aaddf8e68"
ALLOWED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
ENVIRONMENT = {"LEAN_NUM_THREADS": "1", "MATHLIB_NO_CACHE_ON_UPDATE": "1"}
DEFAULT_STAGE_TIMEOUT = 2400
BUILD_TIMEOUT = 3600
KERNEL_TIMEOUT = 7200
BINDING_NAMES = ["target_exact", "envelope_exact", "square_exact", "inputs_exact",
                 "counts_exact", "checked_envelope", "checked_square"]
DECLARATIONS = [PREFIX + name for name in (
    "FiniteWins.false_impossible", "FiniteWins.zero_iff", "fresh_cell", "finite_immediate", "finite_compose",
    "envelope_card", "square_card", "envelope_subset_square", "square_membership",
    "board_wins", "envelope_wins", "square_wins")]
DECLARATIONS += [BPREFIX + name for name in BINDING_NAMES]
PREDICATE = "A finite-board strategy tree guarantees a translated or square-symmetry copy of the exact six-cell Snaky within the stated number of actual fresh Maker claims from empty Maker and Breaker sets; every legal on-board Breaker reply is covered, and victory needs no further reply."
LIMITS = [
    "This formalizes the source paper's existing 21-Maker-claim finite-board corollaries. It does not establish a new bound, optimality, or a smallest board.",
    "The formal result is a finite-board strategy-tree guarantee, not an extracted or benchmarked executable policy.",
    "The 728-card theorem certificate is distinct from the historical 616-card comparator reconstruction.",
    "The independent Python certificate reconstruction is tested computation, not a formally verified implementation.",
    "Saved receipt replay checks recorded sources, commands, artifacts and bindings. It is not a new kernel execution or an authenticated attestation.",
    "No general translation correctness or improved agent reasoning is established. Model benchmarks and training remain paused."
]
require, encode, read, digest = finite.require, finite.encode, finite.read, finite.digest


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False, allow_nan=False)


def expected_claim(root=ROOT):
    audit = finite.replay(root=root)
    claim = {
        "schema_version": 1, "namespace": "finite-congruence-atlas/snaky-finite-v1",
        "id": CLAIM_ID, "kind": "finite_board_strategy",
        "evidence_status": "lean_proof_with_recorded_kernel_replay",
        "statement": "Maker can force Snaky within 21 actual claims on the exact 251-cell envelope, and on the square with integer coordinates 0 through 16 in both directions.",
        "scope": "One exact 728-card certificate, two specified finite boards, empty initial position; all legal board-contained Breaker replies.",
        "assumptions": ["Maker moves first; players alternate claiming one fresh cell of the selected board.",
                        "Maker wins by owning a translated, rotated or reflected copy of the six specified target cells.",
                        "The game ends when Maker wins; no Breaker reply after victory is required.",
                        "Lean's kernel and only the standard axioms listed in the receipt are trusted."],
        "limits": LIMITS,
        "values": {"target": [list(p) for p in finite.SNAKY], "card_index": 727,
                   "envelope": audit["final"]["support"], "square_bounds": audit["finite_board"]["bounds"],
                   "initial_maker": [], "initial_breaker": [], "certificate": audit["upstream"]},
        "conclusion": {"predicate": PREDICATE, "maker_claims_at_most": 21,
                       "envelope_cells": 251, "square_cells": 289},
        "theorems": {"envelope": PREFIX + "envelope_wins", "square": PREFIX + "square_wins"},
        "applicable_lemmas": [{"theorem": PREFIX + name, "role": role} for name, role in (
            ("fresh_cell", "A strict occupied-cell bound supplies a legal board-contained cell."),
            ("finite_compose", "The finite resource invariant justifies pivot replacement and every legal Breaker continuation."),
            ("board_wins", "Any finite board containing the exact final envelope and at least 42 cells supports the strategy."),
            ("envelope_wins", "Empty initial position on the exact 251-cell envelope."),
            ("square_wins", "Empty initial position on the exact 17 by 17 square."))],
        "citations": [{"path": p, "sha256": digest(root / p)} for p in (
            PROJECT + "/SnakySemantics.lean", PROJECT + "/SnakyFinite.lean", PROJECT + "/vendor-manifest.json")],
        "upstream_context": {"family": "187", "revision": finite.UPSTREAM_COMMIT,
                             "scope_url": f"https://github.com/openai/math/blob/{finite.UPSTREAM_COMMIT}/lean/docs/187.md",
                             "paper_url": f"https://github.com/openai/math/blob/{finite.UPSTREAM_COMMIT}/preprints/Snaky-in-21-Maker-moves-September-25-2026/build/strategy.tex",
                             "role": "The paper states the finite-board corollaries. The selected upstream Lean theorem covers the infinite grid."}
    }
    claim["citations"].append({"path": BINDING, "sha256": hashlib.sha256(binding(claim).encode()).hexdigest()})
    return claim


def _int(value):
    require(type(value) is int and -100 <= value <= 100, "invalid cell coordinate")
    return str(value)


def _nat(value, maximum=1000):
    require(type(value) is int and 0 <= value <= maximum, "invalid natural number")
    return str(value)


def _points(value):
    require(type(value) is list and len(value) <= 300, "invalid cell list")
    result = []
    for p in value:
        require(type(p) is list and len(p) == 2, "invalid cell")
        result.append("(" + _int(p[0]) + ", " + _int(p[1]) + ")")
    require(len(set(result)) == len(result), "duplicate cell")
    return "([" + ", ".join(result) + "] : List Cell).toFinset"


def binding(claim):
    """Only finite literals and validated identifiers are emitted as Lean code."""
    values, conclusion, names = claim["values"], claim["conclusion"], claim["theorems"]
    require(conclusion["predicate"] == PREDICATE, "unsupported predicate meaning")
    for name in names.values():
        require(type(name) is str and re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)+", name),
                "invalid theorem identifier")
    bounds = values["square_bounds"]
    xmin, xmax, ymin, ymax = (_int(bounds[k]) for k in ("x_min", "x_max", "y_min", "y_max"))
    index = _nat(values["card_index"], 727)
    moves = _nat(conclusion["maker_claims_at_most"], 42)
    envelope_count, square_count = (_nat(conclusion[k]) for k in ("envelope_cells", "square_cells"))
    return f'''-- Generated by scripts/snaky_proof.py generate; checked without rewriting.
import SnakyFinite
namespace FiniteCongruenceChecks.SnakyFinite.Binding
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21
private def target : Finset Cell := {_points(values["target"])}
private def envelope : Finset Cell := {_points(values["envelope"])}
private def square : Finset Cell := (Finset.Icc ({xmin} : ℤ) {xmax}).product (Finset.Icc ({ymin} : ℤ) {ymax})
private def initialM : Finset Cell := {_points(values["initial_maker"])}
private def initialB : Finset Cell := {_points(values["initial_breaker"])}
private def targetWin (M : Finset Cell) : Prop := ∃ (r : Fin 8) (t : Cell), target.image (placement r t) ⊆ M
theorem target_exact : snaky = target := by decide +kernel
theorem envelope_exact : envelope_727 = envelope := by decide +kernel
theorem square_exact : square17 = square := by decide +kernel
theorem inputs_exact : initialM = ∅ ∧ initialB = ∅ ∧ ({index} : Nat) = 727 := by decide +kernel
theorem counts_exact : envelope.card = {envelope_count} ∧ square.card = {square_count} := by decide +kernel
private theorem win_exact : HasSnaky = targetWin := by
  funext M
  simp only [HasSnaky, targetWin, target_exact]
theorem checked_envelope : FiniteWins envelope targetWin {moves} initialM initialB := by
  rw [← envelope_exact, ← win_exact, inputs_exact.1, inputs_exact.2.1]
  exact {names["envelope"]}
theorem checked_square : FiniteWins square targetWin {moves} initialM initialB := by
  rw [← square_exact, ← win_exact, inputs_exact.1, inputs_exact.2.1]
  exact {names["square"]}
end FiniteCongruenceChecks.SnakyFinite.Binding
'''


def validate_project(root=ROOT):
    project = root / PROJECT
    require(not (project / "lakefile.lean").exists(), "unexpected executable Lake configuration")
    require((project / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.34.1", "wrong pinned toolchain")
    require(digest(project / "lake-manifest.json") == DEPENDENCY_MANIFEST_SHA256, "changed dependency manifest")
    require(digest(project / "vendor-manifest.json") == VENDOR_MANIFEST_SHA256, "changed upstream manifest")
    expected = ('name = "snakyFinite"\nversion = "0.1.0"\ndefaultTargets = ["SnakyFinite", "SnakyBinding"]\n'
                'moreLeanArgs = ["-j1"]\n\n[[require]]\nname = "mathlib"\n'
                'git = "https://github.com/leanprover-community/mathlib4.git"\n'
                'rev = "d13f23b723b8a846827a245b89c10fc7d3f11612"\n\n' +
                '\n'.join('[[lean_lib]]\nname = "' + m + '"\n' +
                          ('globs = ["' + m + '.+"]\n' if m in ("OAI", "FiniteCards") else '') for m in
                          ("OAI", "FiniteCards", "SnakySemantics", "SnakyFinite", "SnakyBinding")))
    require((project / "lakefile.toml").read_text().strip() == expected.strip(), "unreviewed Lake configuration")
    vendor = read(project / "vendor-manifest.json")
    require(vendor["commit"] == finite.UPSTREAM_COMMIT and vendor["repository"] == "https://github.com/openai/math", "wrong upstream identity")
    paths = {entry["path"] for entry in vendor["files"]}
    require(paths == {p.relative_to(project).as_posix() for p in (project / "OAI").rglob("*.lean")}, "upstream source inventory differs")
    for entry in vendor["files"]:
        payload = (project / entry["path"]).read_bytes()
        require(finite.raw_digest(payload) == entry["sha256"] and len(payload) == entry["bytes"], "upstream bytes changed: " + entry["path"])


def check_binding(root=ROOT):
    validate_project(root)
    claim = expected_claim(root)
    require(canonical(read(root / CLAIM_PATH)) == canonical(claim), "saved claim differs from exact registration")
    require((root / BINDING).read_text(encoding="utf-8") == binding(claim), "stale or altered Lean binding")
    return claim


def module_names(root=ROOT):
    """Local transitive imports of the bound theorem, in dependency order."""
    project = root / PROJECT
    visited, result = set(), []

    def visit(name):
        path = project / (name.replace(".", "/") + ".lean")
        if name in visited or not path.exists():
            return
        visited.add(name)
        for dependency in re.findall(r"^import ([A-Za-z_][A-Za-z_0-9.]*)$", path.read_text(encoding="utf-8"), re.M):
            visit(dependency)
        result.append(name)

    visit("SnakyBinding")
    require(len(result) == 179, "unexpected local proof import closure")
    return result


def source_hashes(root=ROOT):
    paths = ["scripts/snaky_proof.py", finite.SOURCE, finite.INPUT, CLAIM_PATH,
             PROJECT + "/lean-toolchain", PROJECT + "/lakefile.toml", PROJECT + "/lake-manifest.json",
             PROJECT + "/vendor-manifest.json", PROJECT + "/generate_finite_cards.py",
             PROJECT + "/UPSTREAM_LICENSE", PROJECT + "/UPSTREAM_NOTICE.md"]
    project = root / PROJECT
    paths += [PROJECT + "/" + entry["path"] for entry in read(project / "vendor-manifest.json")["files"]]
    paths += [p.relative_to(root).as_posix() for p in sorted((project / "FiniteCards").glob("*.lean"))]
    paths += [PROJECT + "/" + name + ".lean" for name in ("SnakySemantics", "SnakyFinite", "SnakyBinding")]
    return {path: digest(root / path) for path in paths}


def kernel_selectors(root=ROOT):
    # Pinned leanchecker rescans the complete search path for every selector.
    # Prefixes reduce that discovery work, not the set of modules replayed.
    base = "OAI.GameTheory.SnakyTwentyOne."
    selectors = [base + name for name in (
        "Model", "Semantics.Game", "Semantics.Geometry", "Certificate.Operations", "Cards")]
    selectors += ["FiniteCards", "SnakySemantics", "SnakyFinite", "SnakyBinding"]
    project = root / PROJECT
    sources = [p for folder in ("OAI", "FiniteCards") for p in (project / folder).rglob("*.lean")]
    sources += [project / (name + ".lean") for name in selectors[-3:]]
    available = {p.relative_to(project).with_suffix("").as_posix().replace("/", ".") for p in sources}
    selected = {name for name in available if any(
        name == prefix or name.startswith(prefix + ".") for prefix in selectors)}
    require(selected == set(module_names(root)), "kernel selectors differ from proof import closure")
    return selectors


def audit_kernel(log, root=ROOT):
    # These lines announce task waits, not completion. The caller must also
    # require exit zero; only then does the exact inventory describe a replay.
    modules = [line.removeprefix("replaying ") for line in log.splitlines() if line.startswith("replaying ")]
    require(sorted(modules) == sorted(module_names(root)), "missing, duplicate or unexpected kernel module")
    return modules


def controls(claim):
    changed = {}
    for name, mutate in (
        ("changed-target", lambda c: c["values"]["target"][5].__setitem__(0, 5)),
        ("changed-envelope", lambda c: c["values"]["envelope"][0].__setitem__(1, 3)),
        ("changed-square", lambda c: c["values"]["square_bounds"].__setitem__("x_max", 15)),
        ("wrong-move-bound", lambda c: c["conclusion"].__setitem__("maker_claims_at_most", 20)),
        ("wrong-card", lambda c: c["values"].__setitem__("card_index", 726)),
        ("nonempty-input", lambda c: c["values"].__setitem__("initial_maker", [[8, 8]])),
        ("unrelated-theorem", lambda c: c["theorems"].__setitem__("envelope", PREFIX + "square_wins")),
    ):
        candidate = copy.deepcopy(claim)
        mutate(candidate)
        changed[name] = binding(candidate)
    return changed


def audit_source():
    return "import SnakyBinding\n" + "".join("#print axioms " + n + "\n" for n in DECLARATIONS)


def audit_axioms(log):
    reports = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log)
    require(len(reports) == len(DECLARATIONS) and sorted(n for n, _ in reports) == sorted(DECLARATIONS), "missing or duplicate axiom report")
    result = {}
    for name, raw in reports:
        axioms = sorted(x.strip() for x in raw.split(",") if x.strip())
        require(set(axioms) <= ALLOWED_AXIOMS, "forbidden axiom for " + name + ": " + raw)
        result[name] = axioms
    return result


def negative_rejected(code, log):
    # An unavailable import/tool is not a successful mathematical rejection.
    setup_errors = ("unknown module", "unknown namespace", "unknown constant", "unknown identifier",
                    "object file", "does not exist", "no such file", "invalid import", "failed to synthesize",
                    "maximum recursion", "maximum number of heartbeats", "timeout", "stack overflow")
    return (type(code) is int and code > 0 and "error:" in log and
            not any(s in log.lower() for s in setup_errors) and
            any(s in log.lower() for s in ("type mismatch", "evaluated to false", "decide", "unsolved goals")))


def plan(claim, root=ROOT):
    return [("version", ["lake", "env", "lean", "--version"]),
            ("dependencies", ["lake", "exe", "cache", "get"]),
            ("build", ["lake", "build", "SnakyBinding"]),
            ("axioms", ["lake", "env", "lean", "{out}/Audit.lean"]),
            ("kernel", ["lake", "env", "leanchecker", "-v", *kernel_selectors(root)])
            ] + [(name, ["lake", "env", "lean", "{out}/" + name + ".lean"]) for name in controls(claim)]


def stage_timeout(name):
    if name == "build":
        return BUILD_TIMEOUT
    if name == "kernel":
        return KERNEL_TIMEOUT
    return DEFAULT_STAGE_TIMEOUT


def checkpoint(out, receipt):
    # A running receipt is diagnostic evidence, never a successful verification.
    # Exclude the receipt and its temporary file to avoid a self-referential hash.
    receipt["artifacts"] = {p.name: digest(p) for p in sorted(out.iterdir())
                            if p.is_file() and p.name not in {"summary.json", "summary.json.tmp"}}
    temporary = out / "summary.json.tmp"
    temporary.write_bytes(encode(receipt))
    os.replace(temporary, out / "summary.json")


def stop_process(proc):
    if os.name == "posix":
        # Popen below creates this process's own session/group. Never signal the
        # runner's group or discover unrelated processes by name.
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    elif proc.poll() is None:
        proc.kill()
    try:
        return proc.wait(timeout=10)
    except subprocess.TimeoutExpired:
        return None


def run_stage(name, command, *, root, out, receipt, negative=False):
    started = time.perf_counter()
    stage = {"name": name, "command": command, "cwd": PROJECT,
             "status": "running", "failure_kind": None, "exit_code": None,
             "timeout_seconds": stage_timeout(name), "duration_seconds": 0,
             "started_utc": datetime.now(timezone.utc).isoformat()}
    receipt["stages"].append(stage)
    checkpoint(out, receipt)
    proc = None
    try:
        # Streaming to a real file preserves output even if the runner or job is
        # interrupted, and avoids retaining a large compiler log in memory.
        with (out / (name + ".log")).open("wb") as log:
            proc = subprocess.Popen([arg.replace("{out}", str(out)) for arg in command],
                                    cwd=root / PROJECT, env={**os.environ, **ENVIRONMENT},
                                    stdout=log, stderr=subprocess.STDOUT,
                                    start_new_session=os.name == "posix")
            stage["exit_code"] = proc.wait(timeout=stage["timeout_seconds"])
        text = (out / (name + ".log")).read_text(encoding="utf-8", errors="replace")
        require(negative_rejected(stage["exit_code"], text) if negative else stage["exit_code"] == 0,
                "stage failed: " + name + "; see " + str(out))
        if name == "kernel":
            audit_kernel(text, root)
        stage["status"] = "passed"
    except BaseException as error:
        stage["status"] = "failed"
        stage["failure_kind"] = ("timeout" if isinstance(error, subprocess.TimeoutExpired) else
                                 "interrupted" if isinstance(error, (KeyboardInterrupt, SystemExit)) or
                                 (type(stage["exit_code"]) is int and stage["exit_code"] < 0) else
                                 "verification" if isinstance(error, ValueError) else "execution")
        stage["error"] = str(error)
        if proc is not None:
            # A failed parent may already have exited while its helpers remain.
            # Clean up the owned group, retaining the parent's original result.
            stopped_code = stop_process(proc)
            if stage["exit_code"] is None:
                stage["exit_code"] = stopped_code
        raise
    finally:
        stage["duration_seconds"] = round(time.perf_counter() - started, 3)
        stage["finished_utc"] = datetime.now(timezone.utc).isoformat()
        checkpoint(out, receipt)
    return stage


def replay(out=None, root=ROOT):
    root = Path(root)
    out = root / RECEIPT if out is None else Path(out)
    claim = check_binding(root)
    receipt = read(out / "summary.json")
    require(type(receipt["schema_version"]) is int and receipt["schema_version"] == 1 and receipt["status"] == "passed", "run did not pass")
    require(canonical(receipt["claim"]) == canonical(claim) and receipt["limits"] == LIMITS, "receipt claim differs")
    require(receipt["hash_encoding"] == finite.HASH_ENCODING, "wrong hash encoding")
    require(receipt["environment_overrides"] == ENVIRONMENT, "wrong verification environment")
    require(receipt["source_hashes"] == source_hashes(root), "source changed after verification")
    require(receipt["computational_evidence"] == {"path": finite.OUTPUT, "sha256": digest(root / finite.OUTPUT)},
            "computational evidence reference differs")
    finite.replay(root=root)
    expected, negative = plan(claim, root), controls(claim)
    require(len(receipt["stages"]) == len(expected), "missing stages")
    for actual, (name, command) in zip(receipt["stages"], expected):
        require(actual["name"] == name and actual["command"] == command and actual["cwd"] == PROJECT, "wrong verification command")
        require(actual["status"] == "passed" and actual["failure_kind"] is None, "stage did not complete: " + name)
        require(type(actual["timeout_seconds"]) is int and actual["timeout_seconds"] == stage_timeout(name),
                "wrong stage timeout: " + name)
        code = actual["exit_code"]
        require(type(code) is int, "wrong exit code type")
        log = (out / (name + ".log")).read_text(encoding="utf-8")
        require(negative_rejected(code, log) if name in negative else code == 0, "stage failed: " + name)
        if name == "kernel":
            audit_kernel(log, root)
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
               "environment_overrides": ENVIRONMENT,
               "computational_evidence": {"path": finite.OUTPUT, "sha256": digest(root / finite.OUTPUT)},
               "stages": [], "artifacts": {}, "started_utc": datetime.now(timezone.utc).isoformat()}
    checkpoint(out, receipt)
    try:
        for name, command in plan(claim, root):
            print("Checking " + name, flush=True)
            run_stage(name, command, root=root, out=out, receipt=receipt, negative=name in negative)
        require(before == source_hashes(root), "source changed during proof run")
        receipt["axioms"] = audit_axioms((out / "axioms.log").read_text(encoding="utf-8"))
        receipt["finished_utc"] = datetime.now(timezone.utc).isoformat()
        receipt["status"] = "passed"
        checkpoint(out, receipt)
        replay(out, root)
    except BaseException:
        receipt["status"] = "failed"
        receipt["finished_utc"] = datetime.now(timezone.utc).isoformat()
        checkpoint(out, receipt)
        raise
    return receipt


def explain(root=ROOT):
    receipt = replay(root=root)
    claim = copy.deepcopy(receipt["claim"])
    claim["proof_evidence"] = {"path": RECEIPT + "/summary.json", "sha256": digest(root / RECEIPT / "summary.json"),
                               "axioms": receipt["axioms"], "validation": "saved receipt replay; no Lean execution during query"}
    claim["computational_evidence"] = {"path": finite.OUTPUT, "sha256": digest(root / finite.OUTPUT),
                                       "validation": "independent reconstruction of the exact 728-card certificate; Python correctness is not formally proved"}
    return {"id": CLAIM_ID, "path": CLAIM_PATH, "sha256": digest(root / CLAIM_PATH)}, claim


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["generate", "run", "replay"])
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    if args.command == "generate":
        claim = expected_claim()
        (ROOT / CLAIM_PATH).write_bytes(encode(claim))
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
