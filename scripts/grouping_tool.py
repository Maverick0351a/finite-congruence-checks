"""Check a proposal with an identified native build and save claim evidence.

The admission checks are reproducibility checks, not signatures or a machine-code
proof. Run run_grouping_checks.py to reproduce the proof and native test receipt.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

from grouping_reference import decode, evaluate, repair_grouping

ROOT = Path(__file__).resolve().parents[1]
CONTRACT = "specs/unary-grouping-v1.json"
SCHEMA = "specs/grouping-result-v1.schema.json"
CORE = "lean/GroupingChecker.lean"
REQUIRED_SOURCES = {
    CONTRACT, SCHEMA, CORE, "lean/GroupingMain.lean", "lean/GroupingAudit.lean",
    "lean/lakefile.toml", "lean/lean-toolchain", "scripts/grouping_reference.py",
    "scripts/run_grouping_checks.py", "scripts/grouping_tool.py",
}
ASSUMPTIONS = [
    "Four objects, one total unary operation, and equality of the four group labels.",
    "Lean 4.34.1 kernel replay and the recorded standard-axiom audit support the source theorem.",
    "The native receipt relies on the recorded compiler, runtime, operating environment, and independent test harness.",
]
LIMITS = [
    "Executable agreement covers this binary and all 65536 encoded words in the recorded environment; it is not a machine-code refinement proof.",
    "The claim concerns this exact operation and grouping; it does not identify the whole congruence family or prove search completeness or minimality.",
    "Artifact hashes identify bytes and detect changes; they do not authenticate an author's claims. Reproduce the run to check those claims.",
]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def artifact(name: str, root: Path = ROOT) -> Path:
    require(type(name) is str and bool(name), "artifact path must be a nonempty string")
    require(not Path(name).is_absolute() and "\\" not in name and ":" not in name,
            "artifact path must be relative POSIX syntax")
    path = (root / name).resolve()
    require(path.is_relative_to(root.resolve()), "artifact path escapes its evidence root")
    require(path.is_file(), f"missing artifact: {name}")
    return path


def relative(path: Path) -> str:
    return path.resolve().relative_to(ROOT).as_posix()


def read_json(path: Path):
    def unique(items):
        result = {}
        for key, value in items:
            require(key not in result, f"duplicate JSON key: {key}")
            result[key] = value
        return result
    return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=unique)


def schema_check(value, schema: dict, document: dict, at: str = "$") -> None:
    """Enforce the keywords used by the frozen result schema, without a dependency."""
    if "$ref" in schema:
        schema = document["$defs"][schema["$ref"].split("/")[-1]]
    kinds = {"object": dict, "array": list, "integer": int, "boolean": bool,
             "string": str, "null": type(None)}
    if "type" in schema:
        require(type(value) is kinds[schema["type"]], f"{at}: wrong type")
    if "const" in schema:
        require(type(value) is type(schema["const"]) and value == schema["const"], f"{at}: wrong constant")
    if "enum" in schema:
        require(value in schema["enum"], f"{at}: unsupported value")
    if isinstance(value, dict):
        require(set(schema.get("required", [])) <= value.keys(), f"{at}: missing field")
        properties = schema.get("properties", {})
        if schema.get("additionalProperties") is False:
            require(value.keys() <= properties.keys(), f"{at}: unknown field")
        for key in value.keys() & properties.keys():
            schema_check(value[key], properties[key], document, f"{at}.{key}")
    if isinstance(value, list):
        require(schema.get("minItems", 0) <= len(value) <= schema.get("maxItems", len(value)), f"{at}: wrong array size")
        if "items" in schema:
            for i, item in enumerate(value):
                schema_check(item, schema["items"], document, f"{at}[{i}]")
    if isinstance(value, str):
        require(len(value) >= schema.get("minLength", 0), f"{at}: empty string")
        if "pattern" in schema:
            require(re.fullmatch(schema["pattern"], value) is not None, f"{at}: invalid format")
    if type(value) is int:
        require(schema.get("minimum", value) <= value <= schema.get("maximum", value), f"{at}: out of range")
    if "oneOf" in schema:
        matches = 0
        for branch in schema["oneOf"]:
            try:
                schema_check(value, branch, document, at)
                matches += 1
            except ValueError:
                pass
        require(matches == 1, f"{at}: no unique schema alternative")
    for branch in schema.get("allOf", []):
        schema_check(value, branch, document, at)
    if "if" in schema:
        try:
            schema_check(value, schema["if"], document, at)
            selected = "then"
        except ValueError:
            selected = "else"
        schema_check(value, schema.get(selected, {}), document, at)


def encode_proposal(value: dict) -> int:
    require(type(value) is dict and set(value) == {"operation", "group_labels"},
            "invalid_input: expected exactly operation and group_labels")
    digits = []
    for key in ("operation", "group_labels"):
        require(type(value[key]) is list and len(value[key]) == 4,
                f"invalid_input: {key} must have four entries")
        for item in value[key]:
            require(type(item) is int and 0 <= item <= 3,
                    "invalid_input: entries must be integers from 0 to 3; booleans are invalid")
            digits.append(item)
    return sum(digit * 4 ** position for position, digit in enumerate(digits))


def load_receipt(path: Path) -> tuple[dict, dict[int, dict], Path]:
    """Validate current source bindings and independently replay every saved output."""
    from run_grouping_checks import EXPECTED_DECLARATIONS, validate_axioms, validate_records
    path = artifact(relative(path))
    receipt = read_json(path)
    require(receipt.get("passed") is True, "receipt did not pass")
    require(receipt.get("contract_id") == "unary-grouping-v1", "receipt contract mismatch")
    require(receipt.get("sources_unchanged") is True, "sources changed during run")
    require(receipt.get("source_tree_dirty") is False, "evidenced results require a committed source tree")
    require(receipt.get("run_problems") == [], "receipt has run problems")
    manifest = receipt["source_manifest"]
    require(REQUIRED_SOURCES <= manifest.keys(), "receipt lacks required source bindings")
    require(manifest == receipt["source_manifest_after"], "source manifests disagree")
    for name, digest in manifest.items():
        require(sha256(artifact(name)) == digest, f"stale source artifact: {name}")
    require(re.fullmatch("[0-9a-f]{40}", receipt["source_revision"]) is not None,
            "receipt needs a full source revision")
    proof = receipt["proof_status"]
    require(all(proof.get(key) is True for key in ("build", "kernel_replay", "axioms")),
            "source proof checks incomplete")
    require(proof.get("expected_declarations") == list(EXPECTED_DECLARATIONS), "wrong theorem set")
    commands = {command["name"]: command for command in receipt["commands"]}
    require(len(commands) == len(receipt["commands"]), "duplicate recorded command")
    for command in commands.values():
        for channel in ("stdout", "stderr"):
            require(sha256(artifact(command[f"{channel}_path"], path.parent)) == command[f"{channel}_sha256"],
                    "recorded command log hash mismatch")
    for name in ("build", "kernel-replay", "axioms", "native-all"):
        require(commands[name]["exit_code"] == 0, f"required command failed: {name}")
    require(commands["git-revision"]["exit_code"] == commands["git-status"]["exit_code"] == 0,
            "Git provenance commands failed")
    require(artifact(commands["git-revision"]["stdout_path"], path.parent).read_text(encoding="utf-8").strip()
            == receipt["source_revision"], "revision does not match Git log")
    require(not artifact(commands["git-status"]["stdout_path"], path.parent).read_text(encoding="utf-8").strip(),
            "Git status log records uncommitted changes")
    axiom_log = artifact(commands["axioms"]["stdout_path"], path.parent).read_text(encoding="utf-8")
    require(validate_axioms(axiom_log) == proof["axiom_reports"] and proof["axiom_reports"]["passed"] is True,
            "axiom report does not match the saved audit")
    require(receipt["toolchain"]["matches_pin"] is True and
            receipt["toolchain"]["pinned"] == "leanprover/lean4:v4.34.1", "wrong toolchain")
    require(receipt["binary"]["matches_build_artifact"] is True and
            receipt["binary"]["unchanged_during_checks"] is True, "binary provenance is inconsistent")
    binary = receipt["binary"]
    require(binary["sha256"] == binary["build_artifact_sha256"] == binary["sha256_after"],
            "binary digests disagree")
    archive = binary["archive"]
    require(archive["raw_sha256"] == binary["sha256"] and archive["raw_size_bytes"] == binary["size_bytes"],
            "binary archive identifiers disagree")
    # Large executables are release assets, so a source checkout may omit them.
    # Offline validation checks identifiers; a live check always hashes its binary.
    archive_path = path.parent / archive["path"]
    if archive_path.exists():
        archive_path = artifact(archive["path"], path.parent)
        require(sha256(archive_path) == archive["sha256"], "binary archive hash mismatch")
        digest = hashlib.sha256()
        length = 0
        with gzip.open(archive_path, "rb") as handle:
            for block in iter(lambda: handle.read(1024 * 1024), b""):
                length += len(block)
                digest.update(block)
        require(digest.hexdigest() == binary["sha256"] and length == binary["size_bytes"],
                "uncompressed binary archive mismatch")
    require(receipt["adapter_tests"] and all(case["passed"] is True for case in receipt["adapter_tests"]),
            "adapter tests incomplete")
    coverage = receipt["coverage"]
    require(coverage.get("full_domain") is True and
            coverage.get("actual_tested_count") == coverage.get("distinct_word_count") == 65536,
            "receipt is not an exhaustive run")
    require(receipt.get("disagreements") == [], "receipt has disagreements")
    transcript = receipt["transcript"]
    transcript_path = artifact(transcript["path"], path.parent)
    require(sha256(transcript_path) == transcript["sha256"], "native transcript hash mismatch")
    with gzip.open(transcript_path, "rb") as handle:
        raw = handle.read()
    require(hashlib.sha256(raw).hexdigest() == transcript["raw_sha256"], "raw transcript hash mismatch")
    from run_grouping_checks import _unique_object
    records = [json.loads(line, object_pairs_hook=_unique_object) for line in raw.splitlines()]
    checked = validate_records(records)
    require(checked["coverage"]["full_domain"] is True and not checked["disagreements"],
            "saved native transcript fails independent comparison")
    return receipt, {row["word"]: row for row in records}, transcript_path


def result_record(word: int, receipt_path: Path, receipt: dict, row: dict, transcript_path: Path) -> dict:
    operation, labels = decode(word)
    exact_id = f"ug4-v1:{word:04x}"
    return {
        "schema_version": 1, "status": "evidenced_result", "input_id": exact_id,
        "input": {"word": word, "hex": f"{word:04x}", "operation": operation, "group_labels": labels},
        "claim_id": f"preservation:{exact_id}", "claim_kind": "unary_grouping_preservation",
        "specification": {"contract_id": "unary-grouping-v1", "version": 1,
                          "artifact_path": CONTRACT, "artifact_sha256": sha256(artifact(CONTRACT))},
        "checker": {"version": "1", "source_revision": receipt["source_revision"],
                    "source_sha256": receipt["source_manifest"][CORE],
                    "theorem_declaration": "GroupingChecker.check_iff",
                    "binary_sha256": receipt["binary"]["sha256"]},
        "outcome": {"preserves": row["preserves"], "violating_pair": row["violating_pair"]},
        "evidence": [
            {"kind": "source_proof", "artifact_path": relative(receipt_path),
             "artifact_sha256": sha256(receipt_path), "case_pointer": "/proof_status"},
            {"kind": "bounded_executable_agreement", "artifact_path": relative(transcript_path),
             "artifact_sha256": sha256(transcript_path), "case_pointer": f"jsonl:word={word}"},
        ],
        "assumptions": ASSUMPTIONS.copy(), "limits": LIMITS.copy(),
    }


def validate_result(record: dict, cached=None) -> None:
    schema = read_json(artifact(SCHEMA))
    schema_check(record, schema, schema)
    word = record["input"]["word"]
    evidence = record["evidence"]
    require([item["kind"] for item in evidence] == ["source_proof", "bounded_executable_agreement"],
            "evidence must contain source proof followed by bounded executable agreement")
    for item in evidence:
        require(sha256(artifact(item["artifact_path"])) == item["artifact_sha256"], "evidence hash mismatch")
    receipt_path = artifact(evidence[0]["artifact_path"])
    receipt, rows, transcript_path = cached or load_receipt(receipt_path)
    expected = result_record(word, receipt_path, receipt, rows[word], transcript_path)
    require(record == expected, "record disagrees with the exact input, native transcript, or required claim limits")
    reference = evaluate(word)
    require(record["outcome"]["preserves"] is reference["preserves"], "outcome disagrees with reference")


def check_native(word: int, binary: Path, receipt_path: Path, cached) -> dict:
    decode(word)  # Strict input boundary before any process launch.
    receipt, rows, transcript_path = cached
    require(sha256(binary) == receipt["binary"]["sha256"], "selected binary does not match receipt")
    process = subprocess.run([str(binary.resolve()), str(word)], capture_output=True, text=True, timeout=30)
    require(process.returncode == 0 and not process.stderr, "native checker failed")
    lines = process.stdout.splitlines()
    require(len(lines) == 1, "native checker returned an unexpected number of records")
    actual = json.loads(lines[0])
    require(actual == rows[word], "native result differs from the saved exhaustive run")
    record = result_record(word, receipt_path, receipt, actual, transcript_path)
    validate_result(record, cached)
    return record


def run_demo(binary: Path, receipt_path: Path, cached) -> dict:
    proposal = {"operation": [0, 2, 2, 3], "group_labels": [0, 0, 1, 2]}
    first_word = encode_proposal(proposal)
    before = check_native(first_word, binary, receipt_path, cached)
    require(before["outcome"] == {"preserves": False, "violating_pair": [0, 1]}, "demo needs the expected counterexample")
    repaired_word = repair_grouping(first_word)
    after = check_native(repaired_word, binary, receipt_path, cached)
    require(after["outcome"]["preserves"] is True, "repair failed verification")
    require(before["input"]["operation"] == after["input"]["operation"], "repair changed the rule")
    require(len(set(after["input"]["group_labels"])) == 2, "demo repair must retain two blocks")
    return {
        "schema_version": 1, "demo_kind": "deterministic_propose_counterexample_repair_recheck",
        "description": "An agent can use this protocol; this saved replay uses a fixed proposal and deterministic repair, with no LLM benchmark claim.",
        "steps": [
            {"action": "propose", "proposal": proposal},
            {"action": "check", "result": before},
            {"action": "repair", "method": "merge conflicting output blocks using grouping_reference.repair_grouping; repair logic is not formally proved",
             "explanation": "0 and 1 start together. Their outputs 0 and 2 are apart. Merge the blocks containing 0 and 2, leaving 3 separate.",
             "proposal": {"operation": after["input"]["operation"], "group_labels": after["input"]["group_labels"]}},
            {"action": "recheck", "result": after},
        ],
        "accepted_input_id": after["input_id"],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    for name in ("check", "demo"):
        sub = subparsers.add_parser(name)
        sub.add_argument("--receipt", required=True, type=Path)
        sub.add_argument("--binary", type=Path, default=ROOT / "lean/.lake/build/bin/grouping_checker")
        sub.add_argument("--out", type=Path)
        if name == "check":
            source = sub.add_mutually_exclusive_group(required=True)
            source.add_argument("--word", type=int, help="decimal integer 0..65535")
            source.add_argument("--input-json", type=Path, help="JSON object with four operation outputs and four group labels")
    validate = subparsers.add_parser("validate")
    validate.add_argument("record", type=Path)
    args = parser.parse_args()
    try:
        if args.command == "validate":
            record = read_json(args.record)
            validate_result(record)
            receipt_path = artifact(record["evidence"][0]["artifact_path"])
            receipt = read_json(receipt_path)
            available = (receipt_path.parent / receipt["binary"]["archive"]["path"]).is_file()
            result = {"status": "validated", "record": str(args.record),
                      "binary_archive_checked": available,
                      "scope": "source/log/transcript consistency; native execution requires check"}
        else:
            word = None
            if args.command == "check":
                word = encode_proposal(read_json(args.input_json)) if args.input_json else args.word
                decode(word)
            receipt_path = args.receipt.resolve()
            cached = load_receipt(receipt_path)
            result = (run_demo(args.binary, receipt_path, cached) if args.command == "demo"
                      else check_native(word, args.binary, receipt_path, cached))
        serialized = json.dumps(result, indent=2, sort_keys=True) + "\n"
        if getattr(args, "out", None):
            require(not args.out.exists(), "output already exists; choose a new path")
            args.out.parent.mkdir(parents=True, exist_ok=True)
            args.out.write_text(serialized, encoding="utf-8", newline="\n")
        print(serialized, end="")
        return 0
    except (ValueError, TypeError, KeyError, OSError, subprocess.SubprocessError) as error:
        print(json.dumps({"status": "error", "message": str(error)}), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
