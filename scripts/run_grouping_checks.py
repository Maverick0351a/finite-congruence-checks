"""Preserve and independently compare the native unary-grouping checker.

The frozen grouping_reference.py was authored from unary-grouping-v1.json
before its author read the Lean implementation. This integration harness was
written afterwards. Both implementations use base-4 decoding; the reference
checks block image sets, while Lean scans pairs. The reference is executable
code, not a formally proved specification. Agreement is evidence about the
saved executable on this finite domain, not a machine-code refinement proof.

Run from a checkout with its pinned Lake toolchain available on PATH:
    python scripts/run_grouping_checks.py --out runs/grouping-check-001

The output directory must be absent or empty. Source files are never changed.
Lake may replay cached build commands: preserved trace files record the actual
compile/link settings, and this script does not call a replay a fresh compile.
"""

from __future__ import annotations

import argparse
from collections import Counter
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import tempfile
from typing import Iterable


ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
INPUT_COUNT = 65536
EXPECTED_DECLARATIONS = tuple("GroupingChecker." + name for name in (
    "decode_operation_bits", "decode_label_bits", "encode_decode",
    "decode_encode", "decodeInt_invalid", "decodeInt_value", "decodeInt_valid",
    "labels_equivalence", "check_iff", "witness_sound", "rejected_has_witness",
))
ALLOWED_AXIOMS = frozenset(("propext", "Classical.choice", "Quot.sound"))
SOURCE_FILES = (
    "specs/unary-grouping-v1.json", "specs/grouping-result-v1.schema.json",
    "scripts/grouping_reference.py", "scripts/test_grouping_reference.py",
    "scripts/run_grouping_checks.py", "scripts/test_grouping_checks.py",
    "scripts/grouping_tool.py", "scripts/test_grouping_tool.py",
    "lean/GroupingChecker.lean", "lean/GroupingMain.lean",
    "lean/GroupingAudit.lean", "lean/lakefile.toml",
    "lean/lake-manifest.json", "lean/lean-toolchain",
)

_reference_spec = importlib.util.spec_from_file_location(
    "grouping_reference_for_native_comparison", ROOT / "scripts/grouping_reference.py"
)
assert _reference_spec is not None and _reference_spec.loader is not None
reference = importlib.util.module_from_spec(_reference_spec)
_reference_spec.loader.exec_module(reference)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def manifest(root: Path = ROOT) -> dict[str, str | None]:
    """Hash exact bytes; an absent required source is recorded explicitly."""
    return {name: sha256(root / name) if (root / name).is_file() else None
            for name in SOURCE_FILES}


def gzip_artifact(source: Path, destination: Path) -> dict:
    """Save deterministic gzip bytes: no original name and mtime exactly zero."""
    with source.open("rb") as raw, destination.open("wb") as target:
        with gzip.GzipFile(filename="", mode="wb", fileobj=target, mtime=0) as compressed:
            shutil.copyfileobj(raw, compressed, length=1024 * 1024)
    return {
        "path": destination.name, "format": "gzip", "mtime": 0,
        "sha256": sha256(destination), "size_bytes": destination.stat().st_size,
        "raw_sha256": sha256(source), "raw_size_bytes": source.stat().st_size,
    }


class InvalidJsonLine:
    def __init__(self, raw: str, error: str):
        self.raw = raw
        self.error = error


def _unique_object(pairs: list[tuple[str, object]]) -> dict:
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON object key: {key}")
        result[key] = value
    return result


def read_jsonl(path: Path) -> Iterable[object]:
    """Keep malformed/blank lines visible to validation instead of skipping."""
    with path.open("rb") as stream:
        for raw in stream:
            try:
                text = raw.decode("utf-8")
                yield json.loads(text, object_pairs_hook=_unique_object,
                                 parse_constant=lambda value: (_ for _ in ()).throw(
                                     ValueError(f"non-JSON number: {value}")))
            except (UnicodeDecodeError, ValueError) as error:
                yield InvalidJsonLine(raw.decode("utf-8", errors="replace"), str(error))


def _digits_equal(actual: object, expected: list[int]) -> bool:
    return (type(actual) is list and len(actual) == 4
            and all(type(value) is int for value in actual) and actual == expected)


def validate_records(records: Iterable[object],
                     expected_words: Iterable[int] = range(INPUT_COUNT)) -> dict:
    """Validate coverage, decoded inputs, result, and mathematical witnesses.

    Expected words may be narrowed by harness tests; a production --all run
    always uses the complete 16-bit domain. Every detected mismatch is kept.
    Pair selection is intentionally independent of the reference's pair choice.
    """
    expected = set(expected_words)
    if any(type(word) is not int or not 0 <= word < INPUT_COUNT for word in expected):
        raise ValueError("expected_words must contain integers in 0..65535")
    counts: Counter[int] = Counter()
    disagreements = []
    total_records = 0
    checked_records = 0

    def problem(index, word, kind, wanted, actual):
        disagreements.append({"record_index": index, "word": word, "kind": kind,
                              "expected": wanted, "actual": actual})

    for index, record in enumerate(records):
        total_records += 1
        if isinstance(record, InvalidJsonLine):
            problem(index, None, "invalid_json", "one JSON object per line",
                    {"raw": record.raw, "error": record.error})
            continue
        if type(record) is not dict:
            problem(index, None, "record_type", "object", record)
            continue
        word = record.get("word")
        if type(word) is not int or not 0 <= word < INPUT_COUNT:
            problem(index, None, "invalid_word", "integer in 0..65535", record)
            continue
        counts[word] += 1
        if record.get("status") != "checked":
            problem(index, word, "status", "checked", record.get("status"))
        else:
            checked_records += 1
        if word not in expected:
            problem(index, word, "unexpected_word", sorted(expected), word)
        if counts[word] > 1:
            problem(index, word, "duplicate_word", "one record", record)

        operation, labels = reference.decode(word)
        result = reference.evaluate(word)
        for field, wanted in (("operation", operation), ("group_labels", labels)):
            if not _digits_equal(record.get(field), wanted):
                problem(index, word, field, wanted, record.get(field))
        if type(record.get("roundtrip_word")) is not int or record["roundtrip_word"] != word:
            problem(index, word, "roundtrip_word", word, record.get("roundtrip_word"))
        if type(record.get("preserves")) is not bool or record["preserves"] != result["preserves"]:
            problem(index, word, "preserves", result, record)

        pair = record.get("violating_pair")
        if "violating_pair" not in record:
            problem(index, word, "missing_violating_pair", "explicit pair or null", None)
        elif result["preserves"]:
            if pair is not None:
                problem(index, word, "unexpected_witness", None, pair)
        else:
            good_pair = (type(pair) is list and len(pair) == 2
                         and all(type(v) is int and 0 <= v < 4 for v in pair))
            if good_pair:
                x, y = pair
                good_pair = labels[x] == labels[y] and labels[operation[x]] != labels[operation[y]]
            if not good_pair:
                problem(index, word, "invalid_witness", {
                    "condition": "g[x] = g[y] and g[f[x]] != g[f[y]]",
                    "reference_example": result["violating_pair"],
                }, pair)

    observed = set(counts)
    missing = sorted(expected - observed)
    for word in missing:
        operation, labels = reference.decode(word)
        problem(None, word, "missing_word", {
            "operation": operation, "group_labels": labels, **reference.evaluate(word)
        }, None)
    coverage = {
        "expected_word_count": len(expected),
        "total_output_records": total_records,
        "actual_tested_count": checked_records,
        "distinct_word_count": len(observed),
        "minimum_word": min(observed) if observed else None,
        "maximum_word": max(observed) if observed else None,
        "missing_words": missing,
        "unexpected_words": sorted(observed - expected),
        "duplicate_words": [{"word": word, "count": count}
                            for word, count in sorted(counts.items()) if count > 1],
        "full_domain": (expected == set(range(INPUT_COUNT)) and observed == expected
                        and total_records == checked_records == INPUT_COUNT
                        and all(count == 1 for count in counts.values())),
        "expected_coverage_complete": (observed == expected
                                      and total_records == checked_records == len(expected)
                                      and all(count == 1 for count in counts.values())),
        "count_definition": "actual_tested_count counts in-range records with status checked, including repeats and records with other invalid fields; distinct_word_count counts distinct in-range words in all parsed objects; both are separate from successful validation",
    }
    return {"coverage": coverage, "disagreements": disagreements}


def validate_axioms(text: str) -> dict:
    pattern = re.compile(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)")
    reports = []
    for match in pattern.finditer(text):
        axioms = [] if match.group(2) is None else [
            value.strip() for value in match.group(2).split(",") if value.strip()
        ]
        reports.append({"declaration": match.group(1), "axioms": axioms})
    names = Counter(report["declaration"] for report in reports)
    forbidden = sorted({axiom for report in reports for axiom in report["axioms"]
                        if axiom not in ALLOWED_AXIOMS})
    missing = sorted(set(EXPECTED_DECLARATIONS) - set(names))
    unexpected = sorted(set(names) - set(EXPECTED_DECLARATIONS))
    duplicates = sorted(name for name, count in names.items() if count != 1)
    return {
        "passed": (len(reports) == len(EXPECTED_DECLARATIONS) and not
                   (forbidden or missing or unexpected or duplicates)),
        "expected_declarations": list(EXPECTED_DECLARATIONS), "reports": reports,
        "allowed_axioms": sorted(ALLOWED_AXIOMS), "forbidden_axioms": forbidden,
        "missing_declarations": missing, "unexpected_declarations": unexpected,
        "duplicate_declarations": duplicates,
    }


class Capture:
    def __init__(self, out: Path):
        self.out = out
        self.commands: list[dict] = []
        (out / "logs").mkdir()

    def run(self, name: str, argv: list[str], cwd: Path = LEAN) -> dict:
        stdout = self.out / "logs" / f"{name}.stdout.txt"
        stderr = self.out / "logs" / f"{name}.stderr.txt"
        item = {"name": name, "argv": [str(arg) for arg in argv], "cwd": str(cwd)}
        with stdout.open("wb") as output, stderr.open("wb") as errors:
            try:
                process = subprocess.run(item["argv"], cwd=cwd, stdout=output,
                                         stderr=errors, check=False)
                item["exit_code"] = process.returncode
            except OSError as error:
                errors.write(str(error).encode("utf-8"))
                item["exit_code"] = None
                item["launch_error"] = str(error)
        item.update({
            "stdout_path": stdout.relative_to(self.out).as_posix(),
            "stdout_sha256": sha256(stdout),
            "stderr_path": stderr.relative_to(self.out).as_posix(),
            "stderr_sha256": sha256(stderr),
        })
        self.commands.append(item)
        return item

    def stdout(self, command: dict) -> str:
        return (self.out / command["stdout_path"]).read_text(encoding="utf-8", errors="replace")


def git_prefix(capture: Capture) -> list[str]:
    """Prefer native Git; allow an installed Windows Git in a WSL checkout."""
    native = shutil.which("git")
    if native:
        return [native]
    windows_git = shutil.which("git.exe")
    if windows_git and platform.system() != "Windows" and shutil.which("wslpath"):
        conversion = capture.run("git-path-conversion", ["wslpath", "-w", str(ROOT)], ROOT)
        converted = capture.stdout(conversion).strip()
        if conversion["exit_code"] == 0 and converted:
            return [windows_git, "-C", converted]
    return [windows_git or "git"]


def collect_build_artifacts(out: Path, lean_root: Path = LEAN,
                            source_root: Path = ROOT) -> list[dict]:
    """Keep Lake's actual saved compile/link trace and response-file bytes."""
    records = []
    build = lean_root / ".lake/build"
    if not build.is_dir():
        return records
    candidates = sorted(path for path in build.rglob("*") if path.is_file()
                        and path.name.startswith(("GroupingChecker.", "GroupingMain.", "grouping_checker."))
                        and (path.name.endswith((".trace", ".rsp", ".setup.json", ".c", ".olean"))))
    for path in candidates:
        record = {"source_path": path.relative_to(source_root).as_posix(),
                  "sha256": sha256(path), "size_bytes": path.stat().st_size}
        if path.name.endswith((".trace", ".rsp", ".setup.json")):
            target = out / "build-traces" / path.relative_to(build)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, target)
            record["path"] = target.relative_to(out).as_posix()
        records.append(record)
    return records


def mutate_wrapper_source(source: bytes) -> bytes:
    """Invert exactly the serialized result field, leaving the checker alone."""
    original = b'("preserves", toJson (check w))'
    replacement = b'("preserves", toJson (!(check w)))'
    if source.count(original) != 1:
        raise ValueError("wrapper mutation requires exactly one expected preserves serialization")
    return source.replace(original, replacement, 1)


def run_wrapper_mutation(capture: Capture) -> dict:
    """Compile an isolated wrapper fault and require every result to disagree.

    The check function and its proved source are unchanged. Only the JSON
    output's preserves field is negated. All disagreements are saved separately
    so an intentionally failing control cannot be mistaken for the real run.
    """
    saved = capture.out / "wrapper-mutation"
    (saved / "source").mkdir(parents=True)
    result = {
        "kind": "compiled_wrapper_output_fault", "passed": False,
        "mutation": "Negate only the emitted preserves field; checker and witness logic unchanged.",
        "scope": "Tests detection of a compiled output-wrapper fault; does not mutate the proved check function or establish machine-code refinement.",
    }
    try:
        mutated = mutate_wrapper_source((LEAN / "GroupingMain.lean").read_bytes())
    except ValueError as error:
        result["error"] = str(error)
        return result
    # A separate small Lake project avoids changing or rebuilding the real source.
    sources = {
        "GroupingChecker.lean": (LEAN / "GroupingChecker.lean").read_bytes(),
        "GroupingMain.lean": mutated,
        "lean-toolchain": (LEAN / "lean-toolchain").read_bytes(),
        "lakefile.toml": b'name = "groupingWrapperFault"\nversion = "0.1.0"\n\n[[lean_lib]]\nname = "GroupingChecker"\n\n[[lean_exe]]\nname = "grouping_checker"\nroot = "GroupingMain"\n',
    }
    for name, data in sources.items():
        (saved / "source" / name).write_bytes(data)
    result["source_manifest"] = {
        f"wrapper-mutation/source/{name}": sha256(saved / "source" / name)
        for name in sources
    }
    result["original_wrapper_sha256"] = sha256(LEAN / "GroupingMain.lean")
    with tempfile.TemporaryDirectory(prefix="grouping-wrapper-fault-") as directory:
        staging = Path(directory)
        for name, data in sources.items():
            (staging / name).write_bytes(data)
        build = capture.run("wrapper-fault-build", ["lake", "-v", "build", "grouping_checker"], staging)
        result["build_command"] = build["name"]
        result["build_exit_code"] = build["exit_code"]
        traces = collect_build_artifacts(saved, staging, staging)
        for record in traces:
            if "path" in record:
                record["path"] = "wrapper-mutation/" + record["path"]
        result["build_trace_artifacts"] = traces
        mutant = staging / ".lake/build/bin" / ("grouping_checker.exe" if platform.system() == "Windows" else "grouping_checker")
        if build["exit_code"] != 0 or not mutant.is_file():
            result["error"] = "The isolated wrapper fault failed to compile."
            return result
        archive = gzip_artifact(mutant, saved / "binary.gz")
        archive["path"] = "wrapper-mutation/" + archive["path"]
        result["binary"] = {"sha256": sha256(mutant), "size_bytes": mutant.stat().st_size,
                            "archive": archive}
        native = capture.run("wrapper-fault-all", [str(mutant), "--all"], staging)
        result["native_command"] = native["name"]
        result["native_exit_code"] = native["exit_code"]
        raw = capture.out / native["stdout_path"]
        comparison = validate_records(read_jsonl(raw))
        transcript = gzip_artifact(raw, saved / "native.jsonl.gz")
        transcript["path"] = "wrapper-mutation/" + transcript["path"]
        result["transcript"] = transcript
        native.update({"stdout_path": transcript["path"], "stdout_sha256": transcript["sha256"],
                       "stdout_compression": "gzip", "stdout_uncompressed_sha256": transcript["raw_sha256"]})
        raw.unlink()
        detailed = saved / "comparison.json"
        detailed.write_text(json.dumps(comparison, ensure_ascii=False, separators=(",", ":")) + "\n",
                            encoding="utf-8", newline="\n")
        details_archive = gzip_artifact(detailed, saved / "comparison.json.gz")
        details_archive["path"] = "wrapper-mutation/" + details_archive["path"]
        detailed.unlink()
        result["comparison"] = details_archive
        result["coverage"] = comparison["coverage"]
        result["disagreement_count"] = len(comparison["disagreements"])
        kinds = Counter(item["kind"] for item in comparison["disagreements"])
        result["disagreement_kinds"] = dict(sorted(kinds.items()))
        result["passed"] = (native["exit_code"] == 0 and comparison["coverage"]["full_domain"]
                            and kinds == Counter({"preserves": INPUT_COUNT}))
        result["detected_as_failure"] = bool(comparison["disagreements"])
    return result


def check_adapters(capture: Capture, binary: Path) -> list[dict]:
    cases = [
        ("adapter-valid", ["0", "65535", "00001", "20640", "20648", "-0"], 0),
        ("adapter-invalid", ["-1", "65536", "", " ", "+1", " 1", "1 ",
                             "true", "False", "1.0", "1e0", "0x50a0", "--unknown"], 2),
        ("adapter-mixed", ["0", "65536", "00001"], 2),
        ("adapter-empty", [], 2),
    ]
    results = []
    for name, tokens, exit_code in cases:
        command = capture.run(name, [str(binary), *tokens], ROOT)
        records = list(read_jsonl(capture.out / command["stdout_path"]))
        errors = []
        if command["exit_code"] != exit_code:
            errors.append({"kind": "exit_code", "expected": exit_code,
                           "actual": command["exit_code"]})
        if len(records) != len(tokens):
            errors.append({"kind": "record_count", "expected": len(tokens), "actual": len(records)})
        for index, (token, record) in enumerate(zip(tokens, records)):
            valid = (name == "adapter-valid" or (name == "adapter-mixed" and token != "65536"))
            if valid:
                check = validate_records([record], [int(token)])
                errors.extend({"adapter_record_index": index, **error}
                              for error in check["disagreements"])
            else:
                wanted = {"status": "invalid_input", "input": token}
                if record != wanted:
                    actual = ({"raw": record.raw, "error": record.error}
                              if isinstance(record, InvalidJsonLine) else record)
                    errors.append({"adapter_record_index": index, "kind": "invalid_input",
                                   "expected": wanted, "actual": actual})
        results.append({"name": name, "tokens": tokens, "expected_exit_code": exit_code,
                        "actual_exit_code": command["exit_code"], "record_count": len(records),
                        "passed": not errors, "disagreements": errors, "command": name})
    return results


def run(out: Path, binary: Path) -> dict:
    out = out.resolve()
    if out.exists() and (not out.is_dir() or any(out.iterdir())):
        raise ValueError("--out must name a new or empty directory")
    out.mkdir(parents=True, exist_ok=True)
    binary = binary.resolve()
    before = manifest()
    capture = Capture(out)
    problems = []
    git = git_prefix(capture)
    revision_command = capture.run("git-revision", [*git, "rev-parse", "HEAD"], ROOT)
    revision = capture.stdout(revision_command).strip() if revision_command["exit_code"] == 0 else None
    status_command = capture.run("git-status", [*git, "status", "--porcelain", "--untracked-files=normal"], ROOT)
    for command in (revision_command, status_command):
        if command["exit_code"] != 0:
            problems.append({"kind": "git_metadata_unavailable", "command": command["name"],
                             "exit_code": command["exit_code"]})
    lake_version = capture.run("lake-version", ["lake", "--version"])
    lean_version = capture.run("lean-version", ["lake", "env", "lean", "--version"])
    build = capture.run("build", ["lake", "-v", "build", "grouping_checker"])
    replay = capture.run("kernel-replay", ["lake", "env", "leanchecker", "GroupingChecker"])
    axiom_command = capture.run("axioms", ["lake", "env", "lean", "GroupingAudit.lean"])
    axiom_check = validate_axioms(capture.stdout(axiom_command))
    traces = collect_build_artifacts(out)
    build_log = capture.stdout(build) + (out / build["stderr_path"]).read_text(encoding="utf-8", errors="replace")
    required_traces = (
        "lean/.lake/build/lib/lean/GroupingChecker.trace",
        "lean/.lake/build/lib/lean/GroupingMain.trace",
        "lean/.lake/build/ir/GroupingChecker.c.o.export.trace",
        "lean/.lake/build/ir/GroupingMain.c.o.export.trace",
        "lean/.lake/build/bin/grouping_checker.trace",
        "lean/.lake/build/bin/grouping_checker.rsp",
    )
    present_traces = {record["source_path"] for record in traces}
    for required in required_traces:
        if required not in present_traces:
            problems.append({"kind": "missing_build_trace", "path": required})

    pinned = (LEAN / "lean-toolchain").read_text(encoding="utf-8").strip()
    version_match = re.fullmatch(r"leanprover/lean4:v([0-9]+\.[0-9]+\.[0-9]+)", pinned)
    actual_lean_version = capture.stdout(lean_version).strip()
    toolchain_matches = bool(version_match and re.search(
        r"\bLean \(version " + re.escape(version_match.group(1)) + r"(?:,|\))", actual_lean_version))
    if not toolchain_matches:
        problems.append({"kind": "toolchain_version", "expected": pinned, "actual": actual_lean_version})

    prefix_command = capture.run("lean-prefix", ["lake", "env", "lean", "--print-prefix"])
    prefix = Path(capture.stdout(prefix_command).strip()) if prefix_command["exit_code"] == 0 else None
    compiler = prefix / "bin" / ("clang.exe" if platform.system() == "Windows" else "clang") if prefix else None
    compiler_info = {"path": str(compiler) if compiler else None}
    if compiler and compiler.is_file():
        compiler_version = capture.run("compiler-version", [str(compiler), "--version"])
        compiler_target = capture.run("compiler-target", [str(compiler), "-dumpmachine"])
        compiler_info.update({"sha256": sha256(compiler), "version": capture.stdout(compiler_version).strip(),
                              "target": capture.stdout(compiler_target).strip()})
    else:
        problems.append({"kind": "compiler_metadata_unavailable", "path": str(compiler) if compiler else None})

    built_binary = LEAN / ".lake/build/bin" / ("grouping_checker.exe" if platform.system() == "Windows" else "grouping_checker")
    binary_info = {
        "path": str(binary), "build_artifact_path": str(built_binary),
        "target_architecture": compiler_info.get("target"),
        "host": {"system": platform.system(), "machine": platform.machine(), "platform": platform.platform()},
        "compiler": compiler_info, "build_command": "build",
        "build_log": {"stdout_path": build["stdout_path"], "stderr_path": build["stderr_path"]},
        "build_trace_artifacts": traces,
        "cache_policy": "Lake validates its dependency traces and may replay cached commands. Trace files and verbose output are retained; a replay is not described as a fresh compiler invocation.",
        "verbose_output_mentions_replay": "replayed" in build_log.lower(),
    }
    transcript = None
    adapter_tests = []
    comparison = validate_records([])
    native_command = None
    if binary.is_file():
        binary_info.update({"sha256": sha256(binary), "size_bytes": binary.stat().st_size})
        binary_info["build_artifact_sha256"] = sha256(built_binary) if built_binary.is_file() else None
        binary_info["matches_build_artifact"] = binary_info["sha256"] == binary_info["build_artifact_sha256"]
        if not binary_info["matches_build_artifact"]:
            problems.append({"kind": "binary_does_not_match_build_artifact"})
        # Preserve the bytes before execution; no executable source is rewritten.
        if binary_info["size_bytes"] <= 256 * 1024 * 1024:
            binary_info["archive"] = gzip_artifact(binary, out / "binary.gz")
        else:
            binary_info["archive"] = None
            problems.append({"kind": "binary_exceeds_archive_limit", "limit_bytes": 256 * 1024 * 1024})

        if platform.system() == "Linux":
            linked = capture.run("linked-libraries", ["ldd", str(binary)], ROOT)
        elif platform.system() == "Darwin":
            linked = capture.run("linked-libraries", ["otool", "-L", str(binary)], ROOT)
        elif shutil.which("dumpbin"):
            linked = capture.run("linked-libraries", ["dumpbin", "/DEPENDENTS", str(binary)], ROOT)
        else:
            linked = None
        binary_info["linked_libraries"] = linked
        binary_info["linked_libraries_scope"] = "The platform command reports dynamic dependencies; static library flags and search paths are preserved in the link response file."
        if not linked or linked["exit_code"] != 0:
            problems.append({"kind": "linked_libraries_report_unavailable"})
        if shutil.which("file"):
            identify = capture.run("binary-file-type", ["file", str(binary)], ROOT)
            binary_info["file_type"] = capture.stdout(identify).strip()

        native_command = capture.run("native-all", [str(binary), "--all"], ROOT)
        raw = out / native_command["stdout_path"]
        comparison = validate_records(read_jsonl(raw))
        transcript = gzip_artifact(raw, out / "native.jsonl.gz")
        transcript["record_format"] = "UTF-8 JSON Lines; native stdout, exact bytes before gzip"
        transcript["command"] = "native-all"
        native_command.update({"stdout_path": transcript["path"], "stdout_sha256": transcript["sha256"],
                               "stdout_compression": "gzip", "stdout_uncompressed_sha256": transcript["raw_sha256"]})
        raw.unlink()  # This single private staging file is now preserved in gzip.
        adapter_tests = check_adapters(capture, binary)
        binary_info["sha256_after"] = sha256(binary)
        binary_info["unchanged_during_checks"] = binary_info["sha256_after"] == binary_info["sha256"]
        if not binary_info["unchanged_during_checks"]:
            problems.append({"kind": "binary_changed_during_checks"})
    else:
        binary_info.update({"sha256": None, "matches_build_artifact": False})
        problems.append({"kind": "missing_binary", "path": str(binary)})

    wrapper_mutation = run_wrapper_mutation(capture)
    if not wrapper_mutation["passed"]:
        problems.append({"kind": "compiled_wrapper_fault_control_failed"})
    after = manifest()
    sources_unchanged = before == after and all(before.values())
    if not sources_unchanged:
        problems.append({"kind": "missing_or_changed_sources", "paths": [
            name for name in before if before[name] is None or before[name] != after[name]
        ]})
    proof_status = {
        "build": build["exit_code"] == 0,
        "kernel_replay": replay["exit_code"] == 0,
        "axioms": axiom_command["exit_code"] == 0 and axiom_check["passed"],
        "expected_declarations": list(EXPECTED_DECLARATIONS), "axiom_reports": axiom_check,
        "scope": "Lean source and exported module replay for the unary grouping checker; excludes a proof about the native executable, compiler, runtime, or hardware",
    }
    passed = bool(
        not problems and sources_unchanged and toolchain_matches
        and all(proof_status[key] for key in ("build", "kernel_replay", "axioms"))
        and native_command is not None and native_command["exit_code"] == 0
        and comparison["coverage"]["full_domain"] and not comparison["disagreements"]
        and adapter_tests and all(case["passed"] for case in adapter_tests)
        and revision is not None and status_command["exit_code"] == 0
        and lake_version["exit_code"] == lean_version["exit_code"] == 0
    )
    summary = {
        "schema_version": 1, "passed": passed, "contract_id": reference.CONTRACT_ID,
        "source_revision": revision,
        "source_tree_dirty": bool(capture.stdout(status_command).strip()) if status_command["exit_code"] == 0 else None,
        "source_manifest": before, "source_manifest_after": after,
        "hash_encoding": "SHA-256 of exact artifact bytes; 64 lowercase hexadecimal digits; no text normalization",
        "sources_unchanged": bool(sources_unchanged),
        "reference": {"path": "scripts/grouping_reference.py", "version": reference.REFERENCE_VERSION,
                      "sha256": before["scripts/grouping_reference.py"],
                      "independence": "Authored from the input contract before its author read the Lean implementation; integration harness authored afterwards. Arithmetic base-4 decoding and block-image-set preservation reference; no formal proof of the Python reference."},
        "harness": {"path": "scripts/run_grouping_checks.py", "sha256": before["scripts/run_grouping_checks.py"]},
        "toolchain": {"pinned": pinned, "lean_version": actual_lean_version,
                      "lake_version": capture.stdout(lake_version).strip(), "matches_pin": toolchain_matches},
        "proof_status": proof_status, "binary": binary_info, "commands": capture.commands,
        "transcript": transcript, **comparison, "adapter_tests": adapter_tests,
        "run_problems": problems, "compiled_wrapper_mutation": wrapper_mutation,
        "scope": "All 65,536 encodings of one unary operation and one labeled grouping on exactly four objects; every labeling remains a distinct input",
        "assumptions": ["The written contract expresses the intended property.",
                        "Lean kernel replay and reported axioms support the source theorem under the installed Lean toolchain.",
                        "The independent Python reference, comparison harness, OS, runtime, and hardware behave correctly.",
                        "SHA-256 binds saved bytes; source revision alone does not identify uncommitted files."],
        "limits": ["Exhaustive executable agreement is not a native machine-code refinement proof.",
                   "One grouping's preservation does not establish a full congruence family or an atlas census.",
                   "Adapter probes are a separate finite test set, not exhaustive testing of every possible input string.",
                   "Unit corruption controls test the harness validator; the compiled fault control changes only the wrapper's emitted acceptance field, not the proved checker.",
                   "The independently authored reference and Lean source still share the same written contract."],
    }
    (out / "summary.json").write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n",
                                      encoding="utf-8", newline="\n")
    return summary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--binary", type=Path, default=LEAN / ".lake/build/bin" /
                        ("grouping_checker.exe" if platform.system() == "Windows" else "grouping_checker"))
    args = parser.parse_args()
    try:
        result = run(args.out, args.binary)
    except (OSError, ValueError) as error:
        print(json.dumps({"status": "error", "message": str(error)}), file=sys.stderr)
        return 2
    print(json.dumps({"passed": result["passed"], "summary": str(args.out / "summary.json"),
                      "actual_tested_count": result["coverage"]["actual_tested_count"],
                      "distinct_word_count": result["coverage"]["distinct_word_count"],
                      "disagreement_count": len(result["disagreements"]),
                      "run_problem_count": len(result["run_problems"])}))
    return 0 if result["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
