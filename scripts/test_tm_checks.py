"""Offline admission controls, independent of Lean availability.

Replay fixtures below are synthetic: their tiny binary is not executable and
their source/build validators are mocked. They exercise retained-record
admission, not a Lean execution, compiled mutation, or proof.
"""
from contextlib import redirect_stdout
import copy
import gzip
import hashlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import run_tm_checks as checks
import tm_cases


class ComparisonTests(unittest.TestCase):
    def setUp(self):
        self.cases = [{"id": "write", "machine": tm_cases.machine(
            2, 2, 0, [1], [[1, 1, 0], None, None, None]),
            "input": [], "steps": 1}]
        # Literal expected result: final write at zero, then head moves left.
        self.record = {"id": "write", "steps": 1, "state": 1,
                       "head": -1, "halted": True, "tape": [[0, 1]]}

    def result(self, rec):
        return checks.compare(self.cases, json.dumps(rec))["passed"]

    def test_exact_configuration(self):
        self.assertTrue(self.result(self.record))

    def test_each_observable_is_checked(self):
        for field, value in (("state", 2), ("head", 0), ("tape", []),
                             ("tape", [[1, 1]]), ("halted", False), ("steps", 0)):
            with self.subTest(field=field, value=value):
                self.assertFalse(self.result(dict(self.record, **{field: value})))

    def test_types_and_canonical_support(self):
        for field, value in (("state", True), ("steps", 1.0), ("head", -1.0),
                             ("halted", 1), ("tape", [[0, True]]),
                             ("tape", [[0, 1], [0, 1]]),
                             ("tape", [[0, 1], [1, 0]]), ("tape", [[0.0, 1]])):
            with self.subTest(field=field, value=value):
                self.assertFalse(self.result(dict(self.record, **{field: value})))

    def test_all_fields_required_and_no_extra_fields(self):
        for field in self.record:
            rec = dict(self.record)
            del rec[field]
            self.assertFalse(self.result(rec))
        self.assertFalse(self.result(dict(self.record, unexpected=1)))

    def test_no_missing_duplicate_unknown_or_malformed_records(self):
        raw = json.dumps(self.record)
        for text in ("", raw + "\n" + raw, raw + "\n{}", raw + "\n{",
                     raw + "\n\n", raw.replace('"write"', '"unknown"'),
                     raw.replace('"state": 1', '"state": 0, "state": 1')):
            with self.subTest(text=text):
                self.assertFalse(checks.compare(self.cases, text)["passed"])

    def test_controls_detect_changed_outputs(self):
        self.assertTrue(all(checks.rejection_controls(self.cases, json.dumps(self.record)).values()))
        self.assertTrue(all(checks.rejection_controls(self.cases, json.dumps(self.record) + "\n").values()))

    def test_each_control_introduces_only_its_named_fault(self):
        observed = []
        original_compare = checks.compare

        def capture(cases, raw):
            result = original_compare(cases, raw)
            observed.append(result)
            return result

        with mock.patch.object(checks, "compare", side_effect=capture):
            controls = checks.rejection_controls(self.cases, json.dumps(self.record) + "\n")
        expected_kinds = {
            "altered-state": ["configuration-mismatch"],
            "altered-head": ["configuration-mismatch"],
            "altered-tape": ["configuration-mismatch"],
            "altered-steps": ["configuration-mismatch"],
            "missing-record": ["missing-record"],
            "duplicate-record": ["duplicate-or-unknown-id"],
            "malformed-json": ["invalid-json"],
        }
        self.assertEqual(set(controls), set(expected_kinds))
        for name, result in zip(controls, observed):
            with self.subTest(control=name):
                self.assertEqual([error["kind"] for error in result["disagreements"]],
                                 expected_kinds[name])

    def test_dataset_ids_and_stated_subdomain(self):
        cases = tm_cases.comparison_cases()
        self.assertEqual(len({c["id"] for c in cases}), len(cases))
        self.assertEqual(sum(c["id"].startswith("small-") for c in cases), 1960)
        self.assertEqual(sum(c["id"].startswith("sample-") for c in cases), 600)
        self.assertEqual(cases, tm_cases.comparison_cases())

    def test_helper_bookkeeping_over_comparison_domain(self):
        checks.helper_checks(tm_cases.comparison_cases())


class RetainedLogValidationTests(unittest.TestCase):
    """Synthetic logs test admission rules; no compiler or native calls occur."""

    def probes(self):
        return [dict(case, exit_code=1, stdout="",
                     stderr="tmOracle: line 1: synthetic invalid input\n")
                for case in checks.input_rejection_cases()]

    def test_expected_adapter_rejections_are_admitted(self):
        checks.validate_input_rejections(self.probes())

    def test_crashes_success_or_wrong_adapter_diagnostic_are_rejected(self):
        for field, value in (("exit_code", -11), ("exit_code", 0),
                             ("exit_code", 2), ("exit_code", True),
                             ("stderr", "Segmentation fault\n"),
                             ("stderr", "tmOracle: line 2: invalid input\n"),
                             ("stderr", ""), ("stdout", "{}\n")):
            with self.subTest(field=field, value=value):
                probes = self.probes()
                probes[0][field] = value
                with self.assertRaises(ValueError):
                    checks.validate_input_rejections(probes)

    def test_missing_duplicated_or_changed_rejection_probes_are_rejected(self):
        probes = self.probes()
        variants = [probes[:-1], [probes[0], *probes[:-1]]]
        for field, value in (("id", "unlisted-probe"), ("input_json", "{}")):
            changed = copy.deepcopy(probes)
            changed[0][field] = value
            variants.append(changed)
        for variant in variants:
            with self.subTest(first=variant[0]["id"], count=len(variant)):
                with self.assertRaises(ValueError):
                    checks.validate_input_rejections(variant)

    def test_pinned_version_and_complete_allowlisted_axiom_reports(self):
        names = ("halted_fixed", "missing_instruction", "instruction_step",
                 "instruction_writes", "instruction_preserves_other_cells")
        reports = [f"'TMOracle.Checks.{name}' depends on axioms: [propext, Quot.sound]"
                   for name in names]
        with tempfile.TemporaryDirectory(prefix="tm-log-test-") as directory:
            root = Path(directory)
            (root / "lean/tm").mkdir(parents=True)
            (root / "lean/tm/lean-toolchain").write_text("leanprover/lean4:v4.34.1\n")
            (root / "build").mkdir()
            version_path = root / "build/lean-version.log"
            axioms_path = root / "build/axioms.log"
            version_path.write_text("Lean (version 4.34.1, synthetic fixture)\n")
            axioms_path.write_text("\n".join(reports) + "\n")
            with mock.patch.object(checks, "ROOT", root):
                checks.validate_build_logs(root)
                variants = [reports[:-1], [*reports[:-1], reports[0]],
                            [*reports, reports[0]],
                            [reports[0].replace("propext", "sorryAx"), *reports[1:]],
                            [reports[0].replace("halted_fixed", "unlisted_theorem"), *reports[1:]]]
                for variant in variants:
                    with self.subTest(reports=variant):
                        axioms_path.write_text("\n".join(variant) + "\n")
                        with self.assertRaises(ValueError):
                            checks.validate_build_logs(root)
                axioms_path.write_text("\n".join(reports) + "\n")
                for version in ("Lean (version 4.34.10, synthetic fixture)\n",
                                "Lean (version 4.33.1, synthetic fixture)\n", ""):
                    with self.subTest(version=version):
                        version_path.write_text(version)
                        with self.assertRaises(ValueError):
                            checks.validate_build_logs(root)


class ReplayAdmissionTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="tm-replay-test-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.out = self.root / "receipt"
        self.out.mkdir()
        (self.out / "build").mkdir()
        (self.root / "lean/tm").mkdir(parents=True)
        self.toolchain = "leanprover/lean4:v4.34.1"
        (self.root / "lean/tm/lean-toolchain").write_text(self.toolchain + "\n")
        self.sources = {"scripts/tm_port.py": "a" * 64}
        self.cases = [{"id": "literal-left-write", "machine": tm_cases.machine(
            2, 2, 0, [1], [[1, 1, 0], None, None, None]), "input": [], "steps": 1}]
        self.record = {"id": "literal-left-write", "steps": 1, "state": 1,
                       "head": -1, "halted": True, "tape": [[0, 1]]}
        for patch in (
            mock.patch.object(checks, "ROOT", self.root),
            mock.patch.object(checks, "check_source"),
            mock.patch.object(checks, "source_hashes", return_value=self.sources),
            mock.patch.object(checks.tm_cases, "comparison_cases", return_value=self.cases),
            mock.patch.object(checks, "validate_build_logs", create=True),
            mock.patch.object(checks, "validate_input_rejections", create=True),
        ):
            patch.start()
            self.addCleanup(patch.stop)
        self.make_fixture()

    def make_fixture(self):
        self.binary = b"Synthetic replay fixture; not executable or Lean evidence.\n"
        (self.out / "binary.gz").write_bytes(gzip.compress(self.binary, mtime=0))
        raw = json.dumps(self.record) + "\n"
        (self.out / "inputs.jsonl").write_text(json.dumps(self.cases[0]) + "\n", encoding="utf-8")
        (self.out / "lean.jsonl").write_text(raw, encoding="utf-8")
        (self.out / "stderr.log").write_text("", encoding="utf-8")
        comparison = checks.compare(self.cases, raw)
        checks.dump(self.out / "comparison.json", comparison)
        checks.dump(self.out / "input-rejections.json", [])
        for name, _ in checks.BUILD_STAGES:
            (self.out / "build" / (name + ".log")).write_text("Synthetic build fixture.\n")
        artifact_names = [*checks.BASE_ARTIFACTS,
                          *("build/" + name + ".log" for name, _ in checks.BUILD_STAGES)]
        self.receipt = {
            "format": "tm-differential-v1", "scope": "synthetic offline admission test",
            "source_sha256": copy.deepcopy(self.sources), "binary_sha256": hashlib.sha256(self.binary).hexdigest(),
            "build_project": "lean/tm", "toolchain": self.toolchain,
            "command": ["lean/tm/.lake/build/bin/tmOracle"],
            "build_commands": [{"name": name, "argv": ["lake", *args], "exit_code": 0,
                                "log": "build/" + name + ".log"} for name, args in checks.BUILD_STAGES],
            "comparison": comparison, "rejection_controls": checks.rejection_controls(self.cases, raw),
            "input_rejection_cases": 0, "helper_cases": 1, "exit_code": 0,
            "passed": True, "sources_unchanged": True,
            "artifacts": {name: checks.sha(self.out / name) for name in artifact_names},
        }
        self.save_receipt()

    def save_receipt(self):
        checks.dump(self.out / "summary.json", self.receipt)

    def refresh_artifact_hash(self, name):
        self.receipt["artifacts"][name] = checks.sha(self.out / name)
        self.save_receipt()

    def replay(self):
        with redirect_stdout(io.StringIO()):
            checks.replay(self.out)

    def test_consistent_synthetic_receipt_replays(self):
        self.replay()

    def test_format_and_build_identity_cannot_be_relabelled(self):
        for key, value in (("format", "different-format"), ("toolchain", "leanprover/lean4:v0.0.0"),
                           ("build_project", "other-project"), ("command", ["arbitrary-binary"])):
            with self.subTest(field=key):
                self.make_fixture()
                self.receipt[key] = value
                self.save_receipt()
                with self.assertRaises(ValueError):
                    self.replay()
        self.make_fixture()
        self.receipt["build_commands"][0]["argv"] = ["lake", "env", "different-tool"]
        self.save_receipt()
        with self.assertRaises(ValueError):
            self.replay()

    def test_missing_manifest_member_and_unhashed_edit_are_rejected(self):
        del self.receipt["artifacts"]["binary.gz"]
        self.save_receipt()
        with self.assertRaises(ValueError):
            self.replay()
        self.make_fixture()
        (self.out / "lean.jsonl").write_text("{}\n", encoding="utf-8")
        with self.assertRaises(ValueError):
            self.replay()

    def test_binary_bytes_cannot_be_changed_by_rehashing_only_archive(self):
        (self.out / "binary.gz").write_bytes(gzip.compress(b"Different synthetic bytes.\n", mtime=0))
        self.refresh_artifact_hash("binary.gz")
        with self.assertRaises(ValueError):
            self.replay()
        self.make_fixture()
        self.receipt["binary_sha256"] = "0" * 64
        self.save_receipt()
        with self.assertRaises(ValueError):
            self.replay()

    def test_rehashed_wrong_output_is_recomputed_and_rejected(self):
        rec = dict(self.record, tape=[[0, 2]])
        (self.out / "lean.jsonl").write_text(json.dumps(rec) + "\n", encoding="utf-8")
        self.refresh_artifact_hash("lean.jsonl")
        with self.assertRaises(ValueError):
            self.replay()

    def test_rehashed_changed_input_is_rejected(self):
        cases = copy.deepcopy(self.cases)
        cases[0]["steps"] = 2
        (self.out / "inputs.jsonl").write_text(json.dumps(cases[0]) + "\n", encoding="utf-8")
        self.refresh_artifact_hash("inputs.jsonl")
        with self.assertRaises(ValueError):
            self.replay()

    def test_rehashed_bool_or_float_input_cannot_equal_frozen_integers(self):
        for field, value in (("steps", True), ("steps", 1.0), ("initial_state", False)):
            with self.subTest(field=field, value=value):
                self.make_fixture()
                case = copy.deepcopy(self.cases[0])
                if field == "initial_state":
                    case["machine"][field] = value
                else:
                    case[field] = value
                (self.out / "inputs.jsonl").write_text(json.dumps(case) + "\n", encoding="utf-8")
                self.refresh_artifact_hash("inputs.jsonl")
                with self.assertRaises(ValueError):
                    self.replay()

    def test_changed_current_sources_invalidate_saved_receipt(self):
        with mock.patch.object(checks, "source_hashes", return_value={"scripts/tm_port.py": "b" * 64}):
            with self.assertRaises(ValueError):
                self.replay()

    def test_unsuccessful_outcome_or_failed_controls_cannot_be_admitted(self):
        for key, value in (("passed", False), ("sources_unchanged", False),
                           ("exit_code", 1), ("helper_cases", 2)):
            with self.subTest(field=key):
                self.make_fixture()
                self.receipt[key] = value
                self.save_receipt()
                with self.assertRaises(ValueError):
                    self.replay()
        self.make_fixture()
        self.receipt["rejection_controls"]["duplicate-record"] = False
        self.save_receipt()
        with self.assertRaises(ValueError):
            self.replay()


if __name__ == "__main__":
    unittest.main()
