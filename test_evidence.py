"""Exercise incomplete/tampered evidence and runner failure propagation."""
from contextlib import redirect_stderr, redirect_stdout
import io
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import run_experiment
from scripts import check_evidence


class EvidenceTests(unittest.TestCase):
    def minimal_run(self):
        return {"passed": True,
                "commands": [{"log": name, "exit_code": 0} for name in sorted(check_evidence.LOGS)],
                "output_sha256": {name: "unused" for name in check_evidence.OUTPUTS},
                "code_sha256": {}}

    def write_run(self, folder, run):
        (folder / "run-evidence.json").write_text(json.dumps(run), encoding="utf-8", newline="\n")

    def test_incomplete_hash_registry_is_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            run = self.minimal_run()
            run["output_sha256"].pop("unit-tests.log")
            self.write_run(folder, run)
            with self.assertRaisesRegex(ValueError, "output hash registry"):
                check_evidence.check(folder, root=folder)

    def test_duplicate_stage_cannot_replace_missing_stage(self):
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            run = self.minimal_run()
            run["commands"][-1] = run["commands"][0].copy()
            self.write_run(folder, run)
            with self.assertRaisesRegex(ValueError, "duplicate experiment stage"):
                check_evidence.check(folder, root=folder)

    def test_changed_output_bytes_are_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            run = self.minimal_run()
            for name in check_evidence.OUTPUTS:
                path = folder / name
                path.write_bytes(b"original fixture bytes")
                run["output_sha256"][name] = check_evidence.sha256(path)
            (folder / "unit-tests.log").write_bytes(b"changed fixture bytes")
            self.write_run(folder, run)
            with self.assertRaisesRegex(ValueError, "output hash mismatch"):
                check_evidence.check(folder, root=folder)

    def test_evidence_member_cannot_escape_directory(self):
        with tempfile.TemporaryDirectory() as temporary:
            with self.assertRaisesRegex(ValueError, "escapes directory"):
                check_evidence.member(Path(temporary), "../outside.json")

    def test_runner_records_failed_child_without_success(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "failed-run"
            fake = SimpleNamespace(returncode=7, stdout="injected child failure\n", stderr="")
            with patch("sys.argv", ["run_experiment.py", "--out", str(output)]), \
                 patch.object(run_experiment.platform, "platform", return_value="test-platform"), \
                 patch.object(run_experiment.subprocess, "run", return_value=fake) as invoked, \
                 redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
                status = run_experiment.main()
            self.assertEqual(status, 1)
            self.assertEqual(invoked.call_count, 1)
            run = json.loads((output / "run-evidence.json").read_text(encoding="utf-8"))
            self.assertFalse(run["passed"])
            self.assertEqual(run["commands"][0]["exit_code"], 7)
            self.assertIn("{python}", run["commands"][0]["argv"])
            self.assertEqual(run["output_sha256"]["unit-tests.log"],
                             check_evidence.sha256(output / "unit-tests.log"))

    def test_runner_rejects_nonempty_directory_without_modifying_it(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary)
            sentinel = output / "existing-evidence.json"
            sentinel.write_bytes(b"preserve me")
            with patch("sys.argv", ["run_experiment.py", "--out", str(output)]), \
                 redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()), \
                 self.assertRaises(SystemExit) as failure:
                run_experiment.main()
            self.assertEqual(failure.exception.code, 2)
            self.assertEqual(sentinel.read_bytes(), b"preserve me")
            self.assertEqual(list(output.iterdir()), [sentinel])


if __name__ == "__main__":
    unittest.main()
