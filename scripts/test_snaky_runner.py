"""Exercise runner failures with short Python processes, never Lean executions."""
import copy
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock

import snaky_proof as proof


class SnakyRunnerTests(unittest.TestCase):
    def setUp(self):
        self.folder = tempfile.TemporaryDirectory()
        self.addCleanup(self.folder.cleanup)
        self.root = Path(self.folder.name)
        (self.root / proof.PROJECT).mkdir(parents=True)
        self.out = self.root / "receipt"
        self.out.mkdir()
        self.receipt = {"status": "running", "stages": [], "artifacts": {}}

    def command(self, source):
        fixture = self.root / "fixture.py"
        fixture.write_text(source, encoding="utf-8")
        return [sys.executable, str(fixture)]

    def stage(self, source, *, negative=False, timeout=5):
        with mock.patch.object(proof, "stage_timeout", return_value=timeout):
            return proof.run_stage("fixture", self.command(source), root=self.root,
                                   out=self.out, receipt=self.receipt, negative=negative)

    def saved(self):
        saved = proof.read(self.out / "summary.json")
        self.assertNotIn("summary.json", saved["artifacts"])
        self.assertNotIn("summary.json.tmp", saved["artifacts"])
        self.assertFalse((self.out / "summary.json.tmp").exists())
        for name, sha in saved["artifacts"].items():
            self.assertEqual(proof.digest(self.out / name), sha)
        return saved

    def assert_child_stopped(self, child_pid):
        deadline = time.monotonic() + 3
        while True:
            try:
                state = Path(f"/proc/{child_pid}/stat").read_text().split(") ", 1)[1].split()[0]
            except FileNotFoundError:
                return
            if state == "Z":  # Exited, awaiting reaping by the system parent.
                return
            if time.monotonic() >= deadline:
                self.fail("spawned child survived its failed process group")
            time.sleep(0.05)

    def test_only_build_and_kernel_get_longer_limits(self):
        self.assertEqual(proof.stage_timeout("build"), 3600)
        self.assertEqual(proof.stage_timeout("kernel"), 7200)
        for name in ("version", "dependencies", "axioms", "changed-target"):
            self.assertEqual(proof.stage_timeout(name), 2400)

    def test_child_sees_running_checkpoint_and_output_is_retained(self):
        source = ("import json, pathlib, sys\n"
                  f"receipt = json.loads(pathlib.Path({str(self.out / 'summary.json')!r}).read_text())\n"
                  "assert receipt['status'] == 'running'\n"
                  "assert receipt['stages'][0]['status'] == 'running'\n"
                  "assert receipt['stages'][0]['exit_code'] is None\n"
                  "print('stdout retained', flush=True)\n"
                  "print('stderr retained', file=sys.stderr, flush=True)\n")
        stage = self.stage(source)
        self.assertEqual(stage["status"], "passed")
        self.assertEqual(stage["exit_code"], 0)
        self.assertIsNone(stage["failure_kind"])
        self.assertEqual(self.saved()["stages"], [stage])
        log = (self.out / "fixture.log").read_text()
        self.assertIn("stdout retained", log)
        self.assertIn("stderr retained", log)

    def test_timeout_keeps_partial_error_but_never_accepts_it(self):
        with self.assertRaises(subprocess.TimeoutExpired):
            self.stage("import time\nprint('error: Type mismatch', flush=True)\ntime.sleep(30)\n",
                       negative=True, timeout=1)
        stage = self.saved()["stages"][0]
        self.assertEqual(stage["status"], "failed")
        self.assertEqual(stage["failure_kind"], "timeout")
        self.assertEqual(stage["timeout_seconds"], 1)
        self.assertGreaterEqual(stage["duration_seconds"], 1)
        self.assertIsInstance(stage["exit_code"], int)
        self.assertNotEqual(stage["exit_code"], 0)
        self.assertIn("error: Type mismatch", (self.out / "fixture.log").read_text())

    def test_completed_expected_rejection_passes_with_its_real_exit_code(self):
        stage = self.stage("import sys\nprint('error: Type mismatch', flush=True)\nsys.exit(1)\n",
                           negative=True)
        self.assertEqual(stage["status"], "passed")
        self.assertEqual(stage["exit_code"], 1)
        self.assertIsNone(stage["failure_kind"])
        self.assertEqual(self.saved()["stages"], [stage])

    def test_kernel_inventory_and_successful_exit_are_both_required(self):
        for code, names, passes in ((0, ["Demo"], True), (1, ["Demo"], False),
                                    (0, [], False), (0, ["Demo", "Demo"], False),
                                    (0, ["Demo", "Unexpected"], False)):
            source = "import sys\n" + "".join(f"print('replaying {name}')\n" for name in names)
            source += f"sys.exit({code})\n"
            with self.subTest(code=code, names=names), \
                    mock.patch.object(proof, "module_names", return_value=["Demo"]):
                if passes:
                    stage = proof.run_stage("kernel", self.command(source), root=self.root,
                                            out=self.out, receipt=self.receipt)
                    self.assertEqual(stage["status"], "passed")
                else:
                    with self.assertRaises(ValueError):
                        proof.run_stage("kernel", self.command(source), root=self.root,
                                        out=self.out, receipt=self.receipt)
                    self.assertEqual(self.saved()["stages"][-1]["status"], "failed")

    def test_launch_failure_preserves_failed_stage_and_empty_log(self):
        with self.assertRaises(OSError):
            proof.run_stage("fixture", [str(self.root / "no-such-executable")], root=self.root,
                            out=self.out, receipt=self.receipt)
        stage = self.saved()["stages"][0]
        self.assertEqual(stage["status"], "failed")
        self.assertEqual(stage["failure_kind"], "execution")
        self.assertIsNone(stage["exit_code"])
        self.assertEqual((self.out / "fixture.log").read_bytes(), b"")

    def test_interrupt_kills_started_process_and_records_actual_exit(self):
        real_popen = subprocess.Popen
        processes = []

        def interrupt_once(*args, **kwargs):
            proc = real_popen(*args, **kwargs)
            processes.append(proc)
            real_wait = proc.wait
            first = True

            def wait(*args, **kwargs):
                nonlocal first
                if first:
                    first = False
                    raise KeyboardInterrupt()
                return real_wait(*args, **kwargs)

            proc.wait = wait
            return proc

        with mock.patch.object(proof.subprocess, "Popen", side_effect=interrupt_once):
            with self.assertRaises(KeyboardInterrupt):
                self.stage("import time\ntime.sleep(30)\n")
        stage = self.saved()["stages"][0]
        self.assertEqual(stage["status"], "failed")
        self.assertEqual(stage["failure_kind"], "interrupted")
        self.assertIsNotNone(processes[0].poll())
        self.assertEqual(stage["exit_code"], processes[0].returncode)

    @unittest.skipUnless(os.name == "posix", "POSIX signal exit codes")
    def test_external_signal_is_not_a_mathematical_rejection(self):
        with self.assertRaises(ValueError):
            self.stage("import os, signal\nprint('error: Type mismatch', flush=True)\n"
                       "os.kill(os.getpid(), signal.SIGTERM)\n", negative=True)
        stage = self.saved()["stages"][0]
        self.assertEqual(stage["failure_kind"], "interrupted")
        self.assertLess(stage["exit_code"], 0)
        self.assertFalse(proof.negative_rejected(stage["exit_code"], "error: Type mismatch"))

    @unittest.skipUnless(sys.platform.startswith("linux"), "Linux /proc verifies child termination")
    def test_timeout_kills_only_its_own_process_group(self):
        unrelated = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(30)"],
                                     start_new_session=True)
        child_file = self.root / "child.pid"
        try:
            source = ("import pathlib, subprocess, sys, time\n"
                      "child = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(30)'])\n"
                      f"pathlib.Path({str(child_file)!r}).write_text(str(child.pid))\n"
                      "print('child started', flush=True)\ntime.sleep(30)\n")
            with self.assertRaises(subprocess.TimeoutExpired):
                self.stage(source, timeout=2)
            child_pid = int(child_file.read_text())
            self.assert_child_stopped(child_pid)
            self.assertIsNone(unrelated.poll(), "an unrelated process was terminated")
            self.assertEqual(self.saved()["stages"][0]["failure_kind"], "timeout")
        finally:
            unrelated.kill()
            unrelated.wait(timeout=5)

    @unittest.skipUnless(sys.platform.startswith("linux"), "Linux /proc verifies child termination")
    def test_signaled_parent_cleanup_stops_child_and_preserves_parent_exit(self):
        child_file = self.root / "child.pid"
        source = ("import os, pathlib, signal, subprocess, sys\n"
                  "child = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(30)'])\n"
                  f"pathlib.Path({str(child_file)!r}).write_text(str(child.pid))\n"
                  "print('error: Type mismatch', flush=True)\n"
                  "os.kill(os.getpid(), signal.SIGTERM)\n")
        with self.assertRaises(ValueError):
            self.stage(source, negative=True)
        self.assert_child_stopped(int(child_file.read_text()))
        stage = self.saved()["stages"][0]
        self.assertEqual(stage["failure_kind"], "interrupted")
        self.assertEqual(stage["exit_code"], -15)

    def test_run_records_top_level_failure_and_does_not_replay(self):
        out = self.root / "full-run"
        (self.root / proof.finite.OUTPUT).parent.mkdir(parents=True)
        (self.root / proof.finite.OUTPUT).write_text("{}", encoding="utf-8")
        command = self.command("import time\nprint('partial build output', flush=True)\ntime.sleep(30)\n")
        with mock.patch.object(proof, "check_binding", return_value={}), \
                mock.patch.object(proof.finite, "replay", return_value={}), \
                mock.patch.object(proof, "source_hashes", return_value={}), \
                mock.patch.object(proof, "controls", return_value={}), \
                mock.patch.object(proof, "plan", return_value=[("build", command)]), \
                mock.patch.object(proof, "stage_timeout", return_value=1), \
                mock.patch.object(proof, "replay") as replay:
            with self.assertRaises(subprocess.TimeoutExpired):
                proof.run(out, root=self.root)
            replay.assert_not_called()
        saved = proof.read(out / "summary.json")
        self.assertEqual(saved["status"], "failed")
        self.assertEqual(saved["stages"][0]["failure_kind"], "timeout")
        self.assertIn("finished_utc", saved)
        self.assertEqual(saved["artifacts"]["build.log"], proof.digest(out / "build.log"))
        self.assertNotIn("summary.json", saved["artifacts"])

    def test_replay_rejects_incomplete_or_failed_stage_despite_success_header(self):
        # Use saved logs solely as a mutation fixture. Mock the historical source
        # hash comparison to reach the new stage checks; this is no proof run.
        shutil.copytree(proof.ROOT / proof.RECEIPT, self.out, dirs_exist_ok=True)
        baseline = proof.read(self.out / "summary.json")
        for stage, (_, command) in zip(baseline["stages"], proof.plan(baseline["claim"])):
            stage["command"] = command
            stage.update(status="passed", failure_kind=None,
                         timeout_seconds=proof.stage_timeout(stage["name"]))
        for change in ({"status": "running"}, {"status": "failed"},
                       {"failure_kind": "timeout"}, {"failure_kind": "interrupted"},
                       {"timeout_seconds": 9999}):
            candidate = copy.deepcopy(baseline)
            candidate["stages"][-1].update(change)
            (self.out / "summary.json").write_bytes(proof.encode(candidate))
            with self.subTest(change=change), \
                    mock.patch.object(proof, "source_hashes", return_value=baseline["source_hashes"]), \
                    mock.patch.object(proof, "audit_kernel"):
                with self.assertRaisesRegex(ValueError, "stage did not complete|wrong stage timeout"):
                    proof.replay(self.out)


if __name__ == "__main__":
    unittest.main()
