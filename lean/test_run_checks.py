"""The formal-check runner must preserve failures and reject stale evidence."""
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("run_checks", Path(__file__).with_name("run_checks.py"))
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


class CheckRunnerTests(unittest.TestCase):
    def test_failed_child_is_recorded_and_stops_run(self):
        with tempfile.TemporaryDirectory() as tmp:
            steps = [("bad-proof", runner.ROOT, [sys.executable, "-c", "print('rejected'); raise SystemExit(7)"]),
                     ("never-run", runner.ROOT, [sys.executable, "-c", "raise SystemExit(0)"])]
            with patch.object(runner, "stages", return_value=steps):
                self.assertFalse(runner.run(Path(tmp), "unused", True))
            record = json.loads((Path(tmp) / "result.json").read_text())
            self.assertFalse(record["passed"])
            self.assertEqual(len(record["commands"]), 1)
            self.assertEqual(record["commands"][0]["exit_code"], 7)
            self.assertIn("rejected", (Path(tmp) / "bad-proof.log").read_text())
            self.assertFalse((Path(tmp) / "never-run.log").exists())

    def test_changed_sources_cannot_produce_passing_record(self):
        with tempfile.TemporaryDirectory() as tmp:
            steps = [("proof", runner.ROOT, [sys.executable, "-c", "raise SystemExit(0)"])]
            with patch.object(runner, "stages", return_value=steps), patch.object(
                    runner, "source_hashes", side_effect=[{"proof": "before"}, {"proof": "after"}]):
                self.assertFalse(runner.run(Path(tmp), "unused", True))
            record = json.loads((Path(tmp) / "result.json").read_text())
            self.assertFalse(record["passed"])
            self.assertFalse(record["sources_unchanged"])

    def test_existing_evidence_is_not_overwritten(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "result.json"
            path.write_text("protected")
            with self.assertRaisesRegex(ValueError, "new or empty"):
                runner.run(Path(tmp), "unused", True)
            self.assertEqual(path.read_text(), "protected")


if __name__ == "__main__":
    unittest.main()
