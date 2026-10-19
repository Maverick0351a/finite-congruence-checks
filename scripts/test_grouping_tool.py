"""Input, schema, and exact-evidence rejection controls for the grouping tool."""
import copy
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import grouping_tool as tool


class InputTests(unittest.TestCase):
    def test_proposal_encoding(self):
        self.assertEqual(tool.encode_proposal({"operation": [0, 2, 2, 3], "group_labels": [0, 0, 1, 2]}), 0x90e8)

    def test_malformed_input(self):
        good = {"operation": [0, 2, 2, 3], "group_labels": [0, 0, 1, 2]}
        for bad in (None, [], {**good, "extra": 1}, {"operation": good["operation"]},
                    {**good, "operation": [0, 1, 2]},
                    *({**good, "group_labels": [0, 0, 1, value]} for value in (True, 2.0, "2", -1, 4, None))):
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                tool.encode_proposal(bad)

    def test_paths_reject_escape_and_missing_file(self):
        for name in ("../outside.json", "/tmp/outside", "C:/outside", "a\\b", "", "does-not-exist.json"):
            with self.subTest(name=name), self.assertRaises(ValueError):
                tool.artifact(name)

    def test_duplicate_json_keys_are_invalid(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "bad.json"
            path.write_text('{"operation": [], "operation": [0,1,2,3]}', encoding="utf-8")
            with self.assertRaises(ValueError):
                tool.read_json(path)

    def test_schema_type_and_outcome_controls(self):
        document = tool.read_json(tool.artifact(tool.SCHEMA))
        outcome = document["properties"]["outcome"]
        tool.schema_check({"preserves": False, "violating_pair": [0, 1]}, outcome, document)
        tool.schema_check({"preserves": True, "violating_pair": None}, outcome, document)
        for value in ({"preserves": 1, "violating_pair": None},
                      {"preserves": True, "violating_pair": [0, 1]},
                      {"preserves": False, "violating_pair": None},
                      {"preserves": False, "violating_pair": [True, 1]},
                      {"preserves": False, "violating_pair": [0, 4]},
                      {"preserves": True},
                      {"preserves": True, "violating_pair": None, "extra": "claim"}):
            with self.subTest(value=value), self.assertRaises(ValueError):
                tool.schema_check(value, outcome, document)


class EvidenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.receipt_path = Path(os.environ.get("GROUPING_RECEIPT", tool.ROOT / "evidence/grouping-checker-v1/summary.json")).resolve()
        if not cls.receipt_path.is_file():
            if "GROUPING_RECEIPT" in os.environ:
                raise FileNotFoundError(f"explicit GROUPING_RECEIPT is missing: {cls.receipt_path}")
            raise unittest.SkipTest("native receipt not generated yet; CI supplies GROUPING_RECEIPT after the exhaustive run")
        cls.cached = tool.load_receipt(cls.receipt_path)

    def record(self, word=0x90e8):
        receipt, rows, transcript = self.cached
        return tool.result_record(word, self.receipt_path, receipt, rows[word], transcript)

    def test_saved_pass_and_fail_records_validate(self):
        for word in (0x90e8, 0x80e8, 0, 65535):
            tool.validate_result(self.record(word), self.cached)

    def test_reject_semantically_changed_records(self):
        edits = [
            lambda r: r.update(input_id="ug4-v1:80e8"),
            lambda r: r["input"].update(word=True),
            lambda r: r["input"].update(group_labels=[0, 0, 0, 2]),
            lambda r: r["outcome"].update(preserves=True, violating_pair=None),
            lambda r: r["outcome"].update(violating_pair=[0, 0]),
            lambda r: r["checker"].update(binary_sha256="0" * 64),
            lambda r: r["checker"].update(source_sha256="0" * 64),
            lambda r: r["specification"].update(artifact_sha256="0" * 64),
            lambda r: r["evidence"][1].update(kind="binary_refinement"),
            lambda r: r["evidence"][1].update(case_pointer="jsonl:word=33000"),
            lambda r: r["evidence"][0].update(artifact_path="../summary.json"),
            lambda r: r["evidence"][0].update(artifact_sha256="0" * 64),
            lambda r: r.update(limits=["Proves all machine code correct"]),
        ]
        for index, edit in enumerate(edits):
            record = copy.deepcopy(self.record())
            edit(record)
            with self.subTest(edit=index), self.assertRaises(ValueError):
                tool.validate_result(record, self.cached)

    def test_reject_inconsistent_receipt_metadata(self):
        edits = [
            lambda r: r.update(source_revision="0" * 40),
            lambda r: r["binary"].update(sha256_after="0" * 64),
            lambda r: r["binary"]["archive"].update(raw_sha256="0" * 64),
            lambda r: r["source_manifest"].update({tool.CORE: "0" * 64}),
            lambda r: r["proof_status"].update(axioms=False),
            lambda r: r["transcript"].update(sha256="0" * 64),
            lambda r: r["coverage"].update(distinct_word_count=65535),
        ]
        for index, edit in enumerate(edits):
            receipt = copy.deepcopy(self.cached[0])
            edit(receipt)
            with self.subTest(edit=index), patch.object(tool, "read_json", return_value=receipt), self.assertRaises(ValueError):
                tool.load_receipt(self.receipt_path)


if __name__ == "__main__":
    unittest.main()
