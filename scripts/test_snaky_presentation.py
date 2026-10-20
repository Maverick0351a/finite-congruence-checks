"""Presentation integrity controls; real publication prerequisites are mandatory.

AnchorControls can run during development. PublishedPresentationTests requires
the actual formal receipt, source anchor and exported files, and never skips
their absence. No test starts Lean, a browser, or a model.
"""
import copy
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

import build_snaky_presentation as presentation


class AnchorControls(unittest.TestCase):
    def setUp(self):
        self.folder = tempfile.TemporaryDirectory()
        self.addCleanup(self.folder.cleanup)
        self.root = Path(self.folder.name)
        self.path = "evidence/example.txt"
        target = self.root / self.path
        target.parent.mkdir()
        target.write_bytes(b"exact evidence\n")
        subprocess.run(["git", "init", "-q", str(self.root)], check=True, capture_output=True)
        subprocess.run(["git", "add", self.path], cwd=self.root, check=True, capture_output=True)
        subprocess.run(["git", "-c", "user.name=Presentation Test", "-c", "user.email=test@example.invalid",
                        "commit", "-qm", "Isolated source anchor fixture"], cwd=self.root, check=True, capture_output=True)
        revision = subprocess.run(["git", "rev-parse", "HEAD"], cwd=self.root, check=True, capture_output=True, text=True).stdout.strip()
        self.anchor = {"schema_version": 1, "revision": revision,
                       "files": {self.path: presentation.proof.digest(target)}}

    def check(self, anchor=...):
        return presentation.check_anchor(self.root, self.anchor if anchor is ... else anchor, [self.path])

    def test_real_git_anchor_accepts_exact_bytes(self):
        self.check()

    def test_invalid_revision_and_coverage_fail_closed(self):
        for revision in ("main", "a" * 39, True, "../../other", "0" * 40):
            changed = copy.deepcopy(self.anchor)
            changed["revision"] = revision
            with self.subTest(revision=revision), self.assertRaises(ValueError):
                self.check(changed)
        for files in ({}, {**self.anchor["files"], "extra": "0" * 64}):
            changed = copy.deepcopy(self.anchor)
            changed["files"] = files
            with self.subTest(files=files), self.assertRaises(ValueError):
                self.check(changed)

    def test_local_evidence_mutation_is_rejected(self):
        (self.root / self.path).write_bytes(b"altered evidence\n")
        with self.assertRaisesRegex(ValueError, "local anchored source changed"):
            self.check()

    def test_rehashing_changed_local_evidence_does_not_rewrite_history(self):
        target = self.root / self.path
        target.write_bytes(b"altered evidence\n")
        self.anchor["files"][self.path] = presentation.proof.digest(target)
        with self.assertRaisesRegex(ValueError, "Git bytes differ"):
            self.check()

    def test_malformed_anchor_contract_is_rejected(self):
        cases = [None, [], {}, {**self.anchor, "schema_version": True},
                 {**self.anchor, "schema_version": 2}, {**self.anchor, "files": []},
                 {**self.anchor, "extra_conclusion": "all strategies verified"}]
        for changed in cases:
            with self.subTest(anchor=changed), self.assertRaises(ValueError):
                self.check(changed)


class PublishedPresentationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # Deliberately fail instead of skipping a missing proof or publication file.
        cls.data = presentation.build()
        cls.play, cls.record, cls.paths = presentation.inputs()
        cls.anchor = presentation.proof.read(presentation.ROOT / presentation.ANCHOR)

    def test_generated_download_and_offline_script_match(self):
        texts = presentation.output_texts(self.data)
        for relative, expected in zip(presentation.OUTPUTS, texts):
            self.assertEqual((presentation.ROOT / relative).read_text(encoding="utf-8"), expected, relative)
        self.assertEqual(json.loads(texts[0]), self.data)
        self.assertEqual(self.data["play"], self.play)
        self.assertEqual(self.data["claim_record"], self.record)

    def test_claim_and_example_keep_separate_quantifiers(self):
        claim = self.record["claim"]
        self.assertEqual(claim["id"], self.play["sources"]["root_claim_id"])
        self.assertEqual(claim["values"]["envelope"], self.play["board"]["cells"])
        self.assertEqual(claim["conclusion"]["maker_claims_at_most"], 21)
        self.assertEqual(self.play["result"]["maker_claims"], 8)
        self.assertEqual(self.play["kind"], "illustrative_checked_execution")
        self.assertIn("not an extracted formally verified policy", " ".join(self.play["limits"]))
        self.assertEqual(presentation.query.check_record(self.record)["status"], "supported")

    def test_all_publication_links_identify_anchored_inputs(self):
        self.assertEqual(self.data["source_revision"], self.anchor["revision"])
        self.assertEqual(set(self.anchor["files"]), set(self.paths))
        for entry in self.data["evidence"]:
            self.assertEqual(entry["url"], presentation.GITHUB + self.anchor["revision"] + "/" + entry["path"])
            self.assertEqual(entry["sha256"], self.anchor["files"][entry["path"]])

    def copied_inputs(self, folder):
        root = Path(folder)
        for relative in [*self.paths, presentation.ANCHOR]:
            target = root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(presentation.ROOT / relative, target)
        # A rejection must be caused by the mutation, not an incomplete fixture.
        play, record, paths = presentation.inputs(root)
        self.assertEqual(play, self.play)
        self.assertEqual(record, self.record)
        self.assertEqual(paths, self.paths)
        return root

    def test_underlying_play_mutations_stop_export_before_git_lookup(self):
        for mutate in (
            lambda p: p["steps"][2]["maker"].__setitem__("cell", [8, 8]),
            lambda p: p["result"]["target"]["cells"].pop(),
            lambda p: p["sources"].__setitem__("root_claim_id", "unrelated:claim"),
        ):
            with self.subTest(mutate=mutate), tempfile.TemporaryDirectory() as folder:
                root = self.copied_inputs(folder)
                changed = copy.deepcopy(self.play)
                mutate(changed)
                (root / presentation.PLAY).write_bytes(presentation.proof.encode(changed))
                with self.assertRaises(ValueError):
                    presentation.inputs(root)

    def test_underlying_claim_and_proof_mutations_stop_export(self):
        for relative, mutate in (
            (presentation.proof.CLAIM_PATH, lambda c: c["conclusion"].__setitem__("maker_claims_at_most", 8)),
            (presentation.proof.CLAIM_PATH, lambda c: c["theorems"].__setitem__("envelope", "Unrelated.theorem")),
            (presentation.proof.RECEIPT + "/summary.json", lambda c: c["stages"].pop()),
        ):
            with self.subTest(path=relative), tempfile.TemporaryDirectory() as folder:
                root = self.copied_inputs(folder)
                changed = presentation.proof.read(root / relative)
                mutate(changed)
                (root / relative).write_bytes(presentation.proof.encode(changed))
                with self.assertRaises(ValueError):
                    presentation.inputs(root)

    def test_actual_anchor_mutations_fail_closed(self):
        for mutate in (
            lambda a: a.__setitem__("revision", "main"),
            lambda a: a["files"].pop(presentation.PLAY),
            lambda a: a["files"].__setitem__(presentation.PLAY, "0" * 64),
        ):
            changed = copy.deepcopy(self.anchor)
            mutate(changed)
            with self.assertRaises(ValueError):
                presentation.check_anchor(presentation.ROOT, changed, self.paths)


if __name__ == "__main__":
    unittest.main()
