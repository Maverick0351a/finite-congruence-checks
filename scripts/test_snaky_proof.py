"""Test exact claim binding and corruption rejection using the saved proof run.

The actual Lean rejection programs are executed by snaky_proof.py run; these
tests exercise receipt replay and the local query interface.
"""
import copy
from pathlib import Path
import shutil
import tempfile
import unittest

import snaky_proof as proof
import query_context


class SnakyInputTests(unittest.TestCase):
    def test_binding_rejects_unsafe_or_ambiguous_inputs(self):
        original = proof.expected_claim()
        for edit in (
            lambda c: c["theorems"].__setitem__("envelope", "X.y\naxiom bad : False"),
            lambda c: c["values"]["target"][0].__setitem__(0, True),
            lambda c: c["values"]["target"][0].__setitem__(0, 1.0),
            lambda c: c["values"]["target"][0].__setitem__(0, 1000),
            lambda c: c["values"]["target"].append([0, 0]),
            lambda c: c["values"].__setitem__("card_index", -1),
            lambda c: c["conclusion"].__setitem__("maker_claims_at_most", False),
            lambda c: c["conclusion"].__setitem__("predicate", "All polyominoes are Maker wins."),
        ):
            candidate = copy.deepcopy(original)
            edit(candidate)
            with self.subTest(edit=edit), self.assertRaises(ValueError):
                proof.binding(candidate)

    def test_setup_failures_are_not_mathematical_rejections(self):
        self.assertTrue(proof.negative_rejected(1, "error: Type mismatch\n"))
        self.assertTrue(proof.negative_rejected(1, "error: tactic 'decide' evaluated to false\n"))
        for message in ("unknown module", "unknown identifier", "object file missing", "No such file",
                        "maximum number of heartbeats", "timeout", "failed to synthesize"):
            with self.subTest(message=message):
                self.assertFalse(proof.negative_rejected(1, "error: " + message + "\nType mismatch"))
        self.assertFalse(proof.negative_rejected(0, "error: Type mismatch"))
        self.assertFalse(proof.negative_rejected(True, "error: Type mismatch"))
        self.assertFalse(proof.negative_rejected(1, "error: unrelated failure"))

    def test_axiom_gate_requires_exact_reports(self):
        clean = "".join(f"'{n}' does not depend on any axioms\n" for n in proof.DECLARATIONS)
        self.assertEqual(len(proof.audit_axioms(clean)), len(proof.DECLARATIONS))
        for log in (clean.replace("does not depend on any axioms", "depends on axioms: [sorryAx]", 1),
                    "\n".join(clean.splitlines()[1:]), clean + clean.splitlines()[0]):
            with self.assertRaises(ValueError):
                proof.audit_axioms(log)

    def test_changed_vendor_and_dependency_sources_fail(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            project = root / proof.PROJECT
            project.mkdir(parents=True)
            for name in ("lakefile.toml", "lean-toolchain", "lake-manifest.json", "vendor-manifest.json"):
                shutil.copy2(proof.ROOT / proof.PROJECT / name, project / name)
            shutil.copytree(proof.ROOT / proof.PROJECT / "OAI", project / "OAI")
            proof.validate_project(root)
            (project / "lakefile.lean").write_text("-- alternate config", encoding="utf-8")
            with self.assertRaises(ValueError):
                proof.validate_project(root)
            (project / "lakefile.lean").unlink()
            vendor = project / "OAI/GameTheory/SnakyTwentyOne/Model.lean"
            vendor.write_bytes(vendor.read_bytes() + b"\n-- changed\n")
            with self.assertRaises(ValueError):
                proof.validate_project(root)
            shutil.copy2(proof.ROOT / proof.PROJECT / "OAI/GameTheory/SnakyTwentyOne/Model.lean", vendor)
            manifest = proof.read(project / "lake-manifest.json")
            manifest["packages"][0]["rev"] = "0" * 40
            (project / "lake-manifest.json").write_bytes(proof.encode(manifest))
            with self.assertRaises(ValueError):
                proof.validate_project(root)


class SnakyProofTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.claim = proof.check_binding()
        cls.receipt = proof.replay()

    def mutated_receipt(self, edit):
        with tempfile.TemporaryDirectory() as folder:
            out = Path(folder) / "receipt"
            shutil.copytree(proof.ROOT / proof.RECEIPT, out)
            receipt = proof.read(out / "summary.json")
            edit(receipt, out)
            (out / "summary.json").write_bytes(proof.encode(receipt))
            with self.assertRaises((ValueError, OSError)):
                proof.replay(out)

    def test_actual_proof_and_all_controls_passed(self):
        self.assertEqual(len(self.receipt["stages"]), 12)
        negatives = proof.controls(self.claim)
        self.assertEqual(len(negatives), 7)
        for stage in self.receipt["stages"]:
            self.assertEqual(stage["exit_code"] != 0, stage["name"] in negatives)

    def test_query_round_trip_and_wrong_justifications(self):
        original = query_context.explain_claim(proof.CLAIM_ID)
        self.assertEqual(query_context.check_record(original)["status"], "supported")
        for edit in (
            lambda c: c["claim"]["values"]["envelope"][0].__setitem__(1, 3),
            lambda c: c["claim"]["values"]["square_bounds"].__setitem__("x_max", 15),
            lambda c: c["claim"]["values"]["target"][5].__setitem__(0, 5),
            lambda c: c["claim"]["theorems"].__setitem__("envelope", proof.PREFIX + "square_wins"),
            lambda c: c["claim"]["conclusion"].__setitem__("maker_claims_at_most", 20),
            lambda c: c["claim"]["conclusion"].__setitem__("maker_claims_at_most", 21.0),
            lambda c: c["claim"]["values"].__setitem__("initial_breaker", [[8, 8]]),
        ):
            candidate = copy.deepcopy(original)
            edit(candidate)
            with self.subTest(edit=edit):
                self.assertEqual(query_context.check_record(candidate)["status"], "unsupported")

    def test_missing_stage_fails(self):
        self.mutated_receipt(lambda r, _: r["stages"].pop())

    def test_accepted_bad_binding_fails(self):
        self.mutated_receipt(lambda r, _: r["stages"][-1].__setitem__("exit_code", 0))

    def test_wrong_kernel_command_fails(self):
        self.mutated_receipt(lambda r, _: r["stages"][4]["command"].pop())

    def test_wrong_verification_environment_fails(self):
        self.mutated_receipt(lambda r, _: r["environment_overrides"].__setitem__("LEAN_NUM_THREADS", "8"))

    def test_altered_source_hash_fails(self):
        self.mutated_receipt(lambda r, _: r["source_hashes"].__setitem__(proof.BINDING, "0" * 64))

    def test_changed_log_fails(self):
        self.mutated_receipt(lambda r, out: (out / "kernel.log").write_text("replacement", encoding="utf-8"))

    def test_missing_artifact_fails(self):
        self.mutated_receipt(lambda r, out: (out / "Audit.lean").unlink())

    def test_forged_control_with_matching_hash_fails(self):
        def edit(receipt, out):
            path = out / "wrong-move-bound.lean"
            path.write_text("import SnakyFinite\nexample : False := by decide\n", encoding="utf-8")
            receipt["artifacts"][path.name] = proof.digest(path)
        self.mutated_receipt(edit)

    def test_setup_error_even_with_matching_hash_fails(self):
        def edit(receipt, out):
            path = out / "changed-target.log"
            path.write_text("error: unknown module SnakyFinite\n", encoding="utf-8")
            receipt["artifacts"][path.name] = proof.digest(path)
        self.mutated_receipt(edit)


if __name__ == "__main__":
    unittest.main()
