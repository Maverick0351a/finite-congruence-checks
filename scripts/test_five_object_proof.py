"""Integrity and applicability tests against the actual saved five-object proof.

These tests replay evidence, not Lean. The runner separately executes the
deliberate-error programs and checks their Lean rejection.
"""
import copy
from pathlib import Path
import shutil
import tempfile
import unittest

import five_object_proof as proof
import query_context


class FiveObjectProofTests(unittest.TestCase):
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

    def test_actual_proof_and_all_negative_controls_passed(self):
        self.assertEqual(len(self.receipt["stages"]), 12)
        negatives = proof.controls(self.claim)
        self.assertEqual(len(negatives), 8)
        for stage in self.receipt["stages"]:
            self.assertEqual(stage["exit_code"] != 0, stage["name"] in negatives)

    def test_exact_claim_is_supported(self):
        record = query_context.explain_claim(proof.CLAIM_ID)
        self.assertEqual(query_context.check_record(record)["status"], "supported")
        self.assertIn("computational_evidence", record["claim"])
        self.assertIn("proof_evidence", record["claim"])

    def test_wrong_object_theorem_and_conclusion_are_unsupported(self):
        original = query_context.explain_claim(proof.CLAIM_ID)
        for edit in (
            lambda r: r["claim"]["values"]["A"]["operations"][0].__setitem__(0, 1),
            lambda r: r["claim"]["values"]["A"]["groupings"][1].__setitem__(1, 1),
            lambda r: r["claim"]["values"].__setitem__("A_to_B", list(range(8))),
            lambda r: r["claim"]["theorems"].__setitem__("classification_A", proof.PREFIX + "B.all_relations"),
            lambda r: r["claim"]["conclusion"].__setitem__("minimum_A", 2),
            lambda r: r["claim"]["conclusion"].__setitem__("distinct_groupings_B", 7),
            lambda r: r["claim"]["values"]["A"]["operations"][0].__setitem__(0, False),
        ):
            with self.subTest(edit=edit):
                candidate = copy.deepcopy(original)
                edit(candidate)
                self.assertEqual(query_context.check_record(candidate)["status"], "unsupported")

    def test_binding_rejects_injection_and_invalid_domains(self):
        for edit in (
            lambda c: c["theorems"].__setitem__("classification_A", "A.all_relations\naxiom bad : False"),
            lambda c: c["values"]["A"]["operations"][0].__setitem__(0, -1),
            lambda c: c["values"]["A_to_B"].__setitem__(0, True),
            lambda c: c["values"]["B"]["groupings"][0].append(0),
            lambda c: c["conclusion"].__setitem__("predicate", "all finite algebras"),
            lambda c: c["values"]["A"].__setitem__("minimum_unary_operations", 2),
        ):
            candidate = copy.deepcopy(self.claim)
            edit(candidate)
            with self.subTest(edit=edit), self.assertRaises(ValueError):
                proof.binding(candidate)

    def test_missing_stage_fails(self):
        self.mutated_receipt(lambda r, _: r["stages"].pop())

    def test_accepted_bad_binding_fails(self):
        self.mutated_receipt(lambda r, _: r["stages"][-1].__setitem__("exit_code", 0))

    def test_wrong_kernel_command_fails(self):
        self.mutated_receipt(lambda r, _: r["stages"][3]["command"].pop())

    def test_altered_source_hash_fails(self):
        self.mutated_receipt(lambda r, _: r["source_hashes"].__setitem__(proof.BINDING, "0" * 64))

    def test_changed_log_fails(self):
        self.mutated_receipt(lambda r, out: (out / "kernel.log").write_text("replacement", encoding="utf-8"))

    def test_missing_artifact_fails(self):
        self.mutated_receipt(lambda r, out: (out / "Audit.lean").unlink())

    def test_forged_control_even_with_updated_hash_fails(self):
        def edit(receipt, out):
            path = out / "wrong-minimum.lean"
            path.write_text("import FiveObjectMinimum\nexample : False := by decide\n", encoding="utf-8")
            receipt["artifacts"][path.name] = proof.digest(path)
        self.mutated_receipt(edit)

    def test_axiom_gate_rejects_sorry_and_missing_reports(self):
        clean = "".join(f"'{name}' does not depend on any axioms\n" for name in proof.DECLARATIONS)
        self.assertEqual(len(proof.audit_axioms(clean)), len(proof.DECLARATIONS))
        with self.assertRaises(ValueError):
            proof.audit_axioms(clean.replace("does not depend on any axioms", "depends on axioms: [sorryAx]", 1))
        with self.assertRaises(ValueError):
            proof.audit_axioms("\n".join(clean.splitlines()[1:]))

    def test_project_rejects_alternate_config_and_dependencies(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            project = root / proof.PROJECT
            project.mkdir(parents=True)
            for name in ("lakefile.toml", "lean-toolchain", "lake-manifest.json"):
                shutil.copy2(proof.ROOT / proof.PROJECT / name, project / name)
            proof.validate_project(root)
            (project / "lakefile.lean").write_text("-- alternate build program", encoding="utf-8")
            with self.assertRaises(ValueError):
                proof.validate_project(root)
            (project / "lakefile.lean").unlink()
            manifest = proof.read(project / "lake-manifest.json")
            manifest["packages"] = [{"name": "unexpected"}]
            (project / "lake-manifest.json").write_bytes(proof.encode(manifest))
            with self.assertRaises(ValueError):
                proof.validate_project(root)


if __name__ == "__main__":
    unittest.main()
