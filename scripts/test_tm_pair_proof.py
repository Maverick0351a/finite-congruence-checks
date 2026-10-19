"""Evidence gates supplement the real Lean rejection probes saved by run."""
import copy
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

import tm_pair_proof as proof


class PairProofTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.out = proof.ROOT / proof.EVIDENCE
        cls.receipt = proof.replay(cls.out)

    def reject_receipt(self, mutate, message):
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "evidence"
            shutil.copytree(self.out, out)
            receipt = copy.deepcopy(self.receipt)
            mutate(receipt, out)
            (out / "summary.json").write_bytes(proof.encode(receipt))
            with self.assertRaisesRegex(ValueError, message):
                proof.replay(out)

    def test_exact_claim_full_tapes_and_first_halt(self):
        c = self.receipt["claim"]
        self.assertEqual(c["values"]["input"], [])
        self.assertEqual(c["conclusion"]["initial_halted"], [False, False])
        self.assertEqual(c["conclusion"]["first_halt"], [1, 1])
        self.assertEqual(c["conclusion"]["tape"], {"quantifier": "every i : Int", "left": [], "right": [[0, 1]], "unlisted_symbol": 0})
        self.assertEqual(set(self.receipt["axioms"]), set(proof.DECLARATIONS))

    def test_real_lean_controls_failed_for_semantic_mismatch(self):
        for stage in self.receipt["stages"]:
            if stage["name"] in proof.controls(self.receipt["claim"]):
                with self.subTest(stage=stage["name"]):
                    self.assertEqual(stage["exit_code"] == 0, stage["name"] == "sorry-admission")

    def test_changed_claim_fields_and_types(self):
        for field, value in (("theorem", "TMOracle.Checks.halted_fixed"), ("conclusion", {}),
                             ("pair_id", "tm-pair:bb4:v1")):
            with self.subTest(field=field):
                self.reject_receipt(lambda r, o: r["claim"].update({field: value}), "receipt claim differs")
        self.reject_receipt(lambda r, o: r["claim"]["values"]["left"].update(initial_state=False), "receipt claim differs")
        self.reject_receipt(lambda r, o: r["claim"]["conclusion"].update(first_halt=[2, 2]), "receipt claim differs")
        self.reject_receipt(lambda r, o: r["claim"]["values"].update(input=[0]), "receipt claim differs")

    def test_wrong_command_or_cwd(self):
        for change in ({"command": ["lake", "env", "lean", "--version"]}, {"cwd": "lean/tm"}):
            self.reject_receipt(lambda r, o: r["stages"][5].update(change), "wrong command: kernel")

    def test_missing_report_even_with_updated_artifact_hash(self):
        def mutate(r, out):
            path = out / "axioms.log"
            path.write_text("\n".join(path.read_text(encoding="utf-8").splitlines()[1:]), encoding="utf-8")
            r["artifacts"]["axioms.log"] = proof.digest(path)
        self.reject_receipt(mutate, "missing or duplicate axiom")

    def test_changed_source_after_build(self):
        hashes = copy.deepcopy(self.receipt["source_hashes"])
        hashes["lean/tm-pair/TinyPair.lean"] = "0" * 64
        with patch.object(proof, "source_hashes", return_value=hashes):
            with self.assertRaisesRegex(ValueError, "source changed"):
                proof.replay(self.out)

    def test_missing_artifact_or_failed_receipt(self):
        self.reject_receipt(lambda r, o: r["artifacts"].pop("kernel.log"), "missing proof artifacts")
        self.reject_receipt(lambda r, o: r.update(status="failed"), "did not pass")
        self.reject_receipt(lambda r, o: r.update(schema_version=True), "did not pass")
        self.reject_receipt(lambda r, o: r.update(limits=[]), "interpretation differs")

    def test_admitted_custom_missing_duplicate_axiom_rejected(self):
        for log in ("", "'X' depends on axioms: [sorryAx]", "'X' depends on axioms: [Lean.ofReduceBool]",
                    "'X' depends on axioms: [myAxiom]", "'X' does not depend on any axioms\n'X' does not depend on any axioms"):
            with self.subTest(log=log), self.assertRaises(ValueError):
                proof.audit_axioms(log, ["X"])
        self.assertEqual(proof.audit_axioms("'X' does not depend on any axioms", ["X"]), {"X": []})

    def test_redirected_or_extra_path_dependency_rejected(self):
        original = proof.read
        for extra in (False, True):
            def changed(path):
                data = original(path)
                if Path(path) == proof.ROOT / proof.PROJECT / "lake-manifest.json":
                    if extra:
                        data["packages"].append(copy.deepcopy(data["packages"][0]))
                    else:
                        data["packages"][0]["dir"] = "../elsewhere"
                return data
            with patch.object(proof, "read", side_effect=changed):
                with self.assertRaisesRegex(ValueError, "local machine dependency"):
                    proof.validate_project(proof.ROOT)

    def test_generator_rejects_invalid_domains_and_theorem_syntax(self):
        for change in ("bool", "negative", "move", "theorem"):
            c = copy.deepcopy(self.receipt["claim"])
            if change == "bool":
                c["values"]["left"]["initial_state"] = False
            elif change == "negative":
                c["values"]["input"] = [-1]
            elif change == "move":
                c["values"]["right"]["table"][0][2] = 3
            else:
                c["theorem"] = "x\naxiom injected : False"
            with self.subTest(change=change), self.assertRaises((ValueError, TypeError)):
                proof.binding(c)


if __name__ == "__main__":
    unittest.main()
