"""Admitted proofs and partial axiom reports must fail the formal-check gate."""
import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location("check_axioms", Path(__file__).with_name("check_axioms.py"))
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)


class AxiomTests(unittest.TestCase):
    def report(self):
        return "\n".join(f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
                         for name in audit.EXPECTED)

    def test_complete_standard_axiom_report(self):
        self.assertTrue(audit.check(self.report())["passed"])

    def test_admitted_and_native_proofs_rejected(self):
        for axiom in ("sorryAx", "Lean.ofReduceBool", "inventedAxiom"):
            with self.subTest(axiom=axiom), self.assertRaisesRegex(ValueError, "Unapproved"):
                audit.check(self.report().replace("propext", axiom, 1))

    def test_missing_declaration_rejected(self):
        with self.assertRaisesRegex(ValueError, "Incomplete"):
            audit.check("\n".join(self.report().splitlines()[1:]))

    def test_duplicate_declaration_rejected(self):
        with self.assertRaisesRegex(ValueError, "Duplicate"):
            audit.check(self.report() + "\n" + self.report().splitlines()[0])


if __name__ == "__main__":
    unittest.main()
