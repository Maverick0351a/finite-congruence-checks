"""Independent finite observations and precise evidence-binding regressions."""
import copy
import itertools
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

import n5_reverse_transfer as transfer


def partitions(prefix=(0,)):
    """Enumerate restricted growth strings independently of the exporter."""
    if len(prefix) == 4:
        yield prefix
    else:
        for label in range(max(prefix) + 2):
            yield from partitions(prefix + (label,))


def relation(grouping):
    return frozenset((x, y) for x in range(4) for y in range(4) if grouping[x] == grouping[y])


def compatible(operations, grouping):
    return all(grouping[x] != grouping[y] or grouping[op[x]] == grouping[op[y]]
               for op in operations for x in range(4) for y in range(4))


def copy_sources(root):
    for relative in transfer.source_hashes():
        target = root / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(transfer.ROOT / relative, target)
    shutil.copytree(transfer.ROOT / transfer.EVIDENCE, root / transfer.EVIDENCE, dirs_exist_ok=True)


class ReverseLabelsTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.claim = transfer.check_binding()

    def test_saved_receipt_and_original_receipt(self):
        receipt = transfer.replay()
        self.assertEqual(len(receipt["stages"]), 12)
        self.assertEqual(len(receipt["axioms"]), 22)
        self.assertEqual(set(receipt["axioms"]), set(transfer.DECLARATIONS))
        self.assertEqual(transfer.original.replay()["status"], "passed")
        metadata, claim = transfer.explain()
        self.assertEqual(metadata["path"], transfer.CLAIM_PATH)
        self.assertIn("no Lean execution", claim["proof_evidence"]["validation"])

    def test_reverse_labels_and_identity_rule_order(self):
        self.assertEqual(self.claim["mapping"], {
            "object_forward_source_to_target": [3, 2, 1, 0],
            "object_backward_target_to_source": [3, 2, 1, 0],
            "rule_target_to_source": [0, 1], "grouping_source_to_target": [0, 1, 2, 3, 4]})
        self.assertEqual(self.claim["values"]["target"], {
            "operations": [[1, 0, 3, 2], [2, 3, 2, 3]],
            "groupings": [[0, 1, 2, 3], [0, 1, 2, 2], [0, 0, 1, 1], [0, 1, 0, 1], [0, 0, 0, 0]]})

    def test_independent_all_fifteen_partitions(self):
        cases = list(partitions())
        self.assertEqual(len(cases), 15)
        self.assertEqual(len(set(cases)), 15)
        src, dst = self.claim["values"]["source"], self.claim["values"]["target"]
        forward = self.claim["mapping"]["object_forward_source_to_target"]
        source_valid = {relation(p) for p in cases if compatible(src["operations"], p)}
        target_valid = {relation(p) for p in cases if compatible(dst["operations"], p)}
        transported = {frozenset((forward[x], forward[y]) for x, y in rel) for rel in source_valid}
        self.assertEqual(len(source_valid), 5)
        self.assertEqual(len(target_valid), 5)
        self.assertEqual(target_valid, transported)
        self.assertEqual(target_valid, {relation(p) for p in dst["groupings"]})
        for j, x in itertools.product(range(2), range(4)):
            self.assertEqual(dst["operations"][j][forward[x]], forward[src["operations"][j][x]])
        for a, b in itertools.product(range(5), repeat=2):
            self.assertEqual(relation(src["groupings"][a]) <= relation(src["groupings"][b]),
                             relation(dst["groupings"][a]) <= relation(dst["groupings"][b]))

    def test_partial_rename_has_concrete_violating_pair(self):
        grouping = self.claim["values"]["target"]["groupings"][1]
        old_rule = self.claim["values"]["source"]["operations"][1]
        new_rule = self.claim["values"]["target"]["operations"][1]
        self.assertEqual(grouping[2], grouping[3])
        self.assertEqual([old_rule[2], old_rule[3]], [0, 1])
        self.assertNotEqual(grouping[old_rule[2]], grouping[old_rule[3]])
        self.assertEqual(grouping[new_rule[2]], grouping[new_rule[3]])

    def test_changed_record_fields_fail_exact_binding(self):
        mutations = (
            lambda c: c["values"]["target"]["operations"][1].__setitem__(0, 0),
            lambda c: c["values"]["target"]["groupings"][1].__setitem__(2, 1),
            lambda c: c["mapping"].__setitem__("rule_target_to_source", [1, 0]),
            lambda c: c["mapping"].__setitem__("object_backward_target_to_source", [0, 1, 2, 3]),
            lambda c: c["conclusion"].__setitem__("distinct_groupings", 4),
            lambda c: c["conclusion"].__setitem__("inclusion_order_preserved", 1),
            lambda c: c.__setitem__("theorem", "FiniteCongruenceChecks.B3.all_relations"),
            lambda c: c.__setitem__("source_construction_id", "n4-E16709"),
            lambda c: c["values"]["carrier"].__setitem__(1, True),
        )
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            copy_sources(root)
            transfer.check_binding(root)
            for i, mutate in enumerate(mutations):
                with self.subTest(mutation=i):
                    claim = copy.deepcopy(self.claim)
                    mutate(claim)
                    (root / transfer.CLAIM_PATH).write_bytes(transfer.encode(claim))
                    with self.assertRaises(ValueError):
                        transfer.check_binding(root)

    def test_binding_rejects_unrepresentable_meaning_and_injection(self):
        for key, value in (("quantifier", "some relations"), ("predicate", "same diagram"),
                           ("distinct_groupings", True), ("inclusion_order_preserved", 1)):
            claim = copy.deepcopy(self.claim)
            claim["conclusion"][key] = value
            with self.assertRaises(ValueError):
                transfer.binding(claim)
        claim = copy.deepcopy(self.claim)
        claim["theorem"] = "proof\naxiom bad : False"
        with self.assertRaises(ValueError):
            transfer.binding(claim)

    def test_actual_lean_rejects_eight_false_bindings(self):
        receipt = transfer.replay()
        expected = set(transfer.controls(self.claim))
        self.assertEqual(len(expected), 8)
        self.assertEqual({s["name"] for s in receipt["stages"][4:]}, expected)
        for stage in receipt["stages"][4:]:
            self.assertNotEqual(stage["exit_code"], 0)
            self.assertIn("error:", (transfer.ROOT / transfer.EVIDENCE / (stage["name"] + ".log")).read_text(encoding="utf-8"))
        lean = transfer.binding(self.claim)
        self.assertIn("r : V → V → Prop", lean)
        self.assertIn("↔ ∃ a : Fin 5, ∀ x y", lean)
        self.assertIn("dstGroup b x = dstGroup b y", lean)

    def test_corrupted_receipts_and_artifacts_rejected(self):
        mutations = (
            lambda r: r["stages"][0].__setitem__("command", ["true"]),
            lambda r: r["stages"][0].__setitem__("cwd", "lean/renaming"),
            lambda r: r["stages"].pop(),
            lambda r: r["stages"][4].__setitem__("exit_code", 0),
            lambda r: r.__setitem__("schema_version", True),
            lambda r: r["artifacts"].pop("kernel.log"),
        )
        for mutate in mutations:
            with tempfile.TemporaryDirectory() as folder:
                out = Path(folder) / "evidence"
                shutil.copytree(transfer.ROOT / transfer.EVIDENCE, out)
                receipt = transfer.read(out / "summary.json")
                mutate(receipt)
                (out / "summary.json").write_bytes(transfer.encode(receipt))
                with self.assertRaises(ValueError):
                    transfer.replay(out)
        with tempfile.TemporaryDirectory() as folder:
            out = Path(folder) / "evidence"
            shutil.copytree(transfer.ROOT / transfer.EVIDENCE, out)
            (out / "kernel.log").write_text("corrupted", encoding="utf-8")
            with self.assertRaises(ValueError):
                transfer.replay(out)

    def test_source_and_helper_drift_rejected(self):
        for relative in (transfer.PROJECT + "/N5ReverseLabels.lean", "lean/renaming/Renaming.lean",
                         "scripts/n5_transfer.py", "scripts/n5_reverse_transfer.py"):
            with self.subTest(path=relative), tempfile.TemporaryDirectory() as folder:
                root = Path(folder)
                copy_sources(root)
                target = root / relative
                target.write_bytes(target.read_bytes() + b"\n")
                with self.assertRaises(ValueError):
                    transfer.replay(root=root)

    def test_dependency_redirects_stop_before_execution(self):
        for project in ("lean", "lean/renaming", transfer.PROJECT):
            for name in ("lakefile.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain"):
                with self.subTest(project=project, name=name), tempfile.TemporaryDirectory() as folder:
                    root = Path(folder)
                    copy_sources(root)
                    target = root / project / name
                    if name == "lakefile.lean":
                        replacement = "import Lake\n"
                    elif name == "lakefile.toml":
                        replacement = target.read_text(encoding="utf-8") + '\nsrcDir = "elsewhere"\n'
                    elif name == "lake-manifest.json":
                        value = transfer.read(target)
                        value["lakeDir"] = "elsewhere"
                        replacement = json.dumps(value)
                    else:
                        replacement = "leanprover/lean4:v4.0.0\n"
                    target.write_text(replacement, encoding="utf-8")
                    out = root / "unstarted"
                    with self.assertRaises(ValueError):
                        transfer.run(out, root)
                    self.assertFalse(out.exists())

    def test_axiom_gate_rejects_admission_or_missing_report(self):
        log = (transfer.ROOT / transfer.EVIDENCE / "axioms.log").read_text(encoding="utf-8")
        for invalid in ("\n".join(log.splitlines()[1:]), log + log,
                        log.replace("propext", "sorryAx"), log.replace("propext", "Lean.ofReduceBool")):
            with self.assertRaises(ValueError):
                transfer.audit_axioms(invalid, transfer.DECLARATIONS)

    def test_cli_receipt_replay(self):
        result = subprocess.run([sys.executable, str(transfer.ROOT / "scripts/n5_reverse_transfer.py"), "replay"],
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(transfer.CLAIM_ID, result.stdout)


if __name__ == "__main__":
    unittest.main()
