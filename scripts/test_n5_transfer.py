"""Independent finite checks and evidence/claim mismatch controls; no model calls."""
import copy
import itertools
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

import n5_transfer as transfer
import query_context as query


def compatible(ops, partition):
    return all(partition[x] != partition[y] or partition[op[x]] == partition[op[y]]
               for op in ops for x in range(4) for y in range(4))


def relation(partition):
    return frozenset((x, y) for x in range(4) for y in range(4) if partition[x] == partition[y])


class RenamingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.record = query.explain_claim(transfer.CLAIM_ID)
        cls.claim = transfer.read(transfer.ROOT / transfer.CLAIM_PATH)

    def test_saved_proof_and_query(self):
        receipt = transfer.replay()
        self.assertEqual(len(receipt["stages"]), 9)
        self.assertEqual(set(receipt["axioms"]), set(transfer.DECLARATIONS))
        self.assertEqual(query.check_record(self.record)["status"], "supported")
        self.assertIn("no Lean execution", self.record["claim"]["proof_evidence"]["validation"])

    def test_exact_worked_example(self):
        self.assertEqual(self.claim["values"]["target"], {
            "operations": [[2, 1, 2, 1], [3, 2, 1, 0]],
            "groupings": [[0, 1, 2, 3], [0, 1, 1, 2], [0, 1, 1, 0], [0, 1, 0, 1], [0, 0, 0, 0]]})
        self.assertEqual(self.claim["mapping"]["object_backward_target_to_source"], [3, 0, 1, 2])

    def test_all_24_carrier_and_two_rule_permutations(self):
        # Independent all-pairs relations and direct compatibility, not table identity.
        partitions = list({tuple(transfer.source.normalize(p)) for p in itertools.product(range(4), repeat=4)})
        src = self.claim["values"]["source"]
        valid_source = [relation(p) for p in partitions if compatible(src["operations"], p)]
        self.assertEqual(len(partitions), 15)
        self.assertEqual(len(valid_source), 5)
        for p in itertools.permutations(range(4)):
            for rules in ([0, 1], [1, 0]):
                with self.subTest(objects=p, rules=rules):
                    inv, ops, groups = transfer.permuted(src["operations"], src["groupings"], list(p), rules)
                    self.assertEqual([inv[p[x]] for x in range(4)], list(range(4)))
                    for j, x in itertools.product(range(2), range(4)):
                        self.assertEqual(ops[j][p[x]], p[src["operations"][rules[j]][x]])
                    transported = [frozenset((p[x], p[y]) for x, y in r) for r in valid_source]
                    recomputed = {relation(q) for q in partitions if compatible(ops, q)}
                    self.assertEqual(set(transported), recomputed)
                    self.assertEqual({relation(q) for q in groups}, recomputed)
                    for a, b in itertools.product(range(5), repeat=2):
                        self.assertEqual(valid_source[a] <= valid_source[b], transported[a] <= transported[b])

    def test_partial_renaming_breaks_a_grouping(self):
        ops = self.claim["values"]["source"]["operations"]
        target_groups = self.claim["values"]["target"]["groupings"]
        self.assertTrue(any(not compatible(ops, p) for p in target_groups))

    def test_changed_claims_rejected(self):
        mutations = [
            lambda c: c["values"]["target"]["operations"][0].__setitem__(0, 0),
            lambda c: c["values"]["target"]["groupings"][1].__setitem__(2, 2),
            lambda c: c["mapping"].__setitem__("object_forward_source_to_target", [3, 0, 1, 2]),
            lambda c: c["mapping"].__setitem__("rule_target_to_source", [0, 1]),
            lambda c: c["mapping"].__setitem__("grouping_source_to_target", [1, 0, 2, 3, 4]),
            lambda c: c.__setitem__("source_claim_id", "construction:n4-E16709"),
            lambda c: c.__setitem__("theorem", "FiniteCongruenceChecks.B3.all_relations"),
            lambda c: c["conclusion"].__setitem__("distinct_groupings", 4),
            lambda c: c["conclusion"].__setitem__("inclusion_order_preserved", 1),
            lambda c: c["values"]["carrier"].__setitem__(1, True),
            lambda c: c["values"]["carrier"].__setitem__(1, 1.0),
        ]
        for i, mutate in enumerate(mutations):
            with self.subTest(mutation=i):
                changed = copy.deepcopy(self.record)
                mutate(changed["claim"])
                self.assertEqual(query.check_record(changed)["status"], "unsupported")

    def test_invalid_maps_and_injection_rejected(self):
        src = self.claim["values"]["source"]
        for p in ([0, 0, 2, 3], [0, 1, 2, 4], [False, 1, 2, 3], [0, 1, 2], [0., 1, 2, 3]):
            with self.assertRaises(ValueError):
                transfer.permuted(src["operations"], src["groupings"], p, [1, 0])
        for sigma in ([0, 0], [False, 1], [0, 2]):
            with self.assertRaises(ValueError):
                transfer.permuted(src["operations"], src["groupings"], [1, 2, 3, 0], sigma)
        changed = copy.deepcopy(self.claim)
        changed["theorem"] = "proof\naxiom hacked : False"
        with self.assertRaises(ValueError):
            transfer.binding(changed)

    def test_actual_lean_rejections(self):
        receipt = transfer.replay()
        for stage in receipt["stages"][4:]:
            self.assertNotEqual(stage["exit_code"], 0)
            log = (transfer.ROOT / transfer.EVIDENCE / (stage["name"] + ".log")).read_text(encoding="utf-8")
            self.assertIn("error:", log)
        self.assertIn("rule_correspondence", (transfer.ROOT / transfer.BINDING).read_text(encoding="utf-8"))

    def test_corrupted_receipts(self):
        for modify in (
            lambda r: r["stages"][0].__setitem__("command", ["true"]),
            lambda r: r["stages"][0].__setitem__("cwd", "lean/tm"),
            lambda r: r["stages"].pop(),
            lambda r: r["stages"][4].__setitem__("exit_code", 0),
            lambda r: r.__setitem__("schema_version", True),
            lambda r: r["claim"]["conclusion"].__setitem__("inclusion_order_preserved", 1),
            lambda r: r["artifacts"].pop("kernel.log"),
        ):
            with tempfile.TemporaryDirectory() as folder:
                out = Path(folder) / "evidence"
                shutil.copytree(transfer.ROOT / transfer.EVIDENCE, out)
                receipt = transfer.read(out / "summary.json")
                modify(receipt)
                (out / "summary.json").write_bytes(transfer.encode(receipt))
                with self.assertRaises(ValueError):
                    transfer.replay(out)

    def test_axiom_gate_rejects_admission_or_missing_report(self):
        log = (transfer.ROOT / transfer.EVIDENCE / "axioms.log").read_text(encoding="utf-8")
        for invalid in ("\n".join(log.splitlines()[1:]), log + log,
                        log.replace("propext", "sorryAx"), log.replace("propext", "Lean.ofReduceBool")):
            with self.assertRaises(ValueError):
                transfer.audit_axioms(invalid, transfer.DECLARATIONS)

    def test_source_and_dependency_mismatch(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            for relative in transfer.source_hashes():
                target = root / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(transfer.ROOT / relative, target)
            shutil.copytree(transfer.ROOT / transfer.EVIDENCE, root / transfer.EVIDENCE, dirs_exist_ok=True)
            transfer.replay(root=root)
            proof = root / transfer.PROJECT / "Renaming.lean"
            proof.write_text(proof.read_text(encoding="utf-8") + "\n-- changed\n", encoding="utf-8")
            with self.assertRaises(ValueError):
                transfer.replay(root=root)
            manifest = root / transfer.PROJECT / "lake-manifest.json"
            data = transfer.read(manifest)
            data["packages"][0]["dir"] = "../tm"
            manifest.write_bytes(transfer.encode(data))
            with self.assertRaises(ValueError):
                transfer.validate_project(root)

    def test_cli_round_trip(self):
        with tempfile.TemporaryDirectory() as folder:
            candidate = Path(folder) / "transfer.json"
            command = [sys.executable, str(transfer.ROOT / "scripts/query_context.py")]
            result = subprocess.run(command + ["explain", transfer.CLAIM_ID, "--out", str(candidate)], capture_output=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            checked = subprocess.run(command + ["check", str(candidate)], capture_output=True)
            self.assertEqual(checked.returncode, 0, checked.stderr)
            self.assertEqual(json.loads(checked.stdout)["status"], "supported")

    def test_import_configuration_redirects_rejected_before_run(self):
        core_config = (transfer.ROOT / "lean/lakefile.toml").read_text(encoding="utf-8")
        manifest = transfer.read(transfer.ROOT / "lean/lake-manifest.json")
        redirected_manifest = dict(manifest, lakeDir="alternate-build")
        for relative, replacement in (
            ("lean/lakefile.toml", core_config.replace('name = "FiniteCongruenceChecks"',
                'name = "FiniteCongruenceChecks"\nsrcDir = "alternate"')),
            ("lean/lakefile.toml", core_config.replace('name = "CertificateData"',
                'name = "CertificateData"\nsrcDir = "alternate"')),
            ("lean/lake-manifest.json", json.dumps(redirected_manifest)),
            ("lean/lakefile.lean", "import Lake\nopen Lake DSL\npackage alternate\n"),
            (transfer.PROJECT + "/lakefile.lean", "import Lake\nopen Lake DSL\npackage alternate\n"),
        ):
            with self.subTest(path=relative, replacement=replacement), tempfile.TemporaryDirectory() as folder:
                root = Path(folder)
                for project in ("lean", transfer.PROJECT):
                    for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
                        target = root / project / name
                        target.parent.mkdir(parents=True, exist_ok=True)
                        shutil.copyfile(transfer.ROOT / project / name, target)
                transfer.validate_project(root)
                (root / relative).write_text(replacement, encoding="utf-8")
                out = root / "unstarted"
                with self.assertRaises(ValueError):
                    transfer.run(out, root)
                self.assertFalse(out.exists())


if __name__ == "__main__":
    unittest.main()
