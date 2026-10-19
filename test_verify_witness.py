"""Independent verifier tests; no imports from the search implementation."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import verify_witness as verifier


def chain(size):
    return dict(name=f"C{size}", elements=[str(x) for x in range(size)], bottom=0,
                leq=[[a <= b for b in range(size)] for a in range(size)],
                join=[[max(a, b) for b in range(size)] for a in range(size)])


def boolean_square():
    return dict(name="B2", elements=["0", "a", "b", "1"], bottom=0,
                leq=[[(a | b) == b for b in range(4)] for a in range(4)],
                join=[[a | b for b in range(4)] for a in range(4)])


class VerifierTests(unittest.TestCase):
    def test_chain_and_literal_ordered_seed_count(self):
        result = verifier.verify_witness(chain(3), [[0, 1, 2], [1, 0, 2], [2, 2, 0]])
        self.assertTrue(result["passed"])
        self.assertEqual(result["admissible_self_maps"], 15)
        self.assertEqual(result["nonempty_ordered_seed_subsets_enumerated"], 511)
        self.assertEqual(result["lattice_validation"]["derived_meet"],
                         [[min(a, b) for b in range(3)] for a in range(3)])

    def test_nonchain_join_uses_lattice_table(self):
        result = verifier.verify_witness(boolean_square(), [[0, 1, 2], [1, 0, 3], [2, 3, 0]])
        self.assertTrue(result["passed"])

    def test_connectivity_can_fail_after_all_structural_conjuncts_pass(self):
        color = [[0, 1, 2, 3], [1, 0, 3, 3], [2, 3, 0, 3], [3, 3, 3, 0]]
        result = verifier.verify_witness(boolean_square(), color)
        self.assertFalse(result["passed"])
        self.assertTrue(all(result["checks"][key] for key in
                            ("symmetric", "bottom_iff_diagonal", "triangle_join", "order_separation")))
        self.assertFalse(result["checks"]["seed_connectivity"])
        self.assertEqual(result["nonempty_ordered_seed_subsets_enumerated"], 65535)
        self.assertEqual(result["first_connectivity_failure"]["ordered_seeds"], [[0, 1], [0, 2]])
        self.assertEqual(result["first_connectivity_failure"]["disconnected_pair_below_bound"], [0, 3])

    def test_bottom_index_is_not_assumed_to_be_zero(self):
        lattice = dict(name="reordered C2", elements=["top", "bottom"], bottom=1,
                       leq=[[True, False], [True, True]], join=[[0, 0], [0, 1]])
        self.assertTrue(verifier.verify_witness(lattice, [[1, 0], [0, 1]])["passed"])

    def test_bfs_adds_reflexivity_symmetry_and_transitivity(self):
        # Directed marked edges 1->0 and 1->2; vertex 3 remains isolated.
        self.assertEqual(verifier.equivalence_closure(4, (1 << 4) | (1 << 6)), (7, 7, 7, 8))

    def test_trivial_lattice_and_single_vertex(self):
        result = verifier.verify_witness(chain(1), [[0]])
        self.assertTrue(result["passed"])
        self.assertEqual(result["nonempty_ordered_seed_subsets_enumerated"], 1)

    def test_malformed_inputs_and_lattice_laws(self):
        cases = []
        duplicate = chain(2)
        duplicate["elements"][1] = "0"
        cases.append((duplicate, [[0, 1], [1, 0]]))
        reflexive = chain(2)
        reflexive["leq"][1][1] = False
        cases.append((reflexive, [[0, 1], [1, 0]]))
        antisymmetric = chain(2)
        antisymmetric["leq"][1][0] = True
        cases.append((antisymmetric, [[0, 1], [1, 0]]))
        transitive = chain(4)
        transitive["leq"][1][3] = False
        cases.append((transitive, [[0, 1], [1, 0]]))
        bad_join = boolean_square()
        bad_join["join"][1][2] = 2
        cases.append((bad_join, [[0, 1], [1, 0]]))
        numeric_order = chain(2)
        numeric_order["leq"][0][1] = 1
        cases.append((numeric_order, [[0, 1], [1, 0]]))
        boolean_index = chain(2)
        boolean_index["join"][0][0] = False
        cases.append((boolean_index, [[0, 1], [1, 0]]))
        cases.extend([(chain(2), []), (chain(2), [[0, 1], [1]]),
                      (chain(2), [[0, True], [1, 0]]), (chain(2), [[0, 2], [2, 0]])])
        for lattice, color in cases:
            with self.subTest(lattice=lattice, color=color), self.assertRaises(ValueError):
                verifier.verify_witness(lattice, color)

    def test_limit_is_incomplete_verification(self):
        with self.assertRaises(verifier.VerificationLimit):
            verifier.verify_witness(chain(2), [[0, 1], [1, 0]], max_seed_subsets=14)

    def test_cli_exit_status_and_json_evidence(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path, output = root / "certificate.json", root / "result.json"
            cases = [([[0, 1], [1, 0]], 0), ([[0, 0], [0, 0]], 1), ([[0, 2], [2, 0]], 2)]
            for color, expected in cases:
                path.write_text(json.dumps(dict(lattice=chain(2), color=color)))
                run = subprocess.run([sys.executable, str(Path(verifier.__file__)), str(path),
                                      "--output", str(output)], capture_output=True, text=True)
                self.assertEqual(run.returncode, expected, run.stderr)
                result = json.loads(output.read_text())
                self.assertEqual(result["passed"], expected == 0)
                self.assertIsNotNone(result["certificate_sha256"])
                self.assertEqual(result["verification_completed"], expected != 2)


if __name__ == "__main__":
    unittest.main()
