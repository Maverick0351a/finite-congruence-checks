"""Independent finite-oracle and leakage controls for the repair pilot."""

import copy
import importlib.util
from itertools import combinations, permutations, product
import json
from pathlib import Path
import unittest


SCRIPT = Path(__file__).with_name("repair_tasks.py")
SPEC = importlib.util.spec_from_file_location("repair_tasks_under_test", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
repair = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(repair)


def canonical(labels):
    seen = []
    result = []
    for label in labels:
        if label not in seen:
            seen.append(label)
        result.append(seen.index(label))
    return tuple(result)


def initial_fails(operation, labels):
    return any(labels[x] == labels[y] and labels[operation[x]] != labels[operation[y]]
               for x in range(4) for y in range(4))


def independent_closure(operation, labels):
    """Union-find closure, rather than the oracle's partition enumeration."""
    parent = list(range(4))

    def find(x):
        while parent[x] != x:
            x = parent[x]
        return x

    def merge(x, y):
        x, y = find(x), find(y)
        if x == y:
            return False
        parent[y] = x
        return True

    for x in range(4):
        for y in range(4):
            if labels[x] == labels[y]:
                merge(x, y)
    changed = True
    while changed:
        changed = False
        for x in range(4):
            for y in range(4):
                if find(x) == find(y):
                    changed = merge(operation[x], operation[y]) or changed
    return list(canonical([find(x) for x in range(4)]))


def operation_family(operation):
    images = []
    for order in permutations(range(4)):
        # order[new] = old, independently written from the builder's map.
        inverse = {old: new for new, old in enumerate(order)}
        images.append(tuple(inverse[operation[old]] for old in order))
    return min(images)


SAT = {"id": "example", "operation": [0, 2, 2, 3],
       "initial_labels": [0, 0, 1, 2], "separate": [0, 3]}
UNSAT = {"id": "cascade", "operation": [1, 2, 3, 3],
         "initial_labels": [0, 0, 1, 2], "separate": [0, 3]}


class RepairTasksTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = repair.build_dataset()

    def test_all_partitions_match_independent_label_assignment_generation(self):
        expected = {canonical(labels) for labels in product(range(4), repeat=4)}
        actual = repair.partitions()
        self.assertEqual(len(actual), 15)
        self.assertEqual({tuple(labels) for labels in actual}, expected)
        actual[0][0] = 3
        self.assertEqual(repair.partitions()[0][0], 0)

    def test_encoding_fixtures_and_strict_validation(self):
        self.assertEqual(repair.encode([0, 2, 2, 3], [0, 0, 1, 2]), 0x90E8)
        self.assertEqual(repair.encode([0, 2, 2, 2], [0, 0, 1, 1]), 0x50A8)
        self.assertEqual(repair.encode([3] * 4, [3] * 4), 65535)
        self.assertEqual(repair.encode([0] * 4, [0] * 4), 0)
        for bad in ([True, 0, 0, 0], [0.0, 0, 0, 0], [4, 0, 0, 0],
                    [-1, 0, 0, 0], [0, 0, 0], (0, 0, 0, 0), None):
            with self.subTest(bad=bad):
                with self.assertRaises(ValueError):
                    repair.encode(bad, [0] * 4)
                with self.assertRaises(ValueError):
                    repair.encode([0] * 4, bad)

    def test_oracle_matches_independent_closure_on_all_8832_tasks(self):
        independent_partitions = sorted({canonical(labels) for labels in product(range(4), repeat=4)})
        tasks = sat = two_block = 0
        for operation in product(range(4), repeat=4):
            for labels in independent_partitions:
                if not initial_fails(operation, labels):
                    continue
                closure = independent_closure(operation, labels)
                for a, b in combinations(range(4), 2):
                    if labels[a] == labels[b]:
                        continue
                    task = {"operation": list(operation), "initial_labels": list(labels), "separate": [a, b]}
                    solutions = repair.solve(task)
                    expected = [closure] if closure[a] != closure[b] else []
                    self.assertEqual(solutions, expected, task)
                    tasks += 1
                    sat += bool(solutions)
                    if len(set(labels)) == 2:
                        two_block += 1
                        self.assertEqual(solutions, [], task)
        self.assertEqual((tasks, sat, two_block), (8832, 2112, 4032))

    def test_valid_repair_accepts_label_aliases(self):
        self.assertEqual(repair.solve(SAT), [[0, 0, 0, 1]])
        self.assertTrue(repair.grade(SAT, {"status": "repair", "group_labels": [2, 2, 2, 3]})["correct"])
        self.assertFalse(repair.grade(SAT, {"status": "impossible", "group_labels": None})["correct"])

    def test_universal_fallback_and_splitting_cannot_receive_credit(self):
        universal = repair.grade(SAT, {"status": "repair", "group_labels": [0] * 4})
        split = repair.grade(SAT, {"status": "repair", "group_labels": [0, 1, 2, 3]})
        unchanged = repair.grade(SAT, {"status": "repair", "group_labels": SAT["initial_labels"]})
        self.assertFalse(universal["correct"])
        self.assertIn("separation_violated", universal["reason"])
        self.assertFalse(split["correct"])
        self.assertIn("splits_original_block", split["reason"])
        self.assertFalse(unchanged["correct"])
        self.assertIn("not_preserved", unchanged["reason"])

    def test_impossibility_is_graded_by_complete_oracle(self):
        self.assertEqual(repair.solve(UNSAT), [])
        self.assertTrue(repair.grade(UNSAT, {"status": "impossible", "group_labels": None})["correct"])
        self.assertFalse(repair.grade(UNSAT, {"status": "impossible", "group_labels": [0] * 4})["correct"])

    def test_answer_shape_is_exact_and_strict(self):
        invalid = [None, [], {}, {"status": "repair"},
                   {"status": True, "group_labels": None},
                   {"status": "unsat", "group_labels": None},
                   {"status": "repair", "group_labels": [False, 0, 0, 1]},
                   {"status": "repair", "group_labels": [0, 0, 0, 1], "operation": [0] * 4},
                   {"status": "repair", "group_labels": [0, 0, 0, 1], "rationale": "extra"}]
        for answer in invalid:
            with self.subTest(answer=answer):
                result = repair.grade(SAT, answer)
                self.assertFalse(result["correct"])
                self.assertIn("invalid_answer", result["reason"])

    def test_invalid_task_fails_instead_of_becoming_a_model_error(self):
        for field, value in (("separate", [0, 1]), ("separate", [True, 3]),
                             ("initial_labels", [0, 1, 2, 3]), ("operation", [0, 0, 0, 0])):
            task = copy.deepcopy(SAT)
            task[field] = value
            with self.subTest(field=field, value=value):
                with self.assertRaises(ValueError):
                    repair.grade(task, {"status": "impossible", "group_labels": None})

    def test_public_prompt_excludes_oracle_split_and_family(self):
        task = self.data["tasks"][0]
        public = repair.public_task(task)
        self.assertEqual(set(public), {"id", "operation", "initial_labels", "separate"})
        public["operation"][0] = 99
        self.assertNotEqual(task["operation"][0], 99)
        self.assertNotIn("answer_class", json.dumps(repair.public_task(task)))
        self.assertNotIn("solution", json.dumps(repair.public_task(task)))

    def test_splits_are_balanced_and_operation_conjugacy_disjoint(self):
        families = {"dev": set(), "test": set()}
        for split, expected in (("dev", 4), ("test", 12)):
            tasks = [task for task in self.data["tasks"] if task["split"] == split]
            self.assertEqual(len(tasks), expected)
            self.assertEqual(sum(bool(repair.solve(task)) for task in tasks), expected // 2)
            for task in tasks:
                self.assertTrue(initial_fails(task["operation"], task["initial_labels"]))
                self.assertEqual(len(set(task["initial_labels"])), 3)
                families[split].add(operation_family(task["operation"]))
        self.assertEqual((len(families["dev"]), len(families["test"])), (2, 6))
        self.assertFalse(families["dev"] & families["test"])
        self.assertEqual(len({task["id"] for task in self.data["tasks"]}), 16)

    def test_task_orbits_have_no_duplicate_and_ids_match_semantic_keys(self):
        orbits = set()
        for task in self.data["tasks"]:
            orbit = []
            for order in permutations(range(4)):
                inverse = {old: new for new, old in enumerate(order)}
                operation = tuple(inverse[task["operation"][old]] for old in order)
                labels = canonical([task["initial_labels"][old] for old in order])
                pair = tuple(sorted(inverse[old] for old in task["separate"]))
                orbit.append((operation, labels, pair))
            key = min(orbit)
            self.assertNotIn(key, orbits)
            orbits.add(key)
            self.assertEqual(task["id"], repair._identifier("repair-v1:", key))

    def test_census_and_saved_dataset_are_reproducible(self):
        universe = self.data["universe"]
        self.assertEqual(universe["eligible_labeled_tasks"], 8832)
        self.assertEqual(universe["labeled_class_counts"], {"sat": 2112, "unsat": 6720})
        self.assertEqual(universe["task_isomorphism_classes"], 378)
        self.assertEqual(universe["orbit_class_counts"], {"sat": 88, "unsat": 290})
        self.assertEqual(universe["eligible_operation_conjugacy_classes"], 17)
        self.assertEqual(repair.build_dataset(), self.data)
        self.assertEqual(repair.DATASET_PATH.read_bytes(), repair.dataset_bytes(self.data))


if __name__ == "__main__":
    unittest.main(verbosity=2)
