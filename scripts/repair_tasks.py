"""Small, reproducible constrained grouping-repair tasks on four objects.

The oracle enumerates all 15 partitions. It does not import the prior repair
algorithm or use its merge closure to choose answers. The evaluator checks a
fixed unary operation, retention of every original equivalence, and separation
of one designated pair. It is computational evaluation code, not a Lean proof
of the constrained repair oracle or a machine-code result.

Only public_task(task) is appropriate for a model prompt. Saved oracle answers,
class labels, split metadata, and other tasks must stay outside the model's
context and accessible tools. A local held-out split says nothing about the
model's unknown pretraining exposure.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from functools import lru_cache
import hashlib
from itertools import combinations, permutations, product
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DATASET_PATH = ROOT / "benchmarks/repair-v1/tasks.json"
SCHEMA_VERSION = 1
SAMPLING_SEED = "finite-congruence-checks/repair-v1/2026-10-18"
PAIRS = tuple(combinations(range(4), 2))
PERMUTATIONS = tuple(permutations(range(4)))


def _canonical_labels(labels) -> tuple[int, ...]:
    names = {}
    return tuple(names.setdefault(value, len(names)) for value in labels)


@lru_cache(maxsize=1)
def _partition_tuples() -> tuple[tuple[int, ...], ...]:
    def extend(prefix):
        if len(prefix) == 4:
            yield tuple(prefix)
        else:
            for label in range(max(prefix) + 2):
                yield from extend(prefix + [label])
    return tuple(extend([0]))


def partitions() -> list[list[int]]:
    """Return all 15 partitions as fresh canonical label arrays."""
    return [list(labels) for labels in _partition_tuples()]


def _digits(value, name: str) -> list[int]:
    if type(value) is not list or len(value) != 4 or any(
            type(digit) is not int or not 0 <= digit < 4 for digit in value):
        raise ValueError(f"{name} must be a list of four integers in 0..3")
    return value


def encode(operation: list[int], group_labels: list[int]) -> int:
    """Pack the fixed operation and labels using the established base-4 layout."""
    digits = _digits(operation, "operation") + _digits(group_labels, "group_labels")
    return sum(value * 4 ** place for place, value in enumerate(digits))


def _preserves(operation, labels) -> bool:
    return all(labels[x] != labels[y] or labels[operation[x]] == labels[operation[y]]
               for x, y in PAIRS)


def _coarsens(original, proposed) -> bool:
    return all(original[x] != original[y] or proposed[x] == proposed[y] for x, y in PAIRS)


def _validate_task(task: dict) -> tuple[list[int], list[int], list[int]]:
    if type(task) is not dict:
        raise ValueError("task must be an object")
    operation = _digits(task.get("operation"), "operation")
    initial = _digits(task.get("initial_labels"), "initial_labels")
    separate = task.get("separate")
    if (type(separate) is not list or len(separate) != 2
            or any(type(value) is not int or not 0 <= value < 4 for value in separate)
            or separate[0] == separate[1]):
        raise ValueError("separate must contain two distinct integers in 0..3")
    if initial[separate[0]] == initial[separate[1]]:
        raise ValueError("the required pair must be separated in the initial grouping")
    if _preserves(operation, initial):
        raise ValueError("the initial grouping must be rejected by the preservation property")
    return operation, initial, separate


def solve(task: dict) -> list[list[int]]:
    """Enumerate every valid repaired partition, independently of merge closure.

    Canonicalizing names never identifies different partitions. The empty
    result means UNSAT within this exact finite, merges-only task.
    """
    operation, initial, (a, b) = _validate_task(task)
    return [list(candidate) for candidate in _partition_tuples()
            if _coarsens(initial, candidate) and candidate[a] != candidate[b]
            and _preserves(operation, candidate)]


def grade(task: dict, answer: object) -> dict:
    """Score exactly {status, group_labels}; operation changes are not answers.

    Invalid tasks raise ValueError instead of being counted as model failures.
    Label names may differ from the canonical oracle's names. A declaration of
    impossibility is evaluated by exhaustive partition enumeration and should
    be a terminal model answer, not a source of oracle feedback during a trial.
    """
    operation, initial, (a, b) = _validate_task(task)

    def result(correct, reason):
        return {"correct": correct, "reason": reason}

    if type(answer) is not dict or set(answer) != {"status", "group_labels"}:
        return result(False, "invalid_answer: expected exactly status and group_labels")
    status = answer["status"]
    if type(status) is not str or status not in ("repair", "impossible"):
        return result(False, "invalid_answer: status must be repair or impossible")
    if status == "impossible":
        if answer["group_labels"] is not None:
            return result(False, "invalid_answer: impossible requires group_labels null")
        if solve(task):
            return result(False, "false_impossible: at least one valid repair exists")
        return result(True, "certified_impossible: all 15 partitions were checked")
    try:
        candidate = _digits(answer["group_labels"], "group_labels")
    except ValueError as error:
        return result(False, "invalid_answer: " + str(error))
    if not _coarsens(initial, candidate):
        return result(False, "splits_original_block: an original equivalence was removed")
    if candidate[a] == candidate[b]:
        return result(False, "separation_violated: the designated pair was merged")
    if not _preserves(operation, candidate):
        return result(False, "not_preserved: an equal-label pair has differently labeled images")
    return result(True, "valid_repair: preservation, merges-only, and separation all hold")


def public_task(task: dict) -> dict:
    """Return an allowlisted copy without answer class, oracle, or split data."""
    operation, initial, separate = _validate_task(task)
    identifier = task.get("id")
    if type(identifier) is not str or not identifier:
        raise ValueError("public tasks require a nonempty string id")
    return {"id": identifier, "operation": list(operation),
            "initial_labels": list(initial), "separate": list(separate)}


def _relabeled(operation, labels, pair, permutation):
    moved_operation = [0] * 4
    moved_labels = [0] * 4
    for old in range(4):
        moved_operation[permutation[old]] = permutation[operation[old]]
        moved_labels[permutation[old]] = labels[old]
    return (tuple(moved_operation), _canonical_labels(moved_labels),
            tuple(sorted(permutation[x] for x in pair)))


def _task_key(operation, labels, pair):
    return min(_relabeled(operation, labels, pair, permutation) for permutation in PERMUTATIONS)


def _json_bytes(value) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def _rank(purpose: str, value) -> str:
    return hashlib.sha256(SAMPLING_SEED.encode("utf-8") + b"\0"
                          + purpose.encode("ascii") + b"\0" + _json_bytes(value)).hexdigest()


def _identifier(prefix: str, value) -> str:
    return prefix + hashlib.sha256(_json_bytes(value)).hexdigest()


def build_dataset() -> dict:
    """Enumerate the full task universe, then deterministically select a pilot.

    Two development operation families and six different test families each
    contribute one SAT and one UNSAT three-block task. Families are conjugacy
    classes of operations under all 24 object permutations. Entire task
    isomorphism classes are deduplicated before selection. Unused families are
    not silently treated as evaluated data.
    """
    labeled_counts = Counter()
    block_counts = defaultdict(Counter)
    rejected_base_counts = Counter()
    orbit_answers = {}
    function_keys = set()
    eligible_function_keys = set()
    for operation in product(range(4), repeat=4):
        function_key = min(_relabeled(operation, (0, 0, 0, 0), (0, 1), permutation)[0]
                           for permutation in PERMUTATIONS)
        function_keys.add(function_key)
        for initial in _partition_tuples():
            if _preserves(operation, initial):
                continue
            blocks = len(set(initial))
            rejected_base_counts[blocks] += 1
            eligible_function_keys.add(function_key)
            valid_coarsenings = [candidate for candidate in _partition_tuples()
                                if _coarsens(initial, candidate) and _preserves(operation, candidate)]
            for a, b in PAIRS:
                if initial[a] == initial[b]:
                    continue
                solutions = [candidate for candidate in valid_coarsenings if candidate[a] != candidate[b]]
                answer_class = "sat" if solutions else "unsat"
                labeled_counts[answer_class] += 1
                block_counts[blocks][answer_class] += 1
                if len(solutions) > 1:
                    raise AssertionError("Unexpected multiple repairs: reassess the four-object scope")
                key = _task_key(operation, initial, (a, b))
                if key in orbit_answers and orbit_answers[key] != answer_class:
                    raise AssertionError("Isomorphic tasks disagree about satisfiability")
                orbit_answers[key] = answer_class

    # Pair SAT/UNSAT cases within each selected operation family, while keeping
    # entire operation families out of the other split.
    candidates = defaultdict(lambda: defaultdict(list))
    for key, answer_class in orbit_answers.items():
        operation, initial, _ = key
        if len(set(initial)) == 3:
            candidates[operation][answer_class].append(key)
    families = [family for family, classes in candidates.items()
                if classes["sat"] and classes["unsat"]]
    families.sort(key=lambda value: (_rank("operation-family", value), value))
    if len(families) < 8:
        raise AssertionError("Need eight disjoint operation families with both classes")
    selected_families = {"dev": families[:2], "test": families[2:8]}
    tasks = []
    for split, split_families in selected_families.items():
        for family in split_families:
            for answer_class in ("sat", "unsat"):
                key = min(candidates[family][answer_class],
                          key=lambda value: (_rank("task", value), value))
                operation, initial, separate = key
                task = {
                    "id": _identifier("repair-v1:", key), "split": split,
                    "operation": list(operation), "initial_labels": list(initial),
                    "separate": list(separate),
                    "operation_family_id": _identifier("operation-conjugacy-v1:", family),
                }
                solutions = solve(task)
                task["oracle"] = {"answer_class": answer_class, "solutions": solutions,
                                  "solution_count": len(solutions),
                                  "method": "Exhaustively enumerate the 15 canonical partitions."}
                if bool(solutions) != (answer_class == "sat"):
                    raise AssertionError("Selected task disagrees with the direct oracle")
                tasks.append(task)
    tasks.sort(key=lambda task: (task["split"], _rank("presentation-order", task["id"]), task["id"]))
    orbit_counts = Counter(orbit_answers.values())
    return {
        "schema_version": SCHEMA_VERSION, "dataset_id": "repair-v1",
        "sampling_seed": SAMPLING_SEED,
        "sampling_method": "SHA-256(seed + NUL + purpose + NUL + canonical compact sorted-key ASCII JSON); lexical digest order, then value order for ties",
        "status": "dataset_and_oracle_only; no model runs are implied",
        "scope": "One fixed unary operation on four objects; initially rejected grouping; merge entire existing blocks only; keep one initially separated pair separated.",
        "public_answer_schema": {"required_exact_keys": ["status", "group_labels"],
                                 "status": ["repair", "impossible"],
                                 "group_labels": "Four integers in 0..3 for repair; null for impossible. Label names need not be canonical."},
        "oracle": {"method": "Exhaustive enumeration of all 15 partitions; no import of the previous closure-based repair algorithm.",
                   "evidence_status": "Computational oracle cross-checked by independent forced-merge closure tests; not a formal proof of this constrained task."},
        "universe": {
            "objects": 4, "operations": 256, "partitions": 15,
            "operation_conjugacy_classes": len(function_keys),
            "eligible_operation_conjugacy_classes": len(eligible_function_keys),
            "rejected_operation_partition_pairs": sum(rejected_base_counts.values()),
            "eligible_labeled_tasks": sum(labeled_counts.values()),
            "labeled_class_counts": dict(sorted(labeled_counts.items())),
            "task_isomorphism_classes": len(orbit_answers),
            "orbit_class_counts": dict(sorted(orbit_counts.items())),
            "by_initial_block_count": {
                str(blocks): {"rejected_operation_partition_pairs": rejected_base_counts[blocks],
                              "task_class_counts": dict(sorted(classes.items()))}
                for blocks, classes in sorted(block_counts.items())
            },
            "label_convention": "Grouping label aliases are canonicalized; objects remain labeled for labeled-task counts. Required pairs are unordered. Orbit counts additionally quotient simultaneous object permutations of operation, grouping, and pair.",
        },
        "split_policy": {
            "grouping": "Operation conjugacy under all 24 object permutations; no operation family occurs in both dev and test.",
            "development_use": "Only dev cases may guide prompt or runner changes before a versioned held-out run.",
            "heldout_meaning": "Local development holdout only. Model pretraining exposure and training-data contamination are unknown.",
            "selected_initial_block_count": 3,
            "two_block_cases": "Excluded from both sampled splits because every rejected two-block case is UNSAT under the separation constraint; checked as a sanity stratum in exhaustive oracle tests.",
            "dev": {"tasks": 4, "sat": 2, "unsat": 2, "operation_families": 2},
            "test": {"tasks": 12, "sat": 6, "unsat": 6, "operation_families": 6},
            "unused_eligible_operation_families": len(eligible_function_keys) - 8,
        },
        "mathematical_limits": [
            "Every SAT task in this four-object universe has exactly one valid repaired partition, up to group-label renaming.",
            "A rejected two-block grouping can only be repaired by the universal grouping, which violates the required separation.",
            "A rejected three-block grouping admits exactly two proper block merges compatible with the separated pair; two candidate probes can exhaust this repair space.",
            "The fixed separated pair prevents universal-grouping fallback from receiving credit.",
            "Twelve test cases from six operation families are a controlled pilot, not a broad benchmark of mathematical reasoning or new mathematical discovery.",
        ],
        "evaluation_recommendations": [
            "Use fresh model sessions and the identical task, output format, model, settings, and decision budget in each arm; record token usage separately.",
            "Primary outcome: correctness of the first decision after assigned initial feedback. Report SAT and UNSAT accuracy separately and paired per-task outcomes.",
            "Secondary outcomes: success within a fixed decision budget, native-checker queries, tokens, malformed outputs, illegal splits, and violated separation.",
            "Treat impossible as a terminal answer; never provide the private enumeration oracle's satisfiability verdict as trial feedback.",
            "A counterexample must come from the actual native checker and satisfy the candidate's decoded input. Pass/fail and counterexample arms share all non-witness feedback.",
            "Operation families, not raw cases or label aliases, are the independent grouping unit. Avoid significance or broad generalization claims from six test families.",
        ],
        "tasks": tasks,
    }


def dataset_bytes(data: dict) -> bytes:
    return (json.dumps(data, indent=2, ensure_ascii=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=DATASET_PATH)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    data = build_dataset()
    expected = dataset_bytes(data)
    if args.check:
        if not args.out.is_file() or args.out.read_bytes() != expected:
            print("Repair dataset is absent or stale.")
            return 1
    else:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_bytes(expected)
    print(json.dumps({"status": "ok", "dataset": str(args.out),
                      "tasks": len(data["tasks"]), "split_policy": data["split_policy"]}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
