#!/usr/bin/env python3
"""Independently recover a complete finite unary algebra from a graph certificate.

Standard library only. No imports from the witness search or its seed verifier.
Enumerates all n**n operations and every set partition of the carrier.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import itertools
import json
from pathlib import Path


def _require(condition):
    """Keep evidence controls active even with python -O."""
    if not condition:
        raise AssertionError("self-check or enumeration invariant failed")


def check_lattice(lattice: dict) -> tuple[list[str], list[list[bool]]]:
    if not isinstance(lattice, dict):
        raise ValueError("lattice must be an object")
    if not isinstance(lattice.get("name"), str) or not lattice["name"]:
        raise ValueError("lattice.name must be a nonempty string")
    names, leq, join = lattice["elements"], lattice["leq"], lattice["join"]
    if not isinstance(names, list) or not names or not all(isinstance(x, str) for x in names) or len(set(names)) != len(names):
        raise ValueError("lattice element names must be nonempty, distinct strings")
    m = len(names)
    if len(leq) != m or any(len(row) != m or any(type(x) is not bool for x in row) for row in leq):
        raise ValueError("order must be a square boolean table")
    if len(join) != m or any(len(row) != m or any(type(x) is not int or not 0 <= x < m for x in row) for row in join):
        raise ValueError("join must be a square table of lattice element indices")
    bottom = lattice["bottom"]
    if type(bottom) is not int or not 0 <= bottom < m or not all(leq[bottom]):
        raise ValueError("invalid bottom element")
    for a, b, c in itertools.product(range(m), repeat=3):
        if not leq[a][a] or (a != b and leq[a][b] and leq[b][a]):
            raise ValueError("order is not reflexive and antisymmetric")
        if leq[a][b] and leq[b][c] and not leq[a][c]:
            raise ValueError("order is not transitive")
    for a, b in itertools.product(range(m), repeat=2):
        uppers = [u for u in range(m) if leq[a][u] and leq[b][u]]
        least = [u for u in uppers if all(leq[u][v] for v in uppers)]
        lowers = [u for u in range(m) if leq[u][a] and leq[u][b]]
        greatest = [u for u in lowers if all(leq[v][u] for v in lowers)]
        if least != [join[a][b]] or len(greatest) != 1:
            raise ValueError("tables do not define the declared lattice")
    return names, leq


def partitions(n: int):
    """Canonical restricted-growth strings; one tuple per set partition."""
    if n < 1:
        raise ValueError("carrier must be nonempty")

    def extend(prefix: tuple[int, ...]):
        if len(prefix) == n:
            yield prefix
            return
        for block in range(max(prefix) + 2):
            yield from extend(prefix + (block,))

    yield from extend((0,))


def preserves(operation: tuple[int, ...], partition: tuple[int, ...]) -> bool:
    return all(
        partition[x] != partition[y] or partition[operation[x]] == partition[operation[y]]
        for x in range(len(partition)) for y in range(x)
    )


def refines(first: tuple[int, ...], second: tuple[int, ...]) -> bool:
    return all(first[x] != first[y] or second[x] == second[y]
               for x in range(len(first)) for y in range(x))


def relation_partition(relation: list[list[bool]]) -> tuple[int, ...]:
    n = len(relation)
    for x in range(n):
        if not relation[x][x]:
            raise ValueError("threshold relation is not reflexive")
        for y in range(n):
            if relation[x][y] != relation[y][x]:
                raise ValueError("threshold relation is not symmetric")
            for z in range(n):
                if relation[x][y] and relation[y][z] and not relation[x][z]:
                    raise ValueError("threshold relation is not transitive")
    representatives: dict[int, int] = {}
    result = []
    for x in range(n):
        representative = next(y for y in range(n) if relation[x][y])
        if representative not in representatives:
            representatives[representative] = len(representatives)
        result.append(representatives[representative])
    return tuple(result)


def verify(data: dict) -> dict:
    names, leq = check_lattice(data["lattice"])
    color = data["color"]
    n, m = len(color), len(names)
    if not 1 <= n <= 6:
        raise ValueError("this exhaustive verifier supports carrier sizes 1 through 6")
    if any(len(row) != n or any(type(x) is not int or not 0 <= x < m for x in row) for row in color):
        raise ValueError("color must be a square table of lattice element indices")
    thresholds = [relation_partition([[leq[color[x][y]][a] for y in range(n)] for x in range(n)])
                  for a in range(m)]
    operations = []
    preservation_operations = []
    for operation in itertools.product(range(n), repeat=n):
        if all(leq[color[operation[x]][operation[y]]][color[x][y]]
               for x in range(n) for y in range(n)):
            operations.append(operation)
        if all(preserves(operation, partition) for partition in thresholds):
            preservation_operations.append(operation)
    candidates = list(partitions(n))
    congruences = [p for p in candidates if all(preserves(f, p) for f in operations)]
    checks = {
        "admissible_equals_threshold_preserving": operations == preservation_operations,
        "distinct_threshold_relations": len(set(thresholds)) == m,
        "congruences_exactly_threshold_relations": set(congruences) == set(thresholds),
        "order_isomorphism": all(leq[a][b] == refines(thresholds[a], thresholds[b])
                                 for a in range(m) for b in range(m)),
    }
    return {
        "lattice": data["lattice"]["name"],
        "carrier_size": n,
        "functions_enumerated": n ** n,
        "partitions_enumerated": len(candidates),
        "unary_operation_count": len(operations),
        "unary_operation_tables": operations,
        "congruence_count": len(congruences),
        "congruence_partitions": congruences,
        "threshold_partitions": [{"element": name, "partition": p} for name, p in zip(names, thresholds)],
        "checks": checks,
        "passed": all(checks.values()),
    }


def self_check() -> dict:
    bell_counts = [sum(1 for _ in partitions(n)) for n in range(1, 7)]
    _require(bell_counts == [1, 2, 5, 15, 52, 203])
    _require(all(len(set(partitions(n))) == bell_counts[n - 1] for n in range(1, 7)))
    _require(preserves((1, 0, 2), (0, 0, 1)))
    _require(not preserves((0, 2, 1), (0, 0, 1)))
    _require(refines((0, 1, 2), (0, 0, 1)))
    _require(not refines((0, 0, 1), (0, 1, 2)))
    _require(relation_partition([[True, True, False], [True, True, False], [False, False, True]]) == (0, 0, 1))
    invalid = [[True, True, False], [True, True, True], [False, True, True]]
    try:
        relation_partition(invalid)
    except ValueError:
        pass
    else:
        raise AssertionError("nontransitive relation was accepted")
    example = {"lattice": {"name": "C3-control", "elements": ["0", "a", "1"], "bottom": 0,
                            "leq": [[True, True, True], [False, True, True], [False, False, True]],
                            "join": [[0, 1, 2], [1, 1, 2], [2, 2, 2]]},
               "color": [[0, 1, 2], [1, 0, 2], [2, 2, 0]]}
    result = verify(example)
    _require(result["passed"] and result["unary_operation_count"] == 15 and result["congruence_count"] == 3)
    damaged = copy.deepcopy(example)
    damaged["color"] = [[0, 1, 1], [1, 0, 1], [1, 1, 0]]
    damaged_result = verify(damaged)
    _require(not damaged_result["passed"] and not damaged_result["checks"]["distinct_threshold_relations"])
    bad_lattice = copy.deepcopy(example)
    bad_lattice["lattice"]["join"][1][2] = 1
    try:
        verify(bad_lattice)
    except ValueError:
        pass
    else:
        raise AssertionError("invalid join table was accepted")
    return {"passed": True, "bell_numbers_1_through_6": bell_counts,
            "checks": "partition enumeration, preservation/refinement controls, nontransitivity rejection, C3 positive control",
            "negative_controls_rejected": ["missing separating color", "invalid join table"]}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificates", nargs="+", type=Path)
    parser.add_argument("--out", type=Path, default=Path("algebra-check.json"))
    args = parser.parse_args()
    files = args.certificates
    if not files:
        parser.error("no certificate files found")
    if args.out.resolve() in {path.resolve() for path in files}:
        parser.error("output path must not overwrite an input certificate")
    rows = []
    for path in files:
        content = None
        try:
            content = path.read_bytes()
            row = verify(json.loads(content))
        except (OSError, ValueError, TypeError, KeyError, IndexError) as exc:
            row = {"passed": False, "error": str(exc)}
        row["certificate"] = path.name
        row["sha256"] = hashlib.sha256(content).hexdigest() if content is not None else None
        rows.append(row)
    result = {"schema_version": 1, "method": "enumerate all total unary maps and all set partitions",
              "partition_encoding": "equal integers mean membership in the same equivalence class",
              "operation_encoding": "entry at index x is the image of carrier vertex x",
              "limits": "Python exhaustive computation, no Lean compilation or proof of implementation",
              "self_check": self_check(), "certificates": rows, "passed": all(row["passed"] for row in rows)}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps({"passed": result["passed"], "certificates": len(rows), "output": str(args.out)}))
    return 0 if result["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
