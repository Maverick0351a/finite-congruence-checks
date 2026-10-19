#!/usr/bin/env python3
"""Minimize unary operations for each fixed, verified threshold representation.

This is exact set cover over unwanted equivalence relations. It does not minimize
over other embeddings, carrier sizes, or operation arities. Standard library only.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path


def _require(condition):
    """Keep evidence controls active even with python -O."""
    if not condition:
        raise AssertionError("self-check or enumeration invariant failed")


def all_partitions(n: int) -> list[tuple[int, ...]]:
    """Insert each new vertex into an old block or a new last block."""
    if not 1 <= n <= 6:
        raise ValueError("supported carrier sizes are 1 through 6")
    arrangements = [((0,),)]
    for vertex in range(1, n):
        expanded = []
        for blocks in arrangements:
            expanded.append(blocks + ((vertex,),))
            for index in range(len(blocks)):
                expanded.append(blocks[:index] + (blocks[index] + (vertex,),) + blocks[index + 1:])
        arrangements = expanded
    result = []
    for blocks in arrangements:
        labels = [0] * n
        for label, block in enumerate(blocks):
            for vertex in block:
                labels[vertex] = label
        result.append(tuple(labels))
    return sorted(result)


def preserves(operation: tuple[int, ...], partition: tuple[int, ...]) -> bool:
    image_blocks = {}
    for vertex, block in enumerate(partition):
        target_block = partition[operation[vertex]]
        if block in image_blocks and image_blocks[block] != target_block:
            return False
        image_blocks[block] = target_block
    return True


def read_targets(data: dict) -> tuple[int, list[tuple[int, ...]]]:
    """Validate the finite lattice and decode its concrete threshold relations."""
    lattice, color = data["lattice"], data["color"]
    if not isinstance(lattice, dict) or not isinstance(lattice.get("name"), str) or not lattice["name"]:
        raise ValueError("lattice.name must be a nonempty string")
    m, n = len(lattice["elements"]), len(color)
    leq, join, bottom = lattice["leq"], lattice["join"], lattice["bottom"]
    if (not isinstance(lattice["elements"], list)
            or any(not isinstance(name, str) for name in lattice["elements"])
            or len(set(lattice["elements"])) != m):
        raise ValueError("lattice elements must be distinct strings")
    if not 1 <= n <= 4:
        raise ValueError("operation minimization supports carrier sizes 1 through 4")
    if m < 1 or type(bottom) is not int or not 0 <= bottom < m:
        raise ValueError("invalid lattice or carrier size")
    if (len(leq) != m or len(join) != m
            or any(len(row) != m for row in leq + join)
            or any(type(value) is not bool for row in leq for value in row)
            or any(type(value) is not int or not 0 <= value < m for row in join for value in row)
            or any(len(row) != n for row in color)
            or any(type(value) is not int or not 0 <= value < m for row in color for value in row)):
        raise ValueError("malformed finite lattice or color tables")
    for a in range(m):
        if not leq[a][a] or not leq[bottom][a]:
            raise ValueError("reflexivity or bottom condition fails")
        for b in range(m):
            if a != b and leq[a][b] and leq[b][a]:
                raise ValueError("antisymmetry fails")
            if any(leq[a][b] and leq[b][c] and not leq[a][c] for c in range(m)):
                raise ValueError("transitivity fails")
            upper = [c for c in range(m) if leq[a][c] and leq[b][c]]
            lower = [c for c in range(m) if leq[c][a] and leq[c][b]]
            least_upper = [c for c in upper if all(leq[c][d] for d in upper)]
            greatest_lower = [c for c in lower if all(leq[d][c] for d in lower)]
            if least_upper != [join[a][b]] or len(greatest_lower) != 1:
                raise ValueError("join or meet condition fails")
    targets = []
    for a in range(m):
        relation = [[leq[color[x][y]][a] for y in range(n)] for x in range(n)]
        if (any(not relation[x][x] for x in range(n))
                or any(relation[x][y] != relation[y][x] for x in range(n) for y in range(n))
                or any(relation[x][y] and relation[y][z] and not relation[x][z]
                       for x in range(n) for y in range(n) for z in range(n))):
            raise ValueError("threshold is not an equivalence relation")
        representatives = [next(y for y in range(n) if relation[x][y]) for x in range(n)]
        ordered = sorted(set(representatives))
        targets.append(tuple(ordered.index(x) for x in representatives))
    if len(set(targets)) != m:
        raise ValueError("threshold relations do not separate lattice elements")
    for a in range(m):
        for b in range(m):
            inclusion = all(targets[a][x] != targets[a][y] or targets[b][x] == targets[b][y]
                            for x in range(n) for y in range(n))
            if inclusion != leq[a][b]:
                raise ValueError("threshold order disagrees with lattice order")
    return n, targets


def independently_recover_destructions(n: int, targets: list[tuple[int, ...]],
                                     unwanted: list[tuple[int, ...]]) -> tuple[list[tuple[int, ...]], list[set[int]]]:
    """Re-enumerate maps and use pair tests, not the block-image predicate."""
    pool = []
    destructions = set()
    for operation in itertools.product(range(n), repeat=n):
        if any(p[x] == p[y] and p[operation[x]] != p[operation[y]]
               for p in targets for x in range(n) for y in range(x)):
            continue
        pool.append(operation)
        broken = frozenset(i for i, p in enumerate(unwanted)
                           if any(p[x] == p[y] and p[operation[x]] != p[operation[y]]
                                  for x in range(n) for y in range(x)))
        if broken:
            destructions.add(broken)
    return pool, [set(value) for value in sorted(destructions, key=lambda value: tuple(sorted(value)))]


def exact_cover_dp(masks: list[int], universe_size: int) -> dict:
    """0/1 dynamic programming, with one lexicographic representative per mask."""
    full = (1 << universe_size) - 1
    best: dict[int, tuple[int, ...]] = {0: ()}
    for index, mask in enumerate(masks):
        for covered, chosen in list(best.items()):
            combined = covered | mask
            proposal = chosen + (index,)
            previous = best.get(combined)
            if previous is None or (len(proposal), proposal) < (len(previous), previous):
                best[combined] = proposal
    chosen = best.get(full)
    return {"optimum": None if chosen is None else len(chosen),
            "selected_indices": None if chosen is None else list(chosen),
            "coverage_states": len(best)}


def exact_cover_subsets(destructions: list[set[int]], universe_size: int) -> dict:
    """Independent cardinality-first enumeration, using sets instead of bit DP."""
    target = set(range(universe_size))
    covered_by_all = set().union(*destructions) if destructions else set()
    if covered_by_all != target:
        return {"optimum": None, "selected_indices": None, "subsets_examined_by_cardinality": {},
                "uncovered_elements": sorted(target - covered_by_all)}
    examined = {}
    for count in range(len(destructions) + 1):
        examined[str(count)] = 0
        for chosen in itertools.combinations(range(len(destructions)), count):
            examined[str(count)] += 1
            union = set()
            for index in chosen:
                union.update(destructions[index])
            if union == target:
                return {"optimum": count, "selected_indices": list(chosen),
                        "subsets_examined_by_cardinality": examined,
                        "all_smaller_cardinalities_exhausted": True}
    raise AssertionError("full union was attainable but no cover was found")


def choose_operations(n: int, targets: list[tuple[int, ...]]) -> dict:
    if not 1 <= n <= 4:
        raise ValueError("operation minimization supports carrier sizes 1 through 4")
    partitions = all_partitions(n)
    if len(targets) != len(set(targets)) or any(p not in partitions for p in targets):
        raise ValueError("target relations must be distinct canonical set partitions")
    pool = [f for f in itertools.product(range(n), repeat=n)
            if all(preserves(f, p) for p in targets)]
    unwanted = [p for p in partitions if p not in targets]
    representative = {}
    for operation in pool:
        mask = sum(1 << index for index, p in enumerate(unwanted) if not preserves(operation, p))
        # Two operations with the same mask are interchangeable for this objective.
        if mask and mask not in representative:
            representative[mask] = operation
    masks = sorted(representative)
    destructions = [{i for i in range(len(unwanted)) if mask & (1 << i)} for mask in masks]
    dp = exact_cover_dp(masks, len(unwanted))
    independent_pool, independent_destructions = independently_recover_destructions(n, targets, unwanted)
    pool_agrees = pool == independent_pool
    destruction_sets_agree = {frozenset(d) for d in destructions} == {frozenset(d) for d in independent_destructions}
    enumeration = exact_cover_subsets(independent_destructions, len(unwanted))
    enumeration["destruction_sets"] = [sorted(d) for d in independent_destructions]
    if dp["optimum"] != enumeration["optimum"]:
        raise AssertionError("independent optimization methods disagree")
    selected = [] if dp["selected_indices"] is None else [representative[masks[i]] for i in dp["selected_indices"]]
    recovered = [p for p in partitions if all(preserves(f, p) for f in selected)]
    checks = {
        "independent_operation_pool_agrees": pool_agrees,
        "independent_destruction_sets_agree": destruction_sets_agree,
        "optimization_methods_agree": dp["optimum"] == enumeration["optimum"],
        "all_smaller_cardinalities_exhausted": enumeration.get("all_smaller_cardinalities_exhausted", False),
        "selected_operations_preserve_targets": all(preserves(f, p) for f in selected for p in targets),
        "exact_target_congruences_recovered": dp["optimum"] is not None and set(recovered) == set(targets),
    }
    result = {
        "carrier_size": n,
        "all_functions_enumerated": n ** n,
        "all_partitions_enumerated": len(partitions),
        "admissible_operation_count": len(pool),
        "admissible_operation_tables": pool,
        "target_partitions": targets,
        "unwanted_partitions": unwanted,
        "unique_nonempty_destruction_masks": len(masks),
        "mask_representatives": [{"mask": mask, "operation": representative[mask],
                                  "breaks_unwanted_partition_indices": sorted(destructions[i])}
                                 for i, mask in enumerate(masks)],
        "minimum_unary_operation_count": dp["optimum"],
        "selected_unary_operations": selected,
        "recovered_congruence_partitions": recovered,
        "dynamic_programming": dp,
        "independent_subset_enumeration": enumeration,
        "checks": checks,
        "passed": all(checks.values()),
    }
    return result


def self_check() -> dict:
    _require([len(all_partitions(n)) for n in range(1, 7)] == [1, 2, 5, 15, 52, 203])
    # Two distinct required destructions need two operations.
    _require(exact_cover_dp([1, 2], 2)["optimum"] == 2)
    _require(exact_cover_subsets([{0}, {1}], 2)["optimum"] == 2)
    _require(exact_cover_dp([1, 2, 3], 2)["optimum"] == 1)
    _require(exact_cover_subsets([{0}, {1}, {0, 1}], 2)["optimum"] == 1)
    _require(exact_cover_dp([], 0)["optimum"] == 0)
    _require(exact_cover_subsets([], 0)["optimum"] == 0)
    _require(exact_cover_dp([1], 2)["optimum"] is None)
    _require(exact_cover_subsets([{0}], 2)["optimum"] is None)
    c3 = choose_operations(3, [(0, 1, 2), (0, 0, 1), (0, 0, 0)])
    _require(c3["passed"] and c3["minimum_unary_operation_count"] == 1)
    # Removing its unique selected operation gives every partition, including two extras.
    no_operations = []
    without_operation = [p for p in all_partitions(3) if all(preserves(f, p) for f in no_operations)]
    _require(len(set(without_operation) - set(c3["target_partitions"])) == 2)
    _require(choose_operations(3, all_partitions(3))["minimum_unary_operation_count"] == 0)
    try:
        choose_operations(2, [(0, 1), (0, 1)])
    except ValueError:
        pass
    else:
        raise AssertionError("duplicate target partitions accepted")
    # A requested family missing equality cannot be a full congruence lattice.
    _require(not choose_operations(2, [(0, 0)])["passed"])
    example = {"lattice": {"name": "C3-control", "elements": ["0", "a", "1"], "bottom": 0,
                            "leq": [[True, True, True], [False, True, True], [False, False, True]],
                            "join": [[0, 1, 2], [1, 1, 2], [2, 2, 2]]},
               "color": [[0, 1, 2], [1, 0, 2], [2, 2, 0]]}
    _require(read_targets(example) == (3, [(0, 1, 2), (0, 0, 1), (0, 0, 0)]))
    for invalid_names in (["0", "0", "1"], [0, "a", "1"]):
        damaged = {"lattice": {**example["lattice"], "elements": invalid_names}, "color": example["color"]}
        try:
            read_targets(damaged)
        except ValueError:
            pass
        else:
            raise AssertionError("invalid lattice element names accepted")
    for check in (lambda: choose_operations(5, []),
                  lambda: read_targets({**example, "color": [[0] * 5 for _ in range(5)]})):
        try:
            check()
        except ValueError:
            pass
        else:
            raise AssertionError("unbounded minimizer input accepted")
    return {"passed": True,
            "positive_controls": ["Bell counts", "cover optima 0, 1 and 2", "C3 one operation", "Eq(3) zero operations"],
            "negative_controls": ["uncoverable partition", "duplicate target relation", "target missing equality", "C3 operation removal adds two congruences", "invalid lattice element names", "carrier beyond four vertices"]}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificates", nargs="+", type=Path)
    parser.add_argument("--out", type=Path, default=Path("minimal-operations.json"))
    args = parser.parse_args()
    paths = args.certificates
    if not paths:
        parser.error("no certificates supplied or found")
    if args.out.resolve() in {path.resolve() for path in paths}:
        parser.error("output path must not overwrite an input certificate")
    rows = []
    for path in paths:
        result = {"certificate": path.name}
        try:
            raw = path.read_bytes()
            result["certificate_sha256"] = hashlib.sha256(raw).hexdigest()
            data = json.loads(raw)
            n, targets = read_targets(data)
            result.update(choose_operations(n, targets))
            result["lattice"] = data["lattice"]["name"]
            result["checks"]["valid_lattice_and_threshold_order_embedding"] = True
            result["threshold_partitions"] = [{"element": element, "partition": partition}
                                               for element, partition in zip(data["lattice"]["elements"], targets)]
        except (OSError, ValueError, KeyError, TypeError, IndexError) as error:
            result.update({"passed": False, "checks": {"valid_input": False}, "error": str(error)})
        rows.append(result)
    result = {"schema_version": 1,
              "scope": "minimum basic unary operation count on each fixed carrier with its exact saved threshold relations; other embeddings and higher-arity signatures excluded",
              "method": "0/1 set-cover dynamic programming, checked by increasing-cardinality enumeration of distinct destruction sets",
              "completeness_argument": "Every operation in a unary representation of these exact relations must preserve each target relation. All such total unary maps are enumerated. Each unwanted partition must be broken by at least one chosen map. Equal destruction masks are interchangeable; zero masks cannot help. Therefore minimum set cover equals minimum operation count for this fixed representation.",
              "limits": "exhaustive Python computation; no machine-checked proof of the implementation or novelty claim",
              "minimizer_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "self_check": self_check(), "certificates": rows, "passed": all(row["passed"] for row in rows)}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps({"passed": result["passed"], "minima": {r["lattice"]: r["minimum_unary_operation_count"] for r in rows if "lattice" in r},
                      "output": str(args.out)}))
    return 0 if result["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
