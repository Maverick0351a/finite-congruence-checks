"""Independently audit all representable exact relation families on 1..4 points.

Binary relation tables and breadth-first intersections replace the production
partition generator, preservation predicate, and set-cover optimizers. This is
a finite implementation cross-check, not a novelty claim or formal proof.
"""
from __future__ import annotations

import argparse
from collections import Counter, deque
import hashlib
import importlib.util
from itertools import combinations, product
import json
from pathlib import Path
import time

ROOT = Path(__file__).resolve().parents[1]


def relations(n: int) -> list[frozenset[tuple[int, int]]]:
    """Enumerate symmetric binary tables, then retain transitive ones."""
    offdiag = list(combinations(range(n), 2))
    answer = []
    for bits in product((False, True), repeat=len(offdiag)):
        relation = {(x, x) for x in range(n)}
        for (x, y), present in zip(offdiag, bits):
            if present:
                relation.update(((x, y), (y, x)))
        if all((x, z) in relation for x, y in relation for a, z in relation if y == a):
            answer.append(frozenset(relation))
    return answer


def canonical(relation: frozenset[tuple[int, int]], n: int) -> tuple[int, ...]:
    representatives = [min(y for a, y in relation if a == x) for x in range(n)]
    labels = sorted(set(representatives))
    return tuple(labels.index(x) for x in representatives)


def explore(n: int) -> tuple[list[frozenset[tuple[int, int]]], dict[frozenset[int], int]]:
    """Shortest paths count operations added to an initially empty signature.

    Adding one operation intersects the current congruence family with that
    operation's invariant equivalence relations. Every total map is included,
    so every finite unary signature is reachable. Breadth-first distances are
    the minimum operation counts, including the distance-zero empty signature.
    """
    eqs = relations(n)
    operation_congruences = []
    for operation in product(range(n), repeat=n):
        operation_congruences.append(frozenset(i for i, rel in enumerate(eqs)
            if all((operation[x], operation[y]) in rel for x, y in rel)))
    initial = frozenset(range(len(eqs)))
    distance = {initial: 0}
    queue = deque([initial])
    while queue:
        current = queue.popleft()
        for preserved in operation_congruences:
            remaining = current & preserved
            if remaining not in distance:
                distance[remaining] = distance[current] + 1
                queue.append(remaining)
    return eqs, distance


def audit() -> dict:
    started = time.perf_counter()
    # Derive the complete independent answers before importing reviewed code.
    derived = {n: explore(n) for n in range(1, 5)}
    spec = importlib.util.spec_from_file_location("reviewed_minimizer", ROOT / "minimize_operations.py")
    reviewed = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(reviewed)
    rows = []
    for n, (eqs, distance) in derived.items():
        for family, optimum in distance.items():
            actual = reviewed.choose_operations(n, [canonical(eqs[i], n) for i in sorted(family)])
            if not actual["passed"] or actual["minimum_unary_operation_count"] != optimum:
                raise AssertionError(f"n={n}: optimum mismatch for relation indices {sorted(family)}")
        rejected = 0
        equality = eqs.index(frozenset((x, x) for x in range(n)))
        universal = eqs.index(frozenset(product(range(n), repeat=2)))
        for selected in product((False, True), repeat=len(eqs)):
            family = frozenset(i for i, bit in enumerate(selected) if bit)
            if family in distance:
                continue
            # n=4 controls include both unavoidable relations, so rejection
            # checks more than the missing-equality/universal special case.
            if n == 4 and not {equality, universal} <= family:
                continue
            actual = reviewed.choose_operations(n, [canonical(eqs[i], n) for i in sorted(family)])
            if actual["passed"] or actual["minimum_unary_operation_count"] is not None:
                raise AssertionError(f"n={n}: impossible relation family accepted: {sorted(family)}")
            rejected += 1
            if n == 4 and rejected == 32:
                break
        rows.append({"carrier_size": n, "equivalence_relations": len(eqs), "total_unary_maps": n ** n,
                     "all_representable_families_checked": len(distance),
                     "minimum_operation_histogram": dict(sorted(Counter(distance.values()).items())),
                     "unrepresentable_families_rejected": rejected})
    return {"schema_version": 1, "passed": True,
            "method": "all binary equivalence tables; breadth-first intersections of congruence families of all unary maps",
            "scope": "all representable exact relation families on labeled carriers of sizes 1..4; all impossible families for n<=3 and 32 n=4 impossible families containing equality and universal",
            "limitations": "same-session AI implementation review, same Python runtime; no formal proof or mathematical novelty claim; no higher-arity minimization",
            "minimizer_sha256": hashlib.sha256((ROOT / "minimize_operations.py").read_bytes()).hexdigest(),
            "audit_script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "rows": rows, "seconds": round(time.perf_counter() - started, 6)}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, type=Path, help="JSON evidence destination")
    args = parser.parse_args()
    if args.out.resolve() in {Path(__file__).resolve(), (ROOT / "minimize_operations.py").resolve()}:
        parser.error("output must not overwrite reviewed code")
    try:
        result = audit()
    except (AssertionError, ValueError, TypeError, KeyError, OSError) as exc:
        result = {"schema_version": 1, "passed": False, "error": str(exc)}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps({"passed": result["passed"],
                      "families_checked": sum(row["all_representable_families_checked"] for row in result.get("rows", [])),
                      "output": str(args.out)}))
    return 0 if result["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
