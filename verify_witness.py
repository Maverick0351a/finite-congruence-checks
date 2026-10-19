"""Independently verify a finite IsGraphWitness certificate using only stdlib.

Every nonempty subset of ORDERED vertex pairs, including diagonal pairs, is
enumerated. This verifier does not import the search implementation or apply
its reduction to unordered seed edges. Equivalence closure uses bitset BFS.
Python 3.10+. The default exhaustive limit supports at most four vertices.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
from itertools import permutations, product
import json
from pathlib import Path
import time

SOURCE = {
    "repository": "https://github.com/openai/math",
    "revision": "1581d4cbdd69a0faf34b2089614fe2a814316a6a",
    "path": "lean/ComparatorChallenges/FiniteCongruenceGraph.lean",
    "sha256": "2ee495def2e1228bf13df520f6c66699ec22b2cd3bc1ae7383a30957aae9f967",
    "family": "206",
}
DEFAULT_MAX_SEED_SUBSETS = 65535


class VerificationLimit(ValueError):
    """A well-formed certificate exceeds the requested exhaustive budget."""


def validate_lattice(lattice: dict) -> dict:
    """Check a finite poset, its bottom, specified joins and derived meets.

    Element labels are distinct strings; all operation entries use zero-based
    element indices. Joins are verified by the least-upper-bound definition,
    rather than by a selected collection of algebraic identities. Meets are
    derived by testing the greatest-lower-bound definition for each pair.
    """
    if not isinstance(lattice, dict):
        raise ValueError("lattice must be an object")
    if not isinstance(lattice.get("name"), str) or not lattice["name"]:
        raise ValueError("lattice.name must be a nonempty string")
    labels = lattice.get("elements")
    if (not isinstance(labels, list) or not labels
            or any(not isinstance(label, str) for label in labels)
            or len(set(labels)) != len(labels)):
        raise ValueError("lattice.elements must be a nonempty list of distinct string labels")
    size = len(labels)
    bottom = lattice.get("bottom")
    if type(bottom) is not int or not 0 <= bottom < size:
        raise ValueError("lattice.bottom must be an element index")
    leq, join = lattice.get("leq"), lattice.get("join")
    for name, matrix in [("leq", leq), ("join", join)]:
        if (not isinstance(matrix, list) or len(matrix) != size
                or any(not isinstance(row, list) or len(row) != size for row in matrix)):
            raise ValueError(f"lattice.{name} must be an elements-by-elements matrix")
    if any(type(value) is not bool for row in leq for value in row):
        raise ValueError("lattice.leq entries must be JSON booleans")
    if any(type(value) is not int or not 0 <= value < size for row in join for value in row):
        raise ValueError("lattice.join entries must be element indices")
    for a in range(size):
        if not leq[a][a]:
            raise ValueError(f"lattice order is not reflexive at {a}")
        if not leq[bottom][a]:
            raise ValueError(f"lattice.bottom is not below element {a}")
        for b in range(size):
            if a != b and leq[a][b] and leq[b][a]:
                raise ValueError(f"lattice order is not antisymmetric at {a}, {b}")
            for c in range(size):
                if leq[a][b] and leq[b][c] and not leq[a][c]:
                    raise ValueError(f"lattice order is not transitive at {a}, {b}, {c}")
    meet = [[0] * size for _ in range(size)]
    for a, b in product(range(size), repeat=2):
        claimed_join = join[a][b]
        upper = [u for u in range(size) if leq[a][u] and leq[b][u]]
        if claimed_join not in upper or any(not leq[claimed_join][u] for u in upper):
            raise ValueError(f"lattice.join[{a}][{b}] is not the least upper bound")
        lower = [u for u in range(size) if leq[u][a] and leq[u][b]]
        greatest = [u for u in lower if all(leq[v][u] for v in lower)]
        if len(greatest) != 1:
            raise ValueError(f"elements {a}, {b} do not have a unique greatest lower bound")
        meet[a][b] = greatest[0]
    return {"passed": True, "element_count": size, "derived_meet": meet}


def equivalence_closure(size: int, marked_bits: int) -> tuple[int, ...]:
    """Return reachable-vertex bitsets for EqvGen of a directed marked relation.

    Reflexivity adds each starting vertex, symmetry makes the adjacency
    undirected, and BFS reaches precisely its transitive closure.
    """
    neighbors = [1 << v for v in range(size)]
    remaining = marked_bits
    while remaining:
        bit = remaining & -remaining
        left, right = divmod(bit.bit_length() - 1, size)
        neighbors[left] |= 1 << right
        neighbors[right] |= 1 << left
        remaining ^= bit
    rows = []
    for start in range(size):
        reached, frontier = 0, 1 << start
        while frontier:
            reached |= frontier
            next_frontier = 0
            while frontier:
                bit = frontier & -frontier
                next_frontier |= neighbors[bit.bit_length() - 1]
                frontier ^= bit
            frontier = next_frontier & ~reached
        rows.append(reached)
    return tuple(rows)


def structural_checks(lattice: dict, color: list[list[int]]) -> dict:
    """Four graph conjuncts for already validated lattice/matrix domains.

    Exposed so exhaustive rechecks can reject structural failures without
    spending exponential time on an already false conjunction.
    """
    size, levels = len(color), len(lattice["elements"])
    leq, join, bottom = lattice["leq"], lattice["join"], lattice["bottom"]
    pairs = list(product(range(size), repeat=2))
    return {
        "symmetric": all(color[a][b] == color[b][a] for a, b in pairs),
        "bottom_iff_diagonal": all((color[a][b] == bottom) == (a == b) for a, b in pairs),
        "triangle_join": all(leq[color[a][b]][join[color[a][m]][color[m][b]]]
                             for a, b, m in product(range(size), repeat=3)),
        "order_separation": all(
            any(leq[color[a][b]][lower] and not leq[color[a][b]][upper] for a, b in pairs)
            for lower, upper in product(range(levels), repeat=2) if not leq[lower][upper]),
    }


def verify_witness(lattice: dict, color: list[list[int]], *,
                   max_seed_subsets: int = DEFAULT_MAX_SEED_SUBSETS) -> dict:
    """Evaluate every conjunct of the pinned finite predicate.

    Invalid domains/lattices and requests above the resource limit raise
    ValueError. Well-formed matrices return all five predicate results, even
    when an earlier conjunct fails. An empty carrier is rejected because the
    target HasGraphWitness also requires a positive carrier size.
    """
    lattice_validation = validate_lattice(lattice)
    levels = len(lattice["elements"])
    if (not isinstance(color, list) or not color
            or any(not isinstance(row, list) or len(row) != len(color) for row in color)):
        raise ValueError("color must be a nonempty square matrix")
    size = len(color)
    if any(type(value) is not int or not 0 <= value < levels for row in color for value in row):
        raise ValueError("color entries must be lattice element indices")
    if type(max_seed_subsets) is not int or max_seed_subsets < 1:
        raise ValueError("max_seed_subsets must be a positive integer")
    total_seed_subsets = (1 << (size * size)) - 1
    if total_seed_subsets > max_seed_subsets:
        raise VerificationLimit(f"{total_seed_subsets} ordered seed subsets exceed the explicit limit "
                                f"{max_seed_subsets}; verification was not performed")
    leq, join, bottom = lattice["leq"], lattice["join"], lattice["bottom"]
    pairs = list(product(range(size), repeat=2))
    checks = structural_checks(lattice, color)
    admissible = [placement for placement in product(range(size), repeat=size)
                  if all(leq[color[placement[a]][placement[b]]][color[a][b]] for a, b in pairs)]
    # For a single seed, take the literal union over EVERY admissible placement.
    # Unioning these relations over a seed subset matches Marked's two existentials.
    seed_images = []
    for a, b in pairs:
        bits = 0
        for placement in admissible:
            bits |= 1 << (placement[a] * size + placement[b])
        seed_images.append(bits)

    bounds = [bottom] * (total_seed_subsets + 1)
    images = [0] * (total_seed_subsets + 1)
    evaluated = {}
    failed_count, first_failure = 0, None
    for mask in range(1, total_seed_subsets + 1):
        bit = mask & -mask
        index, previous = bit.bit_length() - 1, mask ^ bit
        a, b = pairs[index]
        bounds[mask] = join[bounds[previous]][color[a][b]]
        images[mask] = images[previous] | seed_images[index]
        key = (bounds[mask], images[mask])
        if key not in evaluated:
            reachable = equivalence_closure(size, images[mask])
            evaluated[key] = next(((a, b) for a, b in pairs
                                   if leq[color[a][b]][bounds[mask]]
                                   and not (reachable[a] & (1 << b))), None)
        failing_pair = evaluated[key]
        if failing_pair is not None:
            failed_count += 1
            if first_failure is None:
                first_failure = {
                    "seed_mask": mask,
                    "ordered_seeds": [list(pair) for index, pair in enumerate(pairs)
                                      if mask & (1 << index)],
                    "join_bound": bounds[mask],
                    "disconnected_pair_below_bound": list(failing_pair),
                }
    checks["seed_connectivity"] = failed_count == 0
    return {
        "passed": all(checks.values()),
        "valid_input": True,
        "verification_completed": True,
        "lattice_validation": lattice_validation,
        "carrier_size": size,
        "candidate_self_maps": size ** size,
        "admissible_self_maps": len(admissible),
        "ordered_seed_pairs": len(pairs),
        "nonempty_ordered_seed_subsets_enumerated": total_seed_subsets,
        "distinct_connectivity_cases": len(evaluated),
        "failed_seed_subsets": failed_count,
        "first_connectivity_failure": first_failure,
        "checks": checks,
    }


def verify_search_record(record: dict) -> dict:
    """Independently exhaust the recorded lattices through the recorded bound.

    The bound must be 1..4. All symmetric, bottom-diagonal matrices are
    generated afresh, rather than taking the search's survivor list as complete.
    Structural failures are rejected immediately. Every structural survivor is
    checked against the literal ordered-seed predicate. Vertex classes are
    independently grouped by their full matrices under every permutation.
    """
    maximum = record.get("max_vertices")
    if type(maximum) is not int or not 1 <= maximum <= 4:
        raise ValueError("search record max_vertices must be an integer in 1..4")
    data_by_name = record.get("lattices")
    if not isinstance(data_by_name, dict) or not data_by_name:
        raise ValueError("search record must contain a nonempty lattices object")
    started = time.perf_counter()
    rows, all_matches = [], True
    minima = {}

    def full_matrix_key(matrix):
        n = len(matrix)
        return min(tuple(matrix[p[a]][p[b]] for a in range(n) for b in range(n))
                   for p in permutations(range(n)))

    for name, data in data_by_name.items():
        lattice = data["lattice"]
        validate_lattice(lattice)
        reported_rows = data["sizes"]
        if (len(reported_rows) != maximum
                or sorted(row["vertices"] for row in reported_rows) != list(range(1, maximum + 1))):
            raise ValueError(f"{name}: sizes must contain each positive size through max_vertices once")
        claimed_by_size = {row["vertices"]: row for row in reported_rows}
        smallest = None
        for n in range(1, maximum + 1):
            palette = [value for value in range(len(lattice["elements"]))
                       if value != lattice["bottom"]]
            upper_pairs = [(a, b) for a in range(n) for b in range(a + 1, n)]
            candidate_count, survivor_count, witness_count, seed_count = 0, 0, 0, 0
            class_counts = {}
            structural_rejections = {}
            first_failure = None
            for assignment in product(palette, repeat=len(upper_pairs)):
                matrix = [[lattice["bottom"] for _ in range(n)] for _ in range(n)]
                for index, (a, b) in enumerate(upper_pairs):
                    matrix[a][b] = assignment[index]
                    matrix[b][a] = assignment[index]
                candidate_count += 1
                structure = structural_checks(lattice, matrix)
                if not all(structure.values()):
                    failure = next(key for key, passed in structure.items() if not passed)
                    failure = {"symmetric": "symmetry", "triangle_join": "triangle"}.get(failure, failure)
                    structural_rejections[failure] = structural_rejections.get(failure, 0) + 1
                    continue
                survivor_count += 1
                verification = verify_witness(lattice, matrix)
                seed_count += verification["nonempty_ordered_seed_subsets_enumerated"]
                if not verification["passed"]:
                    if first_failure is None:
                        first_failure = {"color": matrix, "verification": verification}
                    continue
                witness_count += 1
                key = full_matrix_key(matrix)
                class_counts[key] = class_counts.get(key, 0) + 1
            if witness_count and smallest is None:
                smallest = n
            claimed = claimed_by_size[n]
            expected_classes, representatives = {}, []
            for rep in claimed["representatives"]:
                verification = verify_witness(lattice, rep["color"])
                key = full_matrix_key(rep["color"])
                if key in expected_classes:
                    raise ValueError(f"{name}, n={n}: repeated vertex-isomorphism class")
                expected_classes[key] = rep["labeled_count"]
                representatives.append({"color": rep["color"], "verification": verification})
            matches = {
                "candidate_count": candidate_count == claimed["counts"].get("candidates", 0),
                "expected_candidate_count": candidate_count == claimed["expected_candidates"],
                "structural_survivor_count": survivor_count == claimed["counts"].get("structurally_valid", 0),
                "structural_rejection_counts": structural_rejections == {
                    key: value for key, value in claimed["counts"].items()
                    if key not in {"candidates", "structurally_valid", "witnesses", "seed_connectivity"}},
                "witness_count": witness_count == claimed["counts"].get("witnesses", 0),
                "connectivity_failure_count": survivor_count - witness_count
                    == claimed["counts"].get("seed_connectivity", 0),
                "vertex_class_count": len(class_counts) == claimed["vertex_isomorphism_classes"],
                "class_members_and_multiplicities": class_counts == expected_classes,
                "all_reported_representatives_pass": all(rep["verification"]["passed"] for rep in representatives),
            }
            all_matches = all_matches and all(matches.values())
            rows.append({
                "lattice": name, "vertices": n,
                "labeled_candidates_checked": candidate_count,
                "structural_survivors_checked": survivor_count,
                "structural_rejection_counts": structural_rejections,
                "witnesses": witness_count,
                "vertex_isomorphism_classes": len(class_counts),
                "ordered_seed_subsets_enumerated_across_survivors": seed_count,
                "first_connectivity_failure": first_failure,
                "reported_representatives": representatives,
                "matches_primary_record": matches,
            })
        minima[name] = {"independent_minimum_vertices_found": smallest,
                        "matches_primary_record": smallest == data["minimum_vertices_found"],
                        "all_positive_sizes_through": maximum}
        all_matches = all_matches and minima[name]["matches_primary_record"]
    return {
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "source": SOURCE,
        "verifier_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "search_record_content_sha256": hashlib.sha256(
            json.dumps(record, sort_keys=True, separators=(",", ":")).encode("utf-8")).hexdigest(),
        "method": "Independent exhaustive coloring enumeration, literal ordered seeds, BFS closure, full-matrix permutation classes",
        "all_expected_outcomes": bool(all_matches),
        "minimum_vertices": minima,
        "rows": rows,
        "seconds": round(time.perf_counter() - started, 6),
        "limitations": [
            "Finite computation in Python; no Lean compilation or mechanized equivalence proof.",
            "Minimality applies only to the specified lattice and graph-witness predicate.",
            "No witness through the bound is not a nonexistence conclusion above the bound.",
            "No novelty conclusion or verification of the general graph criterion theorem.",
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path, help="JSON object containing lattice and color")
    parser.add_argument("--output", type=Path, help="Default: certificate.verification.json")
    parser.add_argument("--max-seed-subsets", type=int, default=DEFAULT_MAX_SEED_SUBSETS,
                        help="Explicit exhaustive resource limit; default supports up to 4 vertices")
    args = parser.parse_args()
    destination = args.output or args.certificate.with_suffix(".verification.json")
    if destination.resolve() == args.certificate.resolve():
        parser.error("output must differ from the input certificate")
    started = time.perf_counter()
    raw = None
    try:
        raw = args.certificate.read_bytes()
        certificate = json.loads(raw)
        if not isinstance(certificate, dict) or not {"lattice", "color"} <= certificate.keys():
            raise ValueError("certificate must be an object containing lattice and color")
        result = verify_witness(certificate["lattice"], certificate["color"],
                                max_seed_subsets=args.max_seed_subsets)
        code = 0 if result["passed"] else 1
    except VerificationLimit as exc:
        result = {"passed": False, "valid_input": True, "verification_completed": False,
                  "error": str(exc)}
        code = 2
    except (ValueError, OSError, UnicodeError) as exc:
        result = {"passed": False, "valid_input": False, "verification_completed": False,
                  "error": str(exc)}
        code = 2
    result.update({
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "seconds": round(time.perf_counter() - started, 6),
        "source": SOURCE,
        "certificate": args.certificate.name,
        "certificate_sha256": hashlib.sha256(raw).hexdigest() if raw is not None else None,
        "verifier_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "method": "Literal ordered seed-subset enumeration; all self-maps; bitset BFS equivalence closure",
        "limitations": [
            "Checks the supplied finite witness; no search, minimality or novelty conclusion.",
            "No Lean compilation or mechanically proved Python/Lean equivalence.",
            "The general graph criterion theorem and its proof are not verified.",
        ],
    })
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(f"passed={result['passed']}; saved {destination}")
    return code


if __name__ == "__main__":
    raise SystemExit(main())
