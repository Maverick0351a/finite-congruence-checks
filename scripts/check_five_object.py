"""Independent finite audit of two exact five-object congruence families.

Only the Python standard library is imported. All 5^5 label assignments are
canonicalized to enumerate partitions; unary maps are evaluated by literal
pair preservation. No historical search, atlas exporter, or Lean code runs.
The saved result is reproducible computational evidence, not a formal proof.
"""
from __future__ import annotations

import argparse
from functools import lru_cache
import hashlib
from itertools import combinations_with_replacement, product
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
INPUT = "evidence/five-object-v1/constructions.json"
OUTPUT = "evidence/five-object-v1/computational.json"
SOURCE = "scripts/check_five_object.py"
CLAIM_ID = "context:family-206:five-object:operation-minima:v1"
HASH_ENCODING = "SHA-256 of UTF-8 file bytes with CRLF normalized to LF; no other byte changes."


def require(condition, message):
    if not condition:
        raise ValueError(message)


def encode(value):
    return (json.dumps(value, indent=2, ensure_ascii=False, allow_nan=False) + "\n").encode("utf-8")


def _unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "Duplicate JSON key: " + key)
        result[key] = value
    return result


def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"), object_pairs_hook=_unique_object)


def write(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(encode(value))


def digest(path):
    return hashlib.sha256(Path(path).read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def canonical(labels):
    seen = {}
    return tuple(seen.setdefault(label, len(seen)) for label in labels)


@lru_cache(maxsize=1)
def partitions():
    """Enumerate all equivalence relations from all finite label assignments."""
    return tuple(sorted({canonical(labels) for labels in product(range(5), repeat=5)}))


def preserves(operation, grouping):
    return all(grouping[x] != grouping[y] or grouping[operation[x]] == grouping[operation[y]]
               for x in range(5) for y in range(x + 1, 5))


def refines(first, second):
    return all(first[x] != first[y] or second[x] == second[y]
               for x in range(5) for y in range(x + 1, 5))


def family(operations):
    return tuple(p for p in partitions() if all(preserves(op, p) for op in operations))


def mask(groupings):
    selected = set(groupings)
    return sum(1 << i for i, p in enumerate(partitions()) if p in selected)


@lru_cache(maxsize=1)
def unary_maps():
    """All 3,125 maps with the exact set of partitions each one preserves."""
    return tuple((op, mask(family((op,)))) for op in product(range(5), repeat=5))


def expected_input():
    return {
        "schema_version": 1,
        "namespace": "finite-congruence-atlas/five-object-v1",
        "id": CLAIM_ID,
        "kind": "exact_construction_inputs",
        "scope": "Two particular unary algebras on the fixed carrier {0,1,2,3,4}.",
        "assumptions": [
            "A grouping is an equivalence relation represented by canonical block labels.",
            "A unary rule is a total map from this carrier to itself.",
            "Minimum counts range over arbitrary finite lists of unary rules realizing the exact relation family."
        ],
        "limits": [
            "This input is not proof evidence. Computational and Lean receipts are separate.",
            "The comparison is of exact relation families, not a minimum over all embeddings, larger carriers, or higher-arity operations.",
            "No complete five-object census, mathematical novelty, or agent-performance benefit is claimed."
        ],
        "values": {
            "carrier": [0, 1, 2, 3, 4],
            "A": {
                "id": "saved:family-206:five-object:three-rule:v1",
                "operations": [[0, 0, 4, 0, 0], [0, 3, 1, 1, 4], [1, 1, 3, 3, 3]],
                "groupings": [[0, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 2], [0, 1, 1, 1, 0],
                              [0, 1, 2, 1, 0], [0, 1, 2, 1, 1], [0, 1, 2, 1, 3], [0, 1, 2, 3, 4]],
                "minimum_unary_operations": 3,
            },
            "B": {
                "id": "saved:family-206:five-object:two-rule:v1",
                "operations": [[4, 1, 3, 2, 4], [1, 2, 3, 3, 3]],
                "groupings": [[0, 0, 0, 0, 0], [0, 1, 1, 1, 0], [0, 1, 1, 1, 1], [0, 1, 1, 1, 2],
                              [0, 1, 2, 2, 1], [0, 1, 2, 2, 2], [0, 1, 2, 2, 3], [0, 1, 2, 3, 4]],
                "minimum_unary_operations": 2,
            },
            "A_to_B": [0, 2, 4, 1, 3, 5, 6, 7],
        },
        "obstructing_groupings": {
            "A": [[0, 0, 0, 0, 1], [0, 0, 1, 2, 3], [0, 1, 2, 3, 0], [0, 1, 2, 3, 1]],
            "B": [[0, 0, 0, 0, 1], [0, 0, 1, 1, 0]],
        },
    }


def _vector(value, length=5, maximum=4, grouping=False):
    require(type(value) is list and len(value) == length, "Incorrect vector length or type")
    require(all(type(x) is int and 0 <= x <= maximum for x in value), "Values must be in-range integers")
    if grouping:
        require(tuple(value) == canonical(value), "Grouping must use canonical block labels")
    return tuple(value)


def _validate_input(document):
    """Check types before equality; JSON booleans must not stand for integers."""
    expected = expected_input()
    require(type(document) is dict and set(document) == set(expected), "Unexpected input fields")
    require(type(document["schema_version"]) is int and document["schema_version"] == 1, "Invalid schema version")
    for key in ("namespace", "id", "kind", "scope", "assumptions", "limits"):
        require(document[key] == expected[key], "Unexpected input metadata: " + key)
    values = document["values"]
    require(type(values) is dict and set(values) == {"carrier", "A", "B", "A_to_B"}, "Unexpected values fields")
    require(_vector(values["carrier"]) == tuple(range(5)), "Incorrect carrier")
    for name in ("A", "B"):
        value = values[name]
        require(type(value) is dict and set(value) == {"id", "operations", "groupings", "minimum_unary_operations"},
                "Unexpected construction fields")
        require(value["id"] == expected["values"][name]["id"], "Incorrect construction identity")
        minimum = value["minimum_unary_operations"]
        require(type(minimum) is int and minimum == (3 if name == "A" else 2), "Incorrect proposed minimum")
        require(type(value["operations"]) is list and len(value["operations"]) == minimum, "Incorrect rule count")
        for operation in value["operations"]:
            _vector(operation)
        require(type(value["groupings"]) is list and len(value["groupings"]) == 8, "Expected eight groupings")
        groups = tuple(_vector(p, grouping=True) for p in value["groupings"])
        require(groups == tuple(sorted(set(groups))), "Groupings must be distinct and lexicographically ordered")
    _vector(values["A_to_B"], length=8, maximum=7)
    require(sorted(values["A_to_B"]) == list(range(8)), "Order mapping must be a bijection")
    obstructions = document["obstructing_groupings"]
    require(type(obstructions) is dict and set(obstructions) == {"A", "B"}, "Unexpected obstruction fields")
    for name, count in (("A", 4), ("B", 2)):
        require(type(obstructions[name]) is list and len(obstructions[name]) == count, "Incorrect obstruction count")
        rows = tuple(_vector(p, grouping=True) for p in obstructions[name])
        require(len(set(rows)) == count, "Repeated obstruction grouping")


def mathematical_audit(document):
    """Recompute conclusions; accepting an edited input does not bind an old proof."""
    _validate_input(document)
    all_partitions = partitions()
    all_maps = unary_maps()
    require(len(all_partitions) == 52 and len(all_maps) == 3125, "Incomplete finite enumeration")
    results = {}
    for name in ("A", "B"):
        values = document["values"][name]
        operations = tuple(tuple(op) for op in values["operations"])
        groupings = tuple(tuple(p) for p in values["groupings"])
        recovered = family(operations)
        require(recovered == groupings, name + ": rules do not give the declared complete grouping family")
        target_mask = mask(groupings)
        obstruction = tuple(tuple(p) for p in document["obstructing_groupings"][name])
        require(all(p not in groupings for p in obstruction), name + ": obstruction belongs to target family")
        admissible = [(op, m) for op, m in all_maps if m & target_mask == target_mask]
        # Any rule in an exact realization must preserve every target relation.
        # Thus the filter loses no possible realization of this exact family.
        profiles = []
        for op, operation_mask in admissible:
            destruction = [not preserves(op, p) for p in obstruction]
            profiles.append({"operation": list(op), "preserved_partition_indices": [
                i for i in range(52) if operation_mask & (1 << i)],
                "obstruction_destruction": destruction})
        distinct_profiles = sorted({tuple(row["obstruction_destruction"]) for row in profiles})
        full_mask = (1 << 52) - 1
        require(target_mask != full_mask, name + ": empty signature already realizes target")
        require(all(m != target_mask for _, m in admissible), name + ": a single rule realizes target")
        if name == "A":
            pair_count = 0
            witness_counts = [0] * len(obstruction)
            for (first, m), (second, n) in combinations_with_replacement(admissible, 2):
                pair_count += 1
                require(m & n != target_mask, "A: a pair realizes the target")
                witnesses = [i for i, p in enumerate(obstruction) if preserves(first, p) and preserves(second, p)]
                require(bool(witnesses), "A: compact obstruction certificate does not cover a candidate pair")
                witness_counts[witnesses[0]] += 1
            # A second, smaller check makes the explanatory profile argument explicit.
            require(all(not all(a or b for a, b in zip(first, second))
                        for first in distinct_profiles for second in distinct_profiles),
                    "A: two obstruction profiles destroy all four forbidden groupings")
        else:
            pair_count = 0
            witness_counts = [0] * len(obstruction)
            for op, _ in admissible:
                witnesses = [i for i, p in enumerate(obstruction) if preserves(op, p)]
                require(bool(witnesses), "B: compact obstruction certificate does not cover a candidate rule")
                witness_counts[witnesses[0]] += 1
        order = [[refines(p, q) for q in groupings] for p in groupings]
        covers = [[i, j] for i in range(8) for j in range(8) if i != j and order[i][j]
                  and not any(k not in (i, j) and order[i][k] and order[k][j] for k in range(8))]
        results[name] = {
            "construction_id": values["id"],
            "operations": values["operations"],
            "groupings": values["groupings"],
            "partition_indices": [all_partitions.index(p) for p in groupings],
            "distinct_groupings": len(recovered),
            "order": order,
            "covers": covers,
            "minimum_unary_operations": values["minimum_unary_operations"],
            "admissible_maps": len(admissible),
            "distinct_preservation_signatures": len({m for _, m in admissible}),
            "empty_signature_excluded": True,
            "single_rules_excluded": len(admissible),
            "unordered_pairs_with_repetition_excluded": pair_count,
            "obstructing_groupings": [list(p) for p in obstruction],
            "distinct_obstruction_destruction_profiles": [list(p) for p in distinct_profiles],
            "first_obstruction_witness_counts": witness_counts,
            "supplied_operation_destruction_profiles": [[not preserves(op, p) for p in obstruction] for op in operations],
            "admissible_map_records": profiles,
        }
    mapping = document["values"]["A_to_B"]
    require(all(results["A"]["order"][i][j] == results["B"]["order"][mapping[i]][mapping[j]]
                for i in range(8) for j in range(8)), "Proposed grouping mapping is not an order isomorphism")
    return {
        "schema_version": 1,
        "namespace": "finite-congruence-atlas/five-object-v1",
        "id": "evidence:family-206:five-object:finite-audit:v1",
        "claim_id": document["id"],
        "kind": "finite_computational_check",
        "evidence_status": "exhaustive_finite_computation",
        "scope": document["scope"],
        "assumptions": document["assumptions"],
        "limits": document["limits"] + ["The Python audit has not been proved correct; matching hashes do not supply a Lean proof."],
        "method": "All 3,125 label assignments produce 52 canonical partitions; all 3,125 total unary maps are evaluated by literal pair preservation. No project mathematics or historical search code is imported.",
        "checks": {"passed": True, "all_partition_assignments": 3125, "distinct_partitions": 52,
                   "all_unary_maps": 3125, "maximum_pair_comparisons_per_map": 520,
                   "construction_partition_classifications": 104, "order_comparisons": 64,
                   "order_isomorphism_A_to_B": mapping},
        "partition_enumeration": [list(p) for p in all_partitions],
        "constructions": results,
        "minimum_scope": "Exact specified relation family, fixed five-object carrier, unary total maps only.",
        "explanation": {
            "A": "To exclude 00001, a rule must have destruction profile 1000. Such a rule excludes none of 00123, 01230, 01231. Every other admissible rule excludes at most two of those three. Two rules therefore leave an extra grouping; the displayed three rules recover exactly the eight target groupings.",
            "B": "Every admissible rule preserves at least one of 00001 and 00110, both outside the target family. A single rule therefore leaves an extra grouping; the displayed pair recovers exactly the eight target groupings.",
        },
    }


def audit(input_path=None, root=ROOT):
    input_path = Path(input_path) if input_path is not None else Path(root) / INPUT
    result = mathematical_audit(read(input_path))
    # The machine-readable explanation names these registered obstructions.
    require(encode(read(input_path)) == encode(expected_input()), "Input differs from the registered exact constructions")
    result["hash_encoding"] = HASH_ENCODING
    result["source_sha256"] = {INPUT: digest(input_path), SOURCE: digest(Path(root) / SOURCE)}
    return result


def replay(path=None, input_path=None, root=ROOT):
    """Recompute the full finite audit and reject any changed saved field."""
    path = Path(path) if path is not None else Path(root) / OUTPUT
    saved = read(path)
    fresh = audit(input_path, root)
    require(encode(saved) == encode(fresh), "Saved finite audit differs from independent recomputation")
    return fresh


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("check", "replay"))
    parser.add_argument("--input", type=Path, default=ROOT / INPUT)
    parser.add_argument("--out", type=Path, default=ROOT / OUTPUT)
    args = parser.parse_args(argv)
    try:
        require(args.out.resolve() not in {args.input.resolve(), (ROOT / INPUT).resolve(), (ROOT / SOURCE).resolve()},
                "Output must not overwrite an input or checker source")
        result = audit(args.input) if args.command == "check" else replay(args.out, args.input)
        if args.command == "check":
            write(args.out, result)
        print(json.dumps({"passed": True, "command": args.command, "partitions": 52, "unary_maps": 3125,
                          "minimum_A": result["constructions"]["A"]["minimum_unary_operations"],
                          "minimum_B": result["constructions"]["B"]["minimum_unary_operations"],
                          "scope": result["minimum_scope"]}))
        return 0
    except (ValueError, OSError, TypeError, KeyError) as error:
        print("five-object audit failed: " + str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
