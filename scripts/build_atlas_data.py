"""Build the complete unary representation atlas on carriers of one to four points.

    python scripts/build_atlas_data.py
    python scripts/build_atlas_data.py --check

Every total unary map is enumerated. Starting with every equivalence relation,
intersecting with a map's invariant relations enumerates every representable
exact family; breadth-first distance is its minimum number of unary operations.
All vertex permutations identify embeddings that differ only by vertex names.
An exhaustive order-isomorphism search identifies abstract lattice shapes.

For each canonical embedding, the existing independent set-cover minimizer
constructs minimum operations in that embedding's own vertex labeling. This
avoids attaching operations from a differently labeled representative.

Outputs contain no clock, machine path, or changing Git HEAD. Text source hashes
normalize CRLF to LF so the evidence is reproducible across checkout platforms.
--check recomputes everything and compares all three output files byte for byte.
This is bounded computational evidence, not a Lean proof or novelty claim.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import importlib.util
from itertools import permutations
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
INPUT_PATHS = (
    "evidence/operation-minima-audit.json",
    "evidence/search-results.json",
    "minimize_operations.py",
    "scripts/audit_operation_minima.py",
)
OUTPUT_PATHS = ("evidence/atlas.json", "space/atlas-data.json", "space/atlas-data.js")


def require(condition: bool, message: str) -> None:
    """Evidence checks remain active with Python's -O flag."""
    if not condition:
        raise ValueError(message)


def source_digest(path: Path) -> str:
    """Hash UTF-8 text with CRLF normalized to LF, preserving other bytes."""
    content = path.read_bytes()
    content.decode("utf-8")  # Reject non-UTF-8 input rather than hashing ambiguously.
    return hashlib.sha256(content.replace(b"\r\n", b"\n")).hexdigest()


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, f"Cannot load {path.name}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def normal(partition: tuple[int, ...]) -> tuple[int, ...]:
    labels = {}
    return tuple(labels.setdefault(value, len(labels)) for value in partition)


def covers(order: tuple[tuple[bool, ...], ...]) -> list[list[int]]:
    size = len(order)
    return [[lower, upper] for lower in range(size) for upper in range(size)
            if lower != upper and order[lower][upper]
            and not any(middle not in (lower, upper)
                        and order[lower][middle] and order[middle][upper]
                        for middle in range(size))]


def node_profiles(order: tuple[tuple[bool, ...], ...]) -> tuple[tuple[int, ...], ...]:
    """Necessary order-isomorphism invariants; these alone never decide equality."""
    edges = covers(order)
    size = len(order)
    return tuple((sum(order[j][i] for j in range(size)), sum(order[i]),
                  sum(upper == i for _, upper in edges),
                  sum(lower == i for lower, _ in edges)) for i in range(size))


def isomorphic(left: tuple[tuple[bool, ...], ...],
               right: tuple[tuple[bool, ...], ...]) -> bool:
    """Exhaust candidate bijections, checking both directions of every order pair."""
    if len(left) != len(right):
        return False
    lp, rp = node_profiles(left), node_profiles(right)
    if sorted(lp) != sorted(rp):
        return False
    domains = [[j for j in range(len(right)) if lp[i] == rp[j]]
               for i in range(len(left))]
    assigned, used = {}, set()

    def visit() -> bool:
        if len(assigned) == len(left):
            return True
        remaining = {}
        for i in range(len(left)):
            if i in assigned:
                continue
            options = [j for j in domains[i] if j not in used and all(
                left[i][a] == right[j][b] and left[a][i] == right[b][j]
                for a, b in assigned.items())]
            if not options:
                return False
            remaining[i] = options
        i = min(remaining, key=lambda a: (len(remaining[a]), a))
        for j in remaining[i]:
            assigned[i] = j
            used.add(j)
            if visit():
                return True
            used.remove(j)
            del assigned[i]
        return False

    return visit()


def controls(optimizer) -> list[str]:
    """Controls exercise rejection paths without relying on disabled assertions."""
    require(not optimizer.choose_operations(2, [(0, 0)])["passed"],
            "Control failed: a family missing equality was accepted")
    c4 = tuple(tuple(a <= b for b in range(4)) for a in range(4))
    b2 = tuple(tuple((a & b) == a for b in range(4)) for a in range(4))
    require(not isomorphic(c4, b2), "Control failed: C4 was identified with B2")
    perm = (3, 1, 0, 2)
    renamed = tuple(tuple(c4[perm[a]][perm[b]] for b in range(4)) for a in range(4))
    require(isomorphic(c4, renamed), "Control failed: relabeled C4 was not recognized")
    return ["family missing equality rejected", "C4 distinguished from B2",
            "relabeled C4 recognized", "removing any selected operation changes its family"]


def build() -> dict:
    hashes = {name: source_digest(ROOT / name) for name in INPUT_PATHS}
    generator_hash = source_digest(Path(__file__))
    audit = load_module("atlas_relation_audit", ROOT / "scripts/audit_operation_minima.py")
    optimizer = load_module("atlas_operation_minimizer", ROOT / "minimize_operations.py")
    previous = json.loads((ROOT / "evidence/operation-minima-audit.json").read_text(encoding="utf-8"))
    search = json.loads((ROOT / "evidence/search-results.json").read_text(encoding="utf-8"))
    require(previous["passed"] is True and previous["schema_version"] == 1,
            "The recorded operation audit must have passed")
    require([row["carrier_size"] for row in previous["rows"]] == [1, 2, 3, 4],
            "The operation audit must cover exactly carriers 1 through 4")
    require(search["max_vertices"] == 4, "Unexpected named-target search scope")
    control_names = controls(optimizer)
    entries, abstract_types, summaries = [], [], []
    orders = {}

    for n in range(1, 5):
        eqs, families = audit.explore(n)
        distance = {sum(1 << i for i in family): depth for family, depth in families.items()}
        recorded = previous["rows"][n - 1]
        require(len(distance) == recorded["all_representable_families_checked"],
                f"n={n}: family count disagrees with the operation audit")
        histogram = {str(key): value for key, value in sorted(Counter(distance.values()).items())}
        require(histogram == recorded["minimum_operation_histogram"],
                f"n={n}: operation minima disagree with the operation audit")
        partitions = [audit.canonical(relation, n) for relation in eqs]
        require(set(partitions) == set(optimizer.all_partitions(n)),
                f"n={n}: independent partition enumerators disagree")
        lookup = {partition: i for i, partition in enumerate(partitions)}
        transforms = [[lookup[normal(tuple(partition[v] for v in perm))]
                       for partition in partitions] for perm in permutations(range(n))]
        orbit_of = {}
        for mask in sorted(distance):
            orbit = {sum(1 << transform[i] for i in range(len(eqs)) if mask >> i & 1)
                     for transform in transforms}
            require(all(member in distance and distance[member] == distance[mask] for member in orbit),
                    f"n={n}: relabeling changed representability or operation minimum")
            orbit_of[mask] = min(orbit)
        orbit_sizes = Counter(orbit_of.values())
        for mask in sorted(orbit_sizes):
            selected_indices = [i for i in range(len(eqs)) if mask >> i & 1]
            target_partitions = [partitions[i] for i in selected_indices]
            selected_relations = [eqs[i] for i in selected_indices]
            order = tuple(tuple(a <= b for b in selected_relations) for a in selected_relations)
            matching = next((shape for shape in abstract_types
                             if isomorphic(order, orders[shape["id"]])), None)
            if matching is None:
                type_id = f"T{len(abstract_types) + 1:02d}"
                matching = {"id": type_id, "name": f"Shape {type_id}",
                            "lattice_elements": len(order), "embedding_ids": []}
                abstract_types.append(matching)
                orders[type_id] = order
            identity = f"n{n}-E{mask}"
            matching["embedding_ids"].append(identity)
            minimum = optimizer.choose_operations(n, target_partitions)
            require(minimum["passed"] and minimum["minimum_unary_operation_count"] == distance[mask],
                    f"{identity}: set cover and breadth-first operation minima disagree")
            operations = minimum["selected_unary_operations"]
            require(len(operations) == distance[mask], f"{identity}: operation count mismatch")
            for removed in range(len(operations)):
                reduced = operations[:removed] + operations[removed + 1:]
                recovered = {p for p in partitions if all(optimizer.preserves(f, p) for f in reduced)}
                require(recovered != set(target_partitions),
                        f"{identity}: removing a supposedly necessary operation changed nothing")
            entries.append({"id": identity, "carrier_size": n,
                            "abstract_type": matching["id"], "name": matching["name"],
                            "partitions": target_partitions, "operations": operations,
                            "minimum_unary_operations": distance[mask], "orbit_size": orbit_sizes[mask],
                            "order": order, "covers": covers(order), "named_targets": []})
        summaries.append({"carrier_size": n, "labeled_relation_families": len(distance),
                          "embedding_orbits": len(orbit_sizes),
                          "abstract_types": len({row["abstract_type"] for row in entries if row["carrier_size"] == n})})

    # Names describe abstract order types. They do not imply that an atlas
    # representative is byte-identical to a saved graph or has a Lean certificate.
    for name, group in search["lattices"].items():
        named_order = tuple(tuple(row) for row in group["lattice"]["leq"])
        for size in group["sizes"]:
            for representative in size["representatives"]:
                optimizer.read_targets({"lattice": group["lattice"], "color": representative["color"]})
        matching_types = [shape for shape in abstract_types if isomorphic(named_order, orders[shape["id"]])]
        require(len(matching_types) <= 1, f"{name}: duplicate abstract types")
        for shape in matching_types:
            require(shape["name"].startswith("Shape "), f"{name}: duplicate named target shape")
            shape["name"] = name
            for entry in entries:
                if entry["abstract_type"] == shape["id"]:
                    entry["name"] = name
                    entry["named_targets"].append(name)

    require(sum(row["labeled_relation_families"] for row in summaries) == 313,
            "Unexpected total number of labeled relation families")
    require(len(entries) == 39 and len(abstract_types) == 22,
            "Unexpected embedding or abstract-type total")
    require(sum(entry["orbit_size"] for entry in entries) == 313, "Orbits do not cover all labeled families")
    require({row["minimum_unary_operations"] for row in entries
             if row["name"] == "C4" and row["carrier_size"] == 4} == {1, 2},
            "The C4 examples must retain their distinct operation minima")
    require(hashes == {name: source_digest(ROOT / name) for name in INPUT_PATHS}
            and generator_hash == source_digest(Path(__file__)), "Input text changed during generation")
    return {
        "schema_version": 1,
        "scope": "All full congruence relation families of unary algebras on labeled carriers of sizes 1 through 4; one representative per vertex-relabeling orbit, grouped by abstract lattice order isomorphism.",
        "source_sha256": hashes,
        "generator_sha256": generator_hash,
        "hash_encoding": "SHA-256 of UTF-8 file bytes with CRLF normalized to LF; no other byte changes.",
        "encoding": "All indices are zero-based. Equal partition entries belong to one block. operation[x] is the image of object x. order[i][j] means partition i refines partition j. covers lists lower/upper partition indices. IDs are stable for this schema and enumeration order.",
        "evidence_status": "Exhaustive finite Python computation; the atlas entries and operation minima are not Lean proofs and carry no mathematical novelty claim.",
        "minimum_scope": "Minimum number of basic unary operations for the exact displayed relation family on its fixed carrier. The empty signature is permitted and has zero operations. This does not minimize over larger carriers, other embeddings, or higher-arity operations.",
        "method": "Binary equivalence tables; breadth-first intersections of invariant relation families for all total unary maps; all carrier permutations; exhaustive order-isomorphism backtracking; independent partition generation and two exact set-cover methods for each displayed representative.",
        "checks": {"passed": True, "negative_and_relabeling_controls": control_names},
        "carrier_summary": summaries,
        "abstract_types": abstract_types,
        "entries": entries,
    }


def generated_files(data: dict) -> dict[str, bytes]:
    text = json.dumps(data, ensure_ascii=False, indent=2) + "\n"
    return {OUTPUT_PATHS[0]: text.encode("utf-8"), OUTPUT_PATHS[1]: text.encode("utf-8"),
            OUTPUT_PATHS[2]: ("window.ATLAS_DATA = " + text.rstrip("\n") + ";\n").encode("utf-8")}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Rebuild and compare all generated bytes without writing")
    args = parser.parse_args()
    try:
        outputs = generated_files(build())
        if args.check:
            stale = [name for name, content in outputs.items()
                     if not (ROOT / name).is_file() or (ROOT / name).read_bytes() != content]
            require(not stale, "Atlas data is missing or stale: " + ", ".join(stale))
        else:
            for name, content in outputs.items():
                destination = ROOT / name
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(content)
        print(f"{'Checked' if args.check else 'Built'} atlas: 313 labeled families, 39 embedding orbits, 22 abstract types; all 3 files agree.")
        return 0
    except (OSError, ValueError, KeyError, TypeError, IndexError, AssertionError) as exc:
        print(f"Atlas export failed: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
