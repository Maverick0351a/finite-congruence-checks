"""Export deterministic, offline demo data from the pinned research evidence.

    python scripts/build_space_data.py
    python scripts/build_space_data.py --check

Both commands use only the standard library. They replay the eleven displayed
graphs, all seven algebra checks and fixed-representation operation minima; the
full bounded search is read from its independently replayed evidence record.
The seven passing certificates are copied byte for byte. Four negative demo
certificates wrap first-connectivity-failure matrices already in the search
record, with fresh verifier results and an explicit unreachable-pair explanation.
No original evidence is changed. No search outcome or failure is fabricated.

The manifest digest binds all 23 inputs to SOURCE_COMMIT (checked against Git
blobs when this exporter was authored). Updating those inputs requires updating
the anchor and this digest deliberately; --check never rewrites any file.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import minimize_operations
import search
import verify_algebra
import verify_witness

REPOSITORY = "https://github.com/Maverick0351a/finite-congruence-checks"
SOURCE_COMMIT = "355f6d3f0eba56969f3d2a2de2467706a5493db7"
INPUT_MANIFEST_SHA256 = "456622f89365dd3d4cdb6b29326d71299f206db47f809d7e302822f87f994503"
LATTICES = ("C2", "C3", "C4", "B2", "M3", "N5", "M4", "B3")
PASSING = tuple(name for name in LATTICES if name != "M4")
NEGATIVE = ("B2", "M3", "N5", "M4")
COUNT_FIELDS = ("candidates", "structural_survivors", "triangle_rejections",
                "order_separation_rejections", "connectivity_failures", "witnesses",
                "vertex_isomorphism_classes", "ordered_seed_subsets")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(content):
    return hashlib.sha256(content).hexdigest()


def encode(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode("utf-8")


def plain(value):
    """Normalize tuples from the checker APIs to the JSON representation."""
    return json.loads(json.dumps(value))


def input_paths():
    paths = ["search.py", "verify_witness.py", "verify_algebra.py", "minimize_operations.py",
             "reference/FiniteCongruenceGraph.lean"]
    paths += [f"evidence/{name}.json" for name in
              ("search-results", "independent-review-results", "verified-algebras", "minimized-algebras")]
    paths += [f"evidence/{name}-witness{suffix}.json" for name in PASSING for suffix in ("", ".verification")]
    return sorted(paths)


def pinned_inputs():
    contents = {path: (ROOT / path).read_bytes() for path in input_paths()}
    hashes = {path: digest(content) for path, content in contents.items()}
    manifest = json.dumps(hashes, sort_keys=True, separators=(",", ":")).encode("utf-8")
    require(digest(manifest) == INPUT_MANIFEST_SHA256,
            "Inputs differ from the pinned code/evidence commit; review the anchor before rebuilding")
    return contents, hashes


def compare_result(actual, recorded, label):
    """Compare every recomputed field; record-only provenance fields are allowed."""
    for key, value in plain(actual).items():
        require(key in recorded and value == recorded[key], f"{label}: mismatch in {key}")


def lattice_geometry(lattice):
    validation = verify_witness.validate_lattice(lattice)
    leq = lattice["leq"]
    n = len(leq)
    covers = [[a, b] for a in range(n) for b in range(n) if a != b and leq[a][b]
              and not any(c not in (a, b) and leq[a][c] and leq[c][b] for c in range(n))]
    depths = {}

    def depth(vertex):
        if vertex not in depths:
            depths[vertex] = max((depth(a) + 1 for a, b in covers if b == vertex), default=0)
        return depths[vertex]

    top = [b for b in range(n) if all(leq[a][b] for a in range(n))]
    require(len(top) == 1, "Finite lattice must have exactly one top")
    return dict(elements=lattice["elements"], bottom=lattice["bottom"], top=top[0],
                leq=leq, join=lattice["join"], meet=validation["derived_meet"],
                covers=covers, ranks=[depth(a) for a in range(n)])


def size_statistics(name, record, review_rows):
    require([r["vertices"] for r in record["sizes"]] == [1, 2, 3, 4], f"{name}: missing size")
    rows = []
    for raw in record["sizes"]:
        n, counts = raw["vertices"], raw["counts"]
        replay = review_rows.pop((name, n))
        row = dict(vertices=n, complete=raw["complete"], candidates=counts["candidates"],
                   structural_survivors=counts.get("structurally_valid", 0),
                   triangle_rejections=counts.get("triangle", 0),
                   order_separation_rejections=counts.get("order_separation", 0),
                   connectivity_failures=counts.get("seed_connectivity", 0),
                   witnesses=counts.get("witnesses", 0),
                   vertex_isomorphism_classes=raw["vertex_isomorphism_classes"],
                   ordered_seed_subsets=replay["ordered_seed_subsets_enumerated_across_survivors"])
        require(row["complete"], f"{name}/{n}: incomplete search")
        require(row["candidates"] == raw["expected_candidates"] ==
                (len(record["lattice"]["elements"]) - 1) ** math.comb(n, 2), f"{name}/{n}: candidate count")
        require(row["candidates"] == row["structural_survivors"] + row["triangle_rejections"] +
                row["order_separation_rejections"], f"{name}/{n}: structural attrition")
        require(row["structural_survivors"] == row["witnesses"] + row["connectivity_failures"],
                f"{name}/{n}: connectivity attrition")
        require(row["vertex_isomorphism_classes"] == len(raw["representatives"])
                and row["witnesses"] == sum(r["labeled_count"] for r in raw["representatives"]),
                f"{name}/{n}: class multiplicities")
        require(all(replay["matches_primary_record"].values()), f"{name}/{n}: independent replay failed")
        for key, other in (("candidates", "labeled_candidates_checked"),
                           ("structural_survivors", "structural_survivors_checked"),
                           ("witnesses", "witnesses"), ("vertex_isomorphism_classes", "vertex_isomorphism_classes")):
            require(row[key] == replay[other], f"{name}/{n}: independent {key} mismatch")
        rows.append(row)
    return dict(aggregate={key: sum(r[key] for r in rows) for key in COUNT_FIELDS}, sizes=rows,
                minimum_vertices=next((r["vertices"] for r in rows if r["witnesses"]), None))


def positive_example(name, cert, cert_bytes, recorded_verification, algebra, minimum, scope):
    primary = plain(search.check_witness(cert["lattice"], cert["color"]))
    require(primary == cert["primary_check"] and primary["passed"], f"{name}: primary graph check failed")
    verification = verify_witness.verify_witness(cert["lattice"], cert["color"])
    compare_result(verification, recorded_verification, f"{name} graph verification")
    require(verification["passed"], f"{name}: independent graph check failed")
    recovered_algebra = verify_algebra.verify(cert)
    compare_result(recovered_algebra, algebra, f"{name} algebra")
    n, targets = minimize_operations.read_targets(cert)
    recovered_minimum = minimize_operations.choose_operations(n, targets)
    # The saved result adds one lattice-validation check at CLI level.
    for key, value in plain(recovered_minimum).items():
        if key == "checks":
            compare_result(value, minimum[key], f"{name} minimum checks")
        else:
            require(value == minimum[key], f"{name}: minimum mismatch in {key}")
    require(recovered_algebra["passed"] and recovered_minimum["passed"] and minimum["passed"]
            and all(minimum["checks"].values()), f"{name}: algebra/minimization failed")
    require(verification["admissible_self_maps"] == minimum["admissible_operation_count"],
            f"{name}: operation count differs from graph check")
    thresholds = []
    for index, threshold in enumerate(algebra["threshold_partitions"]):
        partition = threshold["partition"]
        require(threshold == minimum["threshold_partitions"][index], f"{name}: threshold mismatch")
        thresholds.append(dict(element=threshold["element"], element_index=index, partition=partition,
                               blocks=[[v for v, block in enumerate(partition) if block == b]
                                       for b in sorted(set(partition))]))
    return dict(id=f"{name}-pass", lattice_id=name, status="pass", vertices=n, color=cert["color"],
                origin="Saved passing witness; certificate copied byte for byte from pinned evidence.",
                primary_check=primary, verification=verification,
                operations=dict(admissible_count=minimum["admissible_operation_count"],
                                admissible_tables=minimum["admissible_operation_tables"],
                                minimum_count=minimum["minimum_unary_operation_count"],
                                selected_tables=minimum["selected_unary_operations"], checks=minimum["checks"], scope=scope),
                congruences=dict(count=algebra["congruence_count"], partitions=algebra["congruence_partitions"],
                                 threshold_partitions=thresholds, checks=algebra["checks"]),
                certificate=f"certificates/{name}-witness.json", certificate_sha256=digest(cert_bytes))


def explain_failure(lattice, color, verification):
    """Expose a literal seed instance and independently follow its marked edges."""
    case = verification["first_connectivity_failure"]
    require(case is not None, "Negative example has no reported failing seed")
    n, leq = len(color), lattice["leq"]
    pairs = list(itertools.product(range(n), repeat=2))
    maps = [f for f in itertools.product(range(n), repeat=n)
            if all(leq[color[f[a]][f[b]]][color[a][b]] for a, b in pairs)]
    seeds, endpoints = case["ordered_seeds"], case["disconnected_pair_below_bound"]
    bound = lattice["bottom"]
    for a, b in seeds:
        bound = lattice["join"][bound][color[a][b]]
    marked = sorted({(f[a], f[b]) for f in maps for a, b in seeds})
    adjacency = [{a} for a in range(n)]
    for a, b in marked:
        adjacency[a].add(b)
        adjacency[b].add(a)
    closure = []
    for start in range(n):
        reached, pending = {start}, [start]
        while pending:
            for vertex in sorted(adjacency[pending.pop()]):
                if vertex not in reached:
                    reached.add(vertex)
                    pending.append(vertex)
        closure.append(sorted(reached))
    start, end = endpoints
    require(len(maps) == verification["admissible_self_maps"] and bound == case["join_bound"],
            "Failure explanation differs from verifier")
    require(leq[color[start][end]][bound] and end not in closure[start], "Counterexample is reachable or outside bound")
    return dict(ordered_seeds=seeds, join_bound=bound, endpoints=endpoints,
                endpoint_color=color[start][end], marked_pairs=plain(marked),
                reachable_pairs=[[a, b] for a in range(n) for b in closure[a]],
                reachable_from_start=closure[start], target_below_bound=True, unreachable=True,
                explanation="The endpoint color lies below the join of the seed colors, but the endpoints are in different components of the reflexive, symmetric, transitive closure of all admissible images of these seeds.")


def negative_example(name, record, upstream, search_hash):
    row = next(r for r in record["sizes"] if r["first_connectivity_failure"] is not None)
    sample, lattice = row["first_connectivity_failure"], record["lattice"]
    color = sample["color"]
    primary = plain(search.check_witness(lattice, color))
    require({k: v for k, v in primary.items() if k != "failure"} == sample["result"],
            f"{name}: saved negative sample differs from primary checker")
    verification = verify_witness.verify_witness(lattice, color)
    require(not verification["passed"] and not verification["checks"]["seed_connectivity"]
            and all(value for key, value in verification["checks"].items() if key != "seed_connectivity"),
            f"{name}: negative example must fail connectivity alone")
    failure = explain_failure(lattice, color, verification)
    origin = ("Demo-generated negative certificate wrapping the first connectivity-failing matrix "
              "already recorded in the pinned bounded search. It is structurally valid and is not a passing witness.")
    source_pointer = f"/lattices/{name}/sizes/{row['vertices'] - 1}/first_connectivity_failure"
    certificate = dict(schema_version=1, source=upstream, lattice=lattice, color=color, primary_check=primary,
                       demo=dict(kind="recorded-connectivity-failure", origin=origin,
                                 source_commit=SOURCE_COMMIT, search_record="evidence/search-results.json",
                                 search_record_sha256=search_hash, source_json_pointer=source_pointer),
                       verification=verification, failure=failure)
    content = encode(certificate)
    example = dict(id=f"{name}-connectivity-failure", lattice_id=name, status="fail", vertices=len(color),
                   color=color, origin=origin, primary_check=primary, verification=verification, failure=failure,
                   operations=None, congruences=None, certificate=f"certificates/{name}-connectivity-failure.json",
                   certificate_sha256=digest(content), source_json_pointer=source_pointer)
    return example, content


def build():
    contents, hashes = pinned_inputs()
    records = {path: json.loads(raw) for path, raw in contents.items() if path.endswith(".json")}
    search_record = records["evidence/search-results.json"]
    review = records["evidence/independent-review-results.json"]
    algebra = records["evidence/verified-algebras.json"]
    minima = records["evidence/minimized-algebras.json"]
    upstream = search_record["source"]
    require(upstream == search.SOURCE and review["source"] == verify_witness.SOURCE,
            "Checker/source provenance mismatch")
    require(hashes["reference/FiniteCongruenceGraph.lean"] == upstream["sha256"], "Pinned Lean source mismatch")
    require(search_record["source_sha256"] == hashes["search.py"]
            and review["verifier_sha256"] == hashes["verify_witness.py"]
            and minima["minimizer_sha256"] == hashes["minimize_operations.py"], "Recorded checker hash mismatch")
    require(search_record["max_vertices"] == 4 and tuple(search_record["lattices"]) == LATTICES,
            "Unexpected search coverage")
    require(review["all_expected_outcomes"] and algebra["passed"] and minima["self_check"]["passed"],
            "Evidence checks did not pass")
    if "search_record_file_sha256" in review:
        require(review["search_record_file_sha256"] == hashes["evidence/search-results.json"], "Search replay hash mismatch")
    review_rows = {(r["lattice"], r["vertices"]): r for r in review["rows"]}
    algebra_rows = {r["lattice"]: r for r in algebra["certificates"]}
    minima_rows = {r["lattice"]: r for r in minima["certificates"]}
    registry = {r["path"]: r["sha256"] for r in search_record["certificates"]}
    require(len(review_rows) == 32 and len(registry) == 7 and set(algebra_rows) == set(minima_rows) == set(PASSING),
            "Missing or duplicate evidence records")
    outputs, lattices, failures = {}, [], []
    for name, record in search_record["lattices"].items():
        stats = size_statistics(name, record, review_rows)
        require(stats["minimum_vertices"] == review["minimum_vertices"][name]["independent_minimum_vertices_found"],
                f"{name}: minimum carrier mismatch")
        witness = None
        if name in PASSING:
            filename = f"{name}-witness.json"
            path, check_path = f"evidence/{filename}", f"evidence/{name}-witness.verification.json"
            cert, saved_verification = records[path], records[check_path]
            require(cert["lattice"] == record["lattice"] and cert["source"] == upstream, f"{name}: certificate provenance")
            require(hashes[path] == registry[filename] == saved_verification["certificate_sha256"] ==
                    algebra_rows[name]["sha256"] == minima_rows[name]["certificate_sha256"], f"{name}: certificate hashes")
            witness = positive_example(name, cert, contents[path], saved_verification, algebra_rows[name], minima_rows[name], minima["scope"])
            require(witness["vertices"] == stats["minimum_vertices"], f"{name}: saved witness size mismatch")
            outputs[witness["certificate"]] = contents[path]
        lattices.append(dict(id=name, name=name, **lattice_geometry(record["lattice"]), stats=stats, witness=witness))
        if name in NEGATIVE:
            example, content = negative_example(name, record, upstream, hashes["evidence/search-results.json"])
            failures.append(example)
            outputs[example["certificate"]] = content
    require(not review_rows, "Unused independent search rows")
    totals = {key: sum(lattice["stats"]["aggregate"][key] for lattice in lattices) for key in COUNT_FIELDS}
    totals.update(lattices=len(lattices), positive_lattices=len(PASSING), saved_witnesses=len(PASSING),
                  failure_examples=len(failures), max_vertices=search_record["max_vertices"])
    source = dict(upstream, family="206", url=f"{upstream['repository']}/blob/{upstream['revision']}/{upstream['path']}")
    data = dict(schema_version=1, title="Finite Congruence Checks", provenance=dict(
        repository=REPOSITORY, source_commit=SOURCE_COMMIT, upstream=source,
        input_manifest_sha256=INPUT_MANIFEST_SHA256,
        sources=[dict(path=path, sha256=sha, url=f"{REPOSITORY}/blob/{SOURCE_COMMIT}/{path}") for path, sha in hashes.items()],
        exporter=dict(path="scripts/build_space_data.py", sha256=digest(Path(__file__).read_bytes())),
        method="Deterministic extraction of pinned bounded-search evidence; fresh replay of every displayed graph, algebra and fixed-representation operation minimum."),
        scope=dict(search=search_record["search"], classes=search_record["isomorphism"], minima=minima["scope"],
                   negative="M4 has no passing graph witness on carriers of size 1 through 4 in this search. Larger carriers are outside this result.",
                   verification="The displayed results are exhaustive Python computations on finite inputs. They do not prove the general graph criterion, Python/Lean equivalence, or mathematical novelty.",
                   failure_examples="Negative certificate wrappers are demo-generated from recorded search samples; they are excluded from the seven saved passing witnesses and do not change aggregate search counts.",
                   ranks="Longest cover-chain distance from the bottom, used only for layout; these values do not assert that a lattice is graded.",
                   encoding="Lattice elements and carrier vertices use zero-based indices. color[x][y] is a lattice element index; operation[x] is the image of vertex x. Equal partition entries identify an equivalence class.",
                   freshness="No timestamps or machine paths are emitted. --check replays displayed checks and compares every generated byte; it does not rerun the complete bounded search."),
        totals=totals, lattices=lattices, failure_examples=failures)
    outputs["data.json"] = encode(data)
    return outputs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Check generated files without rewriting them")
    args = parser.parse_args()
    try:
        outputs = build()
        destination = ROOT / "space"
        if args.check:
            stale = [path for path, content in outputs.items()
                     if not (destination / path).is_file() or (destination / path).read_bytes() != content]
            expected_certificates = {path for path in outputs if path.startswith("certificates/")}
            extra = sorted(str(path.relative_to(destination)).replace("\\", "/")
                           for path in (destination / "certificates").glob("*.json")
                           if path.relative_to(destination).as_posix() not in expected_certificates)
            require(not stale and not extra, f"Demo data is stale or has unexpected certificates: {stale + extra}")
        else:
            for path, content in outputs.items():
                target = destination / path
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(content)
        print(f"{'Checked' if args.check else 'Built'} {len(outputs)} deterministic demo files: 8 lattices, 7 passing witnesses, 4 connectivity failures.")
        return 0
    except (OSError, ValueError, KeyError, TypeError, AssertionError) as exc:
        print(f"Demo export failed: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
