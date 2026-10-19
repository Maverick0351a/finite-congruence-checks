"""Query the checked atlas locally; stdout is versioned JSON, with source citations.

Examples:
  python scripts/query_atlas.py list --carrier 4 --shape C4 --min-rules 1
  python scripts/query_atlas.py show n4-E16403
  python scripts/query_atlas.py compare --shape C4 --carrier 4
  python scripts/query_atlas.py compare
  python scripts/query_atlas.py claims --entry n4-E16403
  python scripts/query_atlas.py build-claims --check

This reads the saved computational evidence. It does not rerun the census or
prove a mathematical claim. Source and receipt integrity are checked before
results are returned. No network, model, third-party package, or server is used.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
import hashlib
from itertools import combinations, permutations, product
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
ATLAS_PATH = "evidence/atlas.json"
REVIEW_PATH = "evidence/atlas-review.json"
CLAIMS_PATH = "evidence/atlas-claims.json"
CLAIM_OUTPUTS = (CLAIMS_PATH, "space/atlas-claims.json", "space/atlas-claims.js")
GENERATOR_PATH = "scripts/query_atlas.py"
HASH_ENCODING = "SHA-256 of UTF-8 file bytes with CRLF normalized to LF; no other byte changes."
SCOPE = "Minimum number of basic unary operations for each exact displayed relation family on its fixed carrier of one through four objects; empty operation signatures are permitted."
EVIDENCE_STATUS = "exhaustive_computation_independently_checked"
ASSUMPTIONS = [
    "Objects form the nonempty labeled carrier {0,...,n-1}; all operations are total unary maps.",
    "Congruences are exactly all partitions preserved by every selected operation; the empty signature is allowed.",
    "The saved independent Python review and its source hashes are the evidence boundary; this query does not rerun it.",
]
LIMITS = [
    "Operation minima fix the exact relation family and carrier; they do not minimize over other embeddings, larger carriers, or higher-arity operations.",
    "The atlas and this query have no Lean correctness proof, external peer-review claim, or mathematical novelty claim.",
    "Atlas shape names do not extend the existing saved N5/B3 graph proofs to atlas entries.",
]
SOURCE_PATHS = {"evidence/operation-minima-audit.json", "evidence/search-results.json",
                "minimize_operations.py", "scripts/audit_operation_minima.py"}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def normalized_bytes(path):
    content = Path(path).read_bytes()
    content.decode("utf-8")
    return content.replace(b"\r\n", b"\n")


def digest(path):
    return hashlib.sha256(normalized_bytes(path)).hexdigest()


def encode(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode("utf-8")


def normalize(labels):
    names = {}
    return tuple(names.setdefault(label, len(names)) for label in labels)


def relation_index(n):
    """Schema-v1 relation order, derived without importing mathematical code.

    The builder visits lexicographic Boolean symmetric-pair tables (False first)
    and retains equivalence relations. Sorting every canonical partition by the
    same pair-equality vector gives exactly that retained-table order.
    """
    eqs = {normalize(labels) for labels in product(range(n), repeat=n)}
    pairs = list(combinations(range(n), 2))
    return sorted(eqs, key=lambda p: tuple(p[x] == p[y] for x, y in pairs))


def check_entry_identity(entry):
    n = entry.get("carrier_size")
    require(type(n) is int and 1 <= n <= 4, "unsupported carrier_size")
    match = re.fullmatch(r"n([1-4])-E([1-9][0-9]*)", entry.get("id", ""))
    require(match is not None and int(match[1]) == n, "invalid schema-v1 entry id")
    eqs = relation_index(n)
    family = [tuple(p) for p in entry["partitions"]]
    require(len(family) == len(set(family)) and all(p in eqs for p in family),
            f"{entry['id']}: invalid canonical partitions")
    index = {p: i for i, p in enumerate(eqs)}
    mask = sum(1 << index[p] for p in family)
    require(mask == int(match[2]), f"{entry['id']}: relation-mask identity mismatch")
    orbit_masks = [sum(1 << index[normalize(p[v] for v in perm)] for p in family)
                   for perm in permutations(range(n))]
    require(mask == min(orbit_masks), f"{entry['id']}: identity is not the canonical relabeling representative")


def load_dataset(root=ROOT):
    """Read and bind saved evidence. This is an integrity gate, not a census replay."""
    root = Path(root)
    data = json.loads(normalized_bytes(root / ATLAS_PATH))
    review = json.loads(normalized_bytes(root / REVIEW_PATH))
    require(type(data.get("schema_version")) is int and data["schema_version"] == 1,
            "unsupported atlas schema_version")
    require(review.get("schema_version") == 1 and review.get("passed") is True,
            "independent review is missing or failed")
    require(data.get("hash_encoding") == review.get("hash_encoding") == HASH_ENCODING,
            "unsupported hash encoding")
    atlas_hash = digest(root / ATLAS_PATH)
    require(review.get("atlas_sha256") == atlas_hash, "independent review does not bind this atlas")
    require(review.get("checker_sha256") == digest(root / "scripts/check_atlas.py"),
            "independent checker source changed; rerun the review")
    require(data.get("generator_sha256") == digest(root / "scripts/build_atlas_data.py"),
            "atlas generator source changed; rebuild and review")
    require(set(data.get("source_sha256", {})) == SOURCE_PATHS, "unexpected atlas source registry")
    for path, expected in data["source_sha256"].items():
        require(digest(root / path) == expected, f"atlas source changed: {path}")
    entries = data["entries"]
    entry_indices = {entry["id"]: i for i, entry in enumerate(entries)}
    review_indices = {entry["id"]: i for i, entry in enumerate(review["entries"])}
    require(len(entry_indices) == len(entries) and len(review_indices) == len(review["entries"])
            and entry_indices.keys() == review_indices.keys(), "duplicate or mismatched reviewed entries")
    require(data["carrier_summary"] == review["carrier_summary"]
            and len(entries) == review["total_embedding_orbits"]
            and len(data["abstract_types"]) == review["abstract_types_across_carriers"],
            "atlas totals differ from the review")
    shapes = {}
    for entry in entries:
        check_entry_identity(entry)
        receipt = review["entries"][review_indices[entry["id"]]]
        require(all(entry[key] == receipt[key] for key in
                    ("carrier_size", "orbit_size", "minimum_unary_operations"))
                and receipt.get("exact_operations_order_and_covers") is True,
                f"{entry['id']}: entry differs from reviewed fields")
        shape_hash = receipt.get("poset_canonical_sha256", "")
        require(re.fullmatch(r"[0-9a-f]{64}", shape_hash) is not None, "invalid reviewed shape hash")
        shape_key = "poset-v1:" + shape_hash
        previous = shapes.setdefault(entry["abstract_type"], shape_key)
        require(previous == shape_key, "abstract type groups different reviewed shapes")
    require(len(set(shapes.values())) == len(shapes), "same reviewed shape has multiple abstract types")
    return {"root": root, "data": data, "review": review,
            "atlas_sha256": atlas_hash, "review_sha256": digest(root / REVIEW_PATH),
            "entry_indices": entry_indices, "review_indices": review_indices,
            "shape_keys": shapes}


def citation(dataset, path, pointer):
    sha = dataset["atlas_sha256"] if path == ATLAS_PATH else dataset["review_sha256"]
    return {"path": path, "json_pointer": pointer, "sha256": sha}


def entry_citations(dataset, entry):
    i = dataset["entry_indices"][entry["id"]]
    j = dataset["review_indices"][entry["id"]]
    return [citation(dataset, ATLAS_PATH, f"/entries/{i}")] + [citation(dataset, ATLAS_PATH, f"/entries/{i}/{field}") for field in
            ("id", "partitions", "operations", "minimum_unary_operations")] + [
                citation(dataset, REVIEW_PATH, f"/entries/{j}")]


def unique_citations(rows):
    result = []
    seen = set()
    for item in rows:
        key = (item["path"], item["json_pointer"], item["sha256"])
        if key not in seen:
            seen.add(key)
            result.append(item)
    return result


def entry_summary(dataset, entry, full=False):
    result = dict(entry) if full else {key: entry[key] for key in
        ("id", "carrier_size", "abstract_type", "name", "minimum_unary_operations", "orbit_size")}
    result.update(shape_key=dataset["shape_keys"][entry["abstract_type"]],
                  lattice_elements=len(entry["partitions"]),
                  claim_ids=[f"construction:{entry['id']}", f"minimum:{entry['id']}"],
                  citations=entry_citations(dataset, entry))
    return result


def select_entries(dataset, carrier=None, shape=None, min_rules=None):
    require(carrier is None or type(carrier) is int and 1 <= carrier <= 4,
            "carrier must be between 1 and 4")
    require(min_rules is None or type(min_rules) is int and min_rules >= 0,
            "min-rules must be a nonnegative integer")
    entries = dataset["data"]["entries"]
    if shape is not None:
        matching_types = {entry["abstract_type"] for entry in entries
                          if shape.casefold() in (entry["name"].casefold(), entry["abstract_type"].casefold(),
                                                 dataset["shape_keys"][entry["abstract_type"]].casefold())}
        require(bool(matching_types), f"unknown shape: {shape}")
        entries = [entry for entry in entries if entry["abstract_type"] in matching_types]
    return [entry for entry in entries if (carrier is None or entry["carrier_size"] == carrier)
            and (min_rules is None or entry["minimum_unary_operations"] == min_rules)]


def query_list(dataset, carrier=None, shape=None, min_rules=None):
    return [entry_summary(dataset, entry) for entry in select_entries(dataset, carrier, shape, min_rules)]


def query_show(dataset, identifier):
    require(identifier in dataset["entry_indices"], f"unknown entry id: {identifier}")
    return [entry_summary(dataset, dataset["data"]["entries"][dataset["entry_indices"][identifier]], full=True)]


def query_compare(dataset, shape=None, carrier=None):
    groups = defaultdict(list)
    for entry in select_entries(dataset, carrier, shape):
        groups[(entry["abstract_type"], entry["carrier_size"])].append(entry)
    result = []
    for (abstract_type, n), entries in groups.items():
        minima = sorted({entry["minimum_unary_operations"] for entry in entries})
        if shape is None and len(minima) < 2:
            continue
        shape_key = dataset["shape_keys"][abstract_type]
        comparison_id = f"comparison:{shape_key}:n{n}"
        result.append({"id": comparison_id, "carrier_size": n, "abstract_type": abstract_type,
                       "shape_key": shape_key, "name": entries[0]["name"],
                       "has_different_minima": len(minima) > 1, "minimum_rule_counts": minima,
                       "entries": [entry_summary(dataset, entry) for entry in entries],
                       "claim_ids": [comparison_id],
                       "scope": "Same abstract lattice shape and same carrier size; each operation minimum belongs to its own exact relation family.",
                       "citations": unique_citations([c for entry in entries for c in entry_citations(dataset, entry)])})
    return result


def claim_record(identifier, kind, statement, citations, **fields):
    return {"id": identifier, "kind": kind, "statement": statement,
            "evidence_status": EVIDENCE_STATUS, "scope": SCOPE,
            "assumptions": ASSUMPTIONS, "limits": LIMITS, **fields,
            "citations": citations}


def make_claims(dataset):
    data = dataset["data"]
    totals = {"labeled_relation_families": sum(r["labeled_relation_families"] for r in data["carrier_summary"]),
              "embedding_orbits": len(data["entries"]), "abstract_types": len(data["abstract_types"])}
    claims = [claim_record("census:carriers-1-4", "bounded_census",
        f"Carriers of sizes 1 through 4 have {totals['labeled_relation_families']} representable labeled congruence families, {totals['embedding_orbits']} classes under object relabeling, and {totals['abstract_types']} abstract lattice shapes across the range.",
        [citation(dataset, ATLAS_PATH, "/carrier_summary"), citation(dataset, ATLAS_PATH, "/abstract_types"),
         citation(dataset, REVIEW_PATH, "/carrier_summary"), citation(dataset, REVIEW_PATH, "/total_embedding_orbits"),
         citation(dataset, REVIEW_PATH, "/abstract_types_across_carriers")], values=totals,
        scope="All full congruence relation families of unary algebras on nonempty labeled carriers of sizes 1 through 4, grouped by object relabeling and abstract lattice order isomorphism.")]
    for entry in data["entries"]:
        identity = entry["id"]
        shared = {"entry_id": identity, "carrier_size": entry["carrier_size"],
                  "shape_key": dataset["shape_keys"][entry["abstract_type"]],
                  "abstract_type": entry["abstract_type"], "name": entry["name"]}
        citations = entry_citations(dataset, entry)
        claims.append(claim_record(f"construction:{identity}", "exact_construction",
            f"The displayed operations for {identity} preserve exactly its {len(entry['partitions'])} displayed partitions.",
            citations, scope=f"The exact displayed operations and complete congruence relation family of {identity} on its fixed {entry['carrier_size']}-object carrier.", **shared))
        claims.append(claim_record(f"minimum:{identity}", "fixed_family_minimum",
            f"The minimum number of basic unary operations for the exact relation family {identity} on its {entry['carrier_size']}-object carrier is {entry['minimum_unary_operations']}.",
            citations, minimum_unary_operations=entry["minimum_unary_operations"],
            scope=f"Minimum number of basic unary operations for the exact displayed relation family {identity} on its fixed {entry['carrier_size']}-object carrier; empty operation signatures are permitted.", **shared))
    # Retain all same-carrier comparison groups, including groups with a single
    # minimum, so compare --shape always cites an existing explicit claim record.
    for shape in data["abstract_types"]:
        for comparison in query_compare(dataset, shape=shape["id"]):
            counts = comparison["minimum_rule_counts"]
            statement = (f"Among the {len(comparison['entries'])} checked {comparison['name']} embeddings on "
                         f"{comparison['carrier_size']} objects, exact-family minimum unary operation counts are {counts}.")
            claims.append(claim_record(comparison["id"], "same_shape_comparison", statement,
                comparison["citations"], shape_key=comparison["shape_key"],
                abstract_type=comparison["abstract_type"], carrier_size=comparison["carrier_size"],
                entry_ids=[entry["id"] for entry in comparison["entries"]],
                minimum_rule_counts=counts, has_different_minima=comparison["has_different_minima"],
                scope=comparison["scope"]))
    return {"schema_version": 1, "namespace": "finite-congruence-atlas/claims-v1",
            "hash_encoding": HASH_ENCODING,
            "sources": {"atlas": {"path": ATLAS_PATH, "sha256": dataset["atlas_sha256"]},
                        "review": {"path": REVIEW_PATH, "sha256": dataset["review_sha256"]},
                        "generator": {"path": GENERATOR_PATH, "sha256": digest(dataset["root"] / GENERATOR_PATH)}},
            "claims": claims}


def load_claims(dataset):
    expected = make_claims(dataset)
    require(normalized_bytes(dataset["root"] / CLAIMS_PATH) == encode(expected),
            "claim records are stale; run build-claims and review the change")
    return expected


def claim_files(claims):
    content = encode(claims)
    return {CLAIM_OUTPUTS[0]: content, CLAIM_OUTPUTS[1]: content,
            CLAIM_OUTPUTS[2]: b"window.ATLAS_CLAIMS = " + content.rstrip(b"\n") + b";\n"}


def query_claims(dataset, entry=None):
    if entry is not None:
        require(entry in dataset["entry_indices"], f"unknown entry id: {entry}")
    claims = load_claims(dataset)["claims"]
    return [claim for claim in claims if entry is None or claim.get("entry_id") == entry
            or entry in claim.get("entry_ids", [])]


class JsonParser(argparse.ArgumentParser):
    def error(self, message):
        raise ValueError(message)


def main(argv=None):
    parser = JsonParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True, parser_class=JsonParser)
    listing = sub.add_parser("list", help="List entries matching exact filters")
    listing.add_argument("--carrier", type=int)
    listing.add_argument("--shape")
    listing.add_argument("--min-rules", type=int)
    showing = sub.add_parser("show", help="Read one complete entry by its stable schema-v1 ID")
    showing.add_argument("id")
    comparison = sub.add_parser("compare", help="Compare same-carrier embeddings; default shows groups with different minima")
    comparison.add_argument("--shape")
    comparison.add_argument("--carrier", type=int)
    claiming = sub.add_parser("claims", help="Read generated claim records and their evidence")
    claiming.add_argument("--entry")
    building = sub.add_parser("build-claims", help="Regenerate deterministic claim records")
    building.add_argument("--check", action="store_true")
    try:
        args = parser.parse_args(argv)
        dataset = load_dataset()
        query = {key: value for key, value in vars(args).items() if key != "command" and value is not None}
        if args.command != "build-claims":
            load_claims(dataset)
        if args.command == "list":
            results = query_list(dataset, args.carrier, args.shape, args.min_rules)
        elif args.command == "show":
            results = query_show(dataset, args.id)
        elif args.command == "compare":
            results = query_compare(dataset, args.shape, args.carrier)
        elif args.command == "claims":
            results = query_claims(dataset, args.entry)
        else:
            claims = make_claims(dataset)
            outputs = claim_files(claims)
            if args.check:
                stale = [name for name, content in outputs.items()
                         if not (ROOT / name).is_file() or normalized_bytes(ROOT / name) != content]
                require(not stale, "claim records are missing or stale: " + ", ".join(stale))
            else:
                for name, content in outputs.items():
                    target = ROOT / name
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_bytes(content)
            results = [{"path": name, "claims": len(claims["claims"]),
                        "action": "checked" if args.check else "built", "sha256": digest(ROOT / name)}
                       for name in outputs]
        output = {"schema_version": 1, "status": "ok", "command": args.command, "query": query,
                  "dataset": {"path": ATLAS_PATH, "sha256": dataset["atlas_sha256"]},
                  "review": {"path": REVIEW_PATH, "sha256": dataset["review_sha256"]},
                  "hash_encoding": HASH_ENCODING, "scope": SCOPE, "evidence_status": EVIDENCE_STATUS,
                  "assumptions": ASSUMPTIONS, "limits": LIMITS, "results": results,
                  "citations": unique_citations([c for result in results for c in result.get("citations", [])])}
        sys.stdout.buffer.write(encode(output))
        return 0
    except (OSError, ValueError, KeyError, TypeError, IndexError) as error:
        sys.stderr.write(json.dumps({"schema_version": 1, "status": "error", "error": str(error)}) + "\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
