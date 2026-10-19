"""Read exact N5, a proved N5 renaming, and one TM claim with curated bindings.

Local deterministic interface; no model calls, network, or Lean execution.
`check` validates a registered record, not an arbitrary mathematical conjecture.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys

import build_n5_context as context
import query_atlas
import tm_context
import n5_transfer
import n5_reverse_transfer

ROOT = context.ROOT
N5_CLAIM_IDS = (context.SAVED_CLAIM_ID, context.ATLAS_CLAIM_ID)
CLAIM_IDS = (*N5_CLAIM_IDS, tm_context.CLAIM_ID, n5_transfer.CLAIM_ID, n5_reverse_transfer.CLAIM_ID)
NAMESPACE = "finite-congruence-context/query-v1"
CHECK_LIMIT = ("Exact registered context matching only. This does not elaborate Lean, "
               "infer theorem applicability, verify arbitrary claims, or establish that an agent preserved meaning.")


def canonical(value):
    # JSON preserves the distinctions Python equality loses: true vs 1 vs 1.0.
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"), allow_nan=False)


def encode(value):
    return (json.dumps(value, ensure_ascii=False, indent=2, allow_nan=False) + "\n").encode("utf-8")


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def read_json(path):
    def invalid_constant(value):
        raise ValueError(f"invalid JSON constant: {value}")
    return json.loads(path.read_text(encoding="utf-8-sig"), object_pairs_hook=unique_object,
                      parse_constant=invalid_constant)


def load_context(root=ROOT):
    expected = context.build(root)
    payload = json.dumps(expected, ensure_ascii=False, indent=2) + "\n"
    for path, text in zip(context.OUTPUTS, (payload, "window.N5_CONTEXT = " + payload.rstrip() + ";\n")):
        context.require((root / path).read_text(encoding="utf-8") == text, f"stale context: {path}")
    # Return the page's saved record, after checking it against its pinned inputs.
    return read_json(root / context.OUTPUTS[0])


def source_record(root, data):
    return {"id": data["id"], "path": context.OUTPUTS[0],
            "sha256": context.digest(root / context.OUTPUTS[0]),
            "source_revision": data["source_revision"], "upstream_revision": data["upstream_revision"],
            "hash_encoding": data["hash_encoding"]}


def explain_claim(identifier, data=None, root=ROOT):
    context.require(identifier in CLAIM_IDS, f"unknown claim id: {identifier}")
    if identifier == tm_context.CLAIM_ID:
        source, claim = tm_context.explain(root)
        return explanation(source, claim)
    if identifier == n5_transfer.CLAIM_ID:
        source, claim = n5_transfer.explain(root)
        return explanation(source, claim)
    if identifier == n5_reverse_transfer.CLAIM_ID:
        source, claim = n5_reverse_transfer.explain(root)
        return explanation(source, claim)
    data = load_context(root) if data is None else data
    if identifier == context.SAVED_CLAIM_ID:
        claim = copy.deepcopy(data["claims"][0])
    else:
        dataset = query_atlas.load_dataset(root)
        claim = copy.deepcopy(next(c for c in query_atlas.load_claims(dataset)["claims"] if c["id"] == identifier))
        entry = dataset["data"]["entries"][dataset["entry_indices"][claim["entry_id"]]]
        claim.update({"construction_id": context.ATLAS_CONSTRUCTION_ID,
                      "values": {"carrier": list(range(entry["carrier_size"])), "operations": entry["operations"],
                                 "groupings": [{"partition": p} for p in entry["partitions"]]},
                      "predicate": "For every equivalence relation on {0,1,2,3}, it is preserved by both displayed operations if and only if it equals one of the displayed groupings.",
                      "applicable_lemmas": [],
                      "proof_status": "No Lean proof for these displayed operation tables is attached by this interface."})
    return explanation(source_record(root, data), claim)


def explanation(source, claim):
    return {"schema_version": 1, "namespace": NAMESPACE, "status": "ok", "command": "explain",
            "context": source, "claim": claim,
            "binding_method": "curated_exact_binding", "validation_limit": CHECK_LIMIT}


def compare(data=None, root=ROOT):
    # Each side retains its own complete evidence status and exact input tables.
    data = load_context(root) if data is None else data
    return {"schema_version": 1, "namespace": NAMESPACE, "status": "ok", "command": "compare",
            "context": source_record(root, data), "comparison": copy.deepcopy(data["atlas_relation"]),
            "claims": [explain_claim(identifier, data, root)["claim"] for identifier in N5_CLAIM_IDS],
            "validation_limit": CHECK_LIMIT}


def mismatch_paths(expected, actual, path=""):
    if type(expected) is not type(actual):
        return [path or "/"]
    if isinstance(expected, dict):
        differences = []
        for key in sorted(set(expected) | set(actual)):
            child = path + "/" + key.replace("~", "~0").replace("/", "~1")
            differences.extend([child] if key not in expected or key not in actual
                               else mismatch_paths(expected[key], actual[key], child))
        return differences
    if isinstance(expected, list):
        if len(expected) != len(actual):
            return [path or "/"]
        return [p for i, (a, b) in enumerate(zip(expected, actual))
                for p in mismatch_paths(a, b, path + f"/{i}")]
    return [] if expected == actual else [path or "/"]


def check_record(candidate, data=None, root=ROOT):
    identifier = candidate.get("claim", {}).get("id") if isinstance(candidate, dict) and isinstance(candidate.get("claim"), dict) else None
    known = isinstance(identifier, str) and identifier in CLAIM_IDS
    differences = mismatch_paths(explain_claim(identifier, data, root), candidate) if known else ["/claim/id"]
    return {"schema_version": 1, "namespace": NAMESPACE,
            "status": "supported" if not differences else "unsupported", "command": "check",
            "candidate_claim_id": identifier,
            "candidate_canonical_sha256": hashlib.sha256(canonical(candidate).encode("utf-8")).hexdigest(),
            "reason": "exact_registered_record_match" if not differences else "record_does_not_match_registered_binding",
            "mismatch_paths": differences, "validation_limit": CHECK_LIMIT}


class JsonParser(argparse.ArgumentParser):
    def error(self, message):
        raise ValueError(message)


def main(argv=None):
    parser = JsonParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True, parser_class=JsonParser)
    explaining = sub.add_parser("explain", help="Explain a registered N5, N5 renaming, or Turing claim")
    explaining.add_argument("claim_id")
    explaining.add_argument("--out", type=Path, help="Save UTF-8 JSON directly (avoids shell encoding changes)")
    sub.add_parser("compare", help="Compare saved N5 with atlas n4-E16709 under the recorded bijection")
    checking = sub.add_parser("check", help="Check an unedited or proposed explain export against known bindings")
    checking.add_argument("record", type=Path)
    try:
        args = parser.parse_args(argv)
        if args.command == "explain":
            output = explain_claim(args.claim_id)
            if args.out:
                args.out.write_bytes(encode(output))
        elif args.command == "compare":
            output = compare()
        else:
            output = check_record(read_json(args.record))
        sys.stdout.buffer.write(encode(output))
        return 1 if output["status"] == "unsupported" else 0
    except (OSError, ValueError, KeyError, TypeError, IndexError, subprocess.SubprocessError) as error:
        sys.stderr.write(json.dumps({"schema_version": 1, "status": "error", "error": str(error)}) + "\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
