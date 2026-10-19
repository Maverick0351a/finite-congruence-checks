"""Export the proof-reuse reading guide from the exact local query records.

No model or Lean execution. Both saved proof receipts are replayed before export.
The anchor records one immutable source commit and hashes of every linked file.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
import re
import subprocess

import n5_transfer as rotate
import n5_reverse_transfer as reverse
import query_context as query

ROOT = Path(__file__).resolve().parents[1]
ANCHOR = "specs/n5-reuse-source-anchor.json"
OUTPUTS = ("space/n5-reuse.json", "space/n5-reuse-data.js",
           "space/n5-reuse-reverse.json", "space/n5-reuse-rotate.json")
GITHUB = "https://github.com/Maverick0351a/finite-congruence-checks/blob/"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def linked_paths(records):
    paths = {"lean/FiniteCongruenceChecks.lean"}
    for module, record in zip((reverse, rotate), records):
        paths.update(c["path"] for c in record["claim"]["citations"])
        paths.update((module.CLAIM_PATH, module.EVIDENCE + "/summary.json"))
    return sorted(paths)


def records(root=ROOT):
    return [query.explain_claim(module.CLAIM_ID, root=root) for module in (reverse, rotate)]


def check_source_commit(root, anchor, paths):
    for path in paths:
        result = subprocess.run(["git", "show", anchor["revision"] + ":" + path], cwd=root,
                                capture_output=True, timeout=30, check=False)
        require(result.returncode == 0, "anchored Git source unavailable: " + path + "; use a full Git checkout")
        actual = hashlib.sha256(result.stdout.replace(b"\r\n", b"\n")).hexdigest()
        require(actual == anchor["files"][path], "Git source differs from anchor: " + path)


def grouping_witness(operations, partition):
    for i, operation in enumerate(operations):
        for x in range(4):
            for y in range(x + 1, 4):
                if partition[x] == partition[y] and partition[operation[x]] != partition[operation[y]]:
                    return {"rule": i, "pair": [x, y], "outputs": [operation[x], operation[y]]}
    return None


def correspondence_witness(claim, rule_map):
    forward = claim["mapping"]["object_forward_source_to_target"]
    source, target = claim["values"]["source"], claim["values"]["target"]
    for j in range(2):
        for x in range(4):
            actual = target["operations"][j][forward[x]]
            expected = forward[source["operations"][rule_map[j]][x]]
            if actual != expected:
                return {"rule": j, "source_object": x, "target_object": forward[x],
                        "target_output": actual, "expected_output": expected}
    return None


def build(root=ROOT):
    original_records = records(root)
    anchor = query.read_json(root / ANCHOR)
    require(type(anchor.get("revision")) is str and re.fullmatch(r"[0-9a-f]{40}", anchor["revision"]),
            "source anchor must identify an immutable Git commit")
    paths = linked_paths(original_records)
    require(set(anchor["files"]) == set(paths), "source anchor coverage differs")
    for path in paths:
        require(anchor["files"][path] == rotate.digest(root / path), "linked source changed: " + path)
    check_source_commit(root, anchor, paths)
    base = GITHUB + anchor["revision"] + "/"
    transfers = []
    for module, key, title, description, record in zip(
        (reverse, rotate), ("reverse", "rotate"),
        ("Reverse the labels; keep the rule names", "Rotate the labels; swap the rule names"),
        ("Exchange 0 with 3 and 1 with 2. Both rules keep their names and are transported with the objects.",
         "Send 0 to 1, 1 to 2, 2 to 3, and 3 to 0. Target f corresponds to source g, and target g to source f."),
        original_records,
    ):
        theorem_path = next(c["path"] for c in record["claim"]["citations"]
                            if c["path"].startswith(module.PROJECT + "/")
                            and c["path"].endswith(".lean")
                            and "Binding" not in c["path"] and not c["path"].endswith("/Renaming.lean"))
        transfers.append({"key": key, "title": title, "description": description, "record": record,
                          "download": "n5-reuse-" + key + ".json",
                          "links": {"construction": base + "lean/FiniteCongruenceChecks.lean",
                                    "claim": base + module.CLAIM_PATH, "proof": base + theorem_path,
                                    "receipt": base + module.EVIDENCE + "/summary.json"}})
    reverse_claim, rotate_claim = [r["claim"] for r in original_records]
    partition = [0, 1, 2, 2]
    old_operations = reverse_claim["values"]["source"]["operations"]
    bad_rule_map = [0, 1]
    bad_evidence = copy.deepcopy(original_records[0])
    bad_evidence["claim"]["theorem"] = "FiniteCongruenceChecks.B3.all_relations"
    unsupported = query.check_record(bad_evidence, root=root)
    require(unsupported["status"] == "unsupported", "unrelated theorem was admitted")
    return {"schema_version": 1, "id": "context:family-206:proof-reuse-demo:v1",
            "source_revision": anchor["revision"], "default_transfer": "reverse", "transfers": transfers,
            "controls": [
                {"id": "grouping-failure", "title": "Rename only the grouping", "category": "grouping_failure",
                 "transfer": "reverse", "partition": partition, "operations": old_operations,
                 "witness": grouping_witness(old_operations, partition),
                 "explanation": "Objects 2 and 3 are together, but the original g sends them to 0 and 1, which are separate. This particular grouping fails for the unchanged rules."},
                {"id": "correspondence-failure", "title": "Forget the rule-name swap", "category": "correspondence_failure",
                 "transfer": "rotate", "rule_map": bad_rule_map,
                 "witness": correspondence_witness(rotate_claim, bad_rule_map), "family_unchanged": True,
                 "explanation": "The target rules and its five groupings stay unchanged. Declaring the wrong rule correspondence breaks the mapping equation; it does not make the target cease to have N5 groupings."},
                {"id": "unsupported-evidence", "title": "Cite the B3 theorem instead", "category": "unsupported_evidence",
                 "transfer": "reverse", "proposed_theorem": bad_evidence["claim"]["theorem"],
                 "validation": unsupported,
                 "explanation": "The construction is unchanged, but this registered claim is not supported by the substituted B3 theorem. Record rejection alone does not show the mathematical conclusion is false."},
            ],
            "limits": ["These controls are deliberately constructed examples, not observed agent mistakes.",
                       "The browser displays finite calculations and saved evidence; it does not run Lean.",
                       "The local query checker matches exact registered records; it is not a general theorem-applicability decision procedure.",
                       "No improvement in agent reasoning is established by this demo."]}


def output_texts(data):
    payload = query.encode(data).decode("utf-8")
    return (payload, "window.N5_REUSE = " + payload.rstrip() + ";\n",
            *(query.encode(t["record"]).decode("utf-8") for t in data["transfers"]))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    data = build()
    for name, text in zip(OUTPUTS, output_texts(data)):
        path = ROOT / name
        if args.check:
            require(path.read_text(encoding="utf-8") == text, "stale demo data: " + name)
        else:
            path.write_bytes(text.encode("utf-8"))
    print("N5 proof reuse: two exact query records, three deliberate controls, and pinned source links checked.")


if __name__ == "__main__":
    main()
