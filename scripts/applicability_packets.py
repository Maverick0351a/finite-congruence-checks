"""Prepare frozen, matched reference packets. No inference or proof execution.

Public development fixtures only. Task-specific keys stay outside the packets.
The shared broker is copied byte-for-byte from the paused pilot's pinned commit.
"""
from __future__ import annotations

import argparse
import hashlib
import html
import importlib.util
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "benchmarks/evidence-applicability-v1"
SOURCE = "5a6e46de73ed045e72149f4f912e2bbee0463086"
BROKER_SOURCE = "a16a9da5cd84c7c4b87326badeff7750a53f56f2"
BROKER_SHA256 = "38b1e2ffbc7a6bc84f82fa91897b2c20812f7b2d36d7ef174d9466a1863f5823"
BROKER = BASE / "broker.py"
REPO_URL = "https://github.com/Maverick0351a/finite-congruence-checks"
RAW = (
    "lean/CertificateData.lean", "lean/FiniteCongruenceChecks.lean",
    "lean/renaming/Renaming.lean", "lean/renaming/N5Renaming.lean",
    "lean/renaming/N5RenamingBinding.lean", "lean/tm-pair/TinyPair.lean",
    "lean/tm-pair/TinyPairBinding.lean", "lean/tm/MachineExtract.lean",
    "lean/tm/MachineChecks.lean", "lean/tm/source/Machine.definitions.txt",
    "lean/tm/source/manifest.json", "evidence/n5-renaming-v1/summary.json",
    "evidence/tm-pair-proof-v1/summary.json", "evidence/tm-port-v1/summary.json",
    "lean/lean-toolchain", "lean/tm/lean-toolchain",
)


def encoded(value):
    return json.dumps(value, ensure_ascii=False, indent=2, allow_nan=False) + "\n"


def digest(data):
    return hashlib.sha256(data.encode("utf-8") if isinstance(data, str) else data).hexdigest()


def blob(path, revision=SOURCE):
    return subprocess.check_output(["git", "show", f"{revision}:{path}"], cwd=ROOT)


def pointer(value, path):
    for part in path.split("/")[1:]:
        part = part.replace("~1", "/").replace("~0", "~")
        value = value[int(part)] if isinstance(value, list) else value[part]
    return value


def documentation(value):
    """Ordinary headings, prose fields and ordered tables; no task-aware text.

    Keep exact keys, scalar types, empty containers and order. The private-to-
    controller offset map identifies every node, including all assumptions.
    Equality of these data does not prove semantic equivalence of the prose.
    """
    chunks, spans = [], []
    size = 0

    def emit(text):
        nonlocal size
        chunks.append(text)
        size += len(text)

    def scalar(node):
        if isinstance(node, str):
            # Preserve labels such as "0" versus numeric 0, empty strings, and
            # strings that already contain JSON quotes. Ordinary prose stays
            # readable; JSON-like strings retain their explicit string syntax.
            try:
                json.loads(node)
                quote = True
            except ValueError:
                quote = not node.strip()
            if quote:
                node = json.dumps(node, ensure_ascii=False)
            return html.escape(node, quote=False).replace("\n", "<br>\n")
        return json.dumps(node, ensure_ascii=False, allow_nan=False)

    def visit(node, path, label, depth):
        begin = size
        if isinstance(node, dict):
            emit(f"{'#' * min(depth + 2, 6)} {html.escape(label)}\n\n")
            if not node:
                emit("Empty object.\n\n")
            for key, item in node.items():
                visit(item, path + "/" + key.replace("~", "~0").replace("/", "~1"), key, depth + 1)
        elif isinstance(node, list):
            emit(f"{'#' * min(depth + 2, 6)} {html.escape(label)}\n\n")
            if not node:
                emit("Empty list.\n\n")
            for i, item in enumerate(node):
                visit(item, path + "/" + str(i), f"Position {i}", depth + 1)
        else:
            emit(f"**{html.escape(label)}:** {scalar(node)}\n\n")
        spans.append({"pointer": path, "kind": type(node).__name__,
                      "span": [begin, size], "value_sha256": digest(encoded(node))})

    visit(value, "", "Reference record", 0)
    return "".join(chunks), spans


def prepare():
    inputs, inventory, records, facts = {}, [], {}, {}
    views = {"documentation": {}, "atlas": {}}

    def get(path):
        data = blob(path)
        inputs[path] = digest(data)
        return data

    def add(ref, title, path, at=None, value=None, raw=None, selection=None):
        data = get(path)
        source = {"commit": SOURCE, "path": path, "sha256": digest(data),
                  "url": f"{REPO_URL}/blob/{SOURCE}/{path}"}
        if at is not None:
            source["json_pointer"] = at
        if selection is not None:
            source["selection"] = selection
        if raw is not None:
            left = right = raw
        else:
            if value is None:
                value = pointer(json.loads(data), at or "")
            records[ref] = value
            left, facts[ref] = documentation(value)
            right = encoded(value)
        # Search is shared and independent of task, condition, or answer key.
        inventory.append({"id": ref, "title": title, "source": source,
                          "search_text": title + "\n" + (encoded(value) if raw is None else raw)})
        views["documentation"][ref] = left
        views["atlas"][ref] = right

    add("R01", "Saved N5 classification", "space/n5-context.json", "/claims/0")
    add("R02", "N5 rotation and rule permutation", "evidence/n5-renaming-v1/claim.json", "")
    add("R03", "Tiny-stay formal machine result", "evidence/tm-pair-proof-v1/claim.json", "")
    atlas = json.loads(get("evidence/atlas.json"))
    claims = json.loads(get("evidence/atlas-claims.json"))["claims"]
    for ref, entry_id in (("R04", "n4-E16403"), ("R05", "n4-E16457")):
        index = next(i for i, e in enumerate(atlas["entries"]) if e["id"] == entry_id)
        add(ref, entry_id + " C4 construction", "evidence/atlas.json", f"/entries/{index}")
        chosen = [i for i, c in enumerate(claims) if c.get("entry_id") == entry_id]
        add(ref + "C", entry_id + " claims and limits", "evidence/atlas-claims.json",
            value=[claims[i] for i in chosen], selection=[f"/claims/{i}" for i in chosen])
    traces = json.loads(get("evidence/tm-atlas-traces-v1.json"))
    # Exclude the BB3/BB4 and nonblank tasks reserved by the original pilot.
    tiny = next(p for p in traces["pairs"] if p["id"] == "tm-pair:tiny-stay:v1")
    ti = traces["pairs"].index(tiny)
    add("R06", "Tiny-stay execution trace", "evidence/tm-atlas-traces-v1.json", f"/pairs/{ti}")
    for j, path in enumerate(RAW, 10):
        add(f"S{j}", path, path, raw=get(path).decode("utf-8"))
    # Keep the six selected native/input rows verbatim and give original line IDs.
    for ref, path in (("S30", "evidence/tm-port-v1/inputs.jsonl"),
                      ("S31", "evidence/tm-port-v1/lean.jsonl")):
        rows = get(path).decode("utf-8").splitlines(keepends=True)
        numbers = sorted({(s["input_source"] if ref == "S30" else s)["line"]
                          for side in ("left", "right") for s in tiny[side]["trace_sources"]})
        add(ref, "Tiny-stay " + path, path, raw="".join(rows[i-1] for i in numbers),
            selection={"one_based_lines": numbers})
    return {"inputs": inputs, "inventory": inventory, "views": views, "records": records, "fact_map": facts}


def packet_files(data):
    files = {}
    for arm, texts in data["views"].items():
        files[f"{arm}/inventory.json"] = encoded(data["inventory"])
        files[f"{arm}/texts.json"] = encoded(texts)
    tasks = json.loads((BASE / "tasks.json").read_text(encoding="utf-8"))
    rubric = json.loads((BASE / "rubric.json").read_text(encoding="utf-8"))
    answer_format = json.loads((BASE / "answer-format.json").read_text(encoding="utf-8"))
    for task in tasks["tasks"]:
        # The controller delivers only one of these condition-independent prompts.
        # Do not mount this containing directory in an answering environment.
        files[f"prompts/{task['id']}.json"] = encoded({
            "instructions": tasks["instructions"], "assigned_task": task,
            "answer_format": answer_format,
            "rubric": {k: rubric[k] for k in ("scale", "dimensions")},
            "resources": {"tools": ["search(query)", "read(reference,page)"],
                          "source_access": "Only the supplied reference collection; source URLs are provenance.",
                          "limits": json.loads((BASE / "protocol.json").read_text(encoding="utf-8"))["candidate_limits_per_answer"]}})
    return files


def freeze(data):
    return {"schema_version": 1, "source_commit": SOURCE,
            "preparer_sha256": digest(Path(__file__).read_bytes()),
            "status": "preparation_only_not_authorized_for_model_execution",
            "hash_encoding": "SHA-256 of exact Git or generated UTF-8 bytes, no normalization",
            "source_files": data["inputs"],
            "broker_origin": {"commit": BROKER_SOURCE, "path": "scripts/semantic_broker.py",
                              "sha256": BROKER_SHA256},
            "prepared_files": {p: digest(t) for p, t in packet_files(data).items()},
            "reference_count": len(data["inventory"]),
            "formatted_records": len(data["records"]),
            "shared_raw_references": len(data["inventory"]) - len(data["records"]),
            "text_bytes": {arm: sum(len(t.encode("utf-8")) for t in texts.values())
                           for arm, texts in data["views"].items()},
            "fact_map_sha256": digest(encoded(data["fact_map"])),
            "protocol_files": {p: digest((BASE / p).read_bytes()) for p in
                               ("tasks.json", "rubric.json", "protocol.json", "answer-format.json",
                                "key-commitment.json", "reviewer-prompt.txt")}}


def check(data):
    expected = json.loads((BASE / "freeze.json").read_text(encoding="utf-8"))
    if freeze(data) != expected:
        raise ValueError("freeze differs; do not overwrite an existing version to hide drift")
    if digest(BROKER.read_bytes()) != expected["broker_origin"]["sha256"]:
        raise ValueError("shared broker differs from pinned original")
    for ref, spans in data["fact_map"].items():
        for item in spans:
            if digest(encoded(pointer(data["records"][ref], item["pointer"]))) != item["value_sha256"]:
                raise ValueError("fact map differs")
    return expected


def check_key(path, data):
    """Controller only: check integrity/coverage, never grade semantic answers."""
    raw = path.read_bytes()
    commitment = json.loads((BASE / "key-commitment.json").read_text(encoding="utf-8"))
    if len(raw) != commitment["bytes"] or digest(raw) != commitment["sha256"]:
        raise ValueError("private key does not match its public commitment")
    key = json.loads(raw)
    tasks = json.loads((BASE / "tasks.json").read_text(encoding="utf-8"))["tasks"]
    if set(key["tasks"]) != {t["id"] for t in tasks}:
        raise ValueError("private key task coverage differs")
    for task in tasks:
        entry = key["tasks"][task["id"]]
        if set(entry["required_semantic_units"]) != set(task["questions"]):
            raise ValueError("private key question coverage differs")
        if not set(entry["suggested_source_ids"]) <= set(data["views"]["atlas"]):
            raise ValueError("private key references unavailable evidence")
    return {"integrity": "pass", "task_coverage": len(tasks), "semantic_review": "not_established_by_this_check"}


def check_paths(path, data):
    """Controller-selected retrieval feasibility, not answering-agent effort."""
    integrity = check_key(path, data)
    key = json.loads(path.read_bytes())
    spec = importlib.util.spec_from_file_location("applicability_broker", BROKER)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    protocol = json.loads((BASE / "protocol.json").read_text(encoding="utf-8"))
    limits = protocol["candidate_limits_per_answer"]
    paths = []
    for task_id, task in key["tasks"].items():
        row = {"task_id": task_id, "conditions": {}}
        for arm, texts in data["views"].items():
            broker = module.Broker(data["inventory"], texts,
                                   max_calls=limits["tool_calls"],
                                   max_bytes=limits["returned_utf8_bytes"], seconds=limits["seconds"])
            for query in ("N5", "Tiny-stay"):
                broker.call("search", {"query": query})
            for ref in task["suggested_source_ids"]:
                first = broker.call("read", {"reference": ref, "page": 0})
                for page in range(1, first["pages"]):
                    broker.call("read", {"reference": ref, "page": page})
            row["conditions"][arm] = {"calls": broker.calls, "returned_utf8_bytes": broker.bytes,
                                      "transport_bytes": sum(e["transport_bytes"] for e in broker.log),
                                      "fits_proposed_limits": True}
        paths.append(row)
    return {"source_commit": SOURCE, "key_integrity": integrity,
            "sample_retrieval_paths": paths,
            "path_limit": "Controller-selected sources plus two searches; an existence check, not observed agent effort. Paths are withheld from answering packets."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("build", "check", "freeze", "check-key", "check-paths"))
    parser.add_argument("--out", type=Path)
    parser.add_argument("--key", type=Path)
    args = parser.parse_args()
    data = prepare()
    if args.action == "freeze":
        target = BASE / "freeze.json"
        with target.open("x", encoding="utf-8", newline="\n") as stream:
            stream.write(encoded(freeze(data)))
    else:
        report = check(data)
        if args.action in ("check-key", "check-paths"):
            if args.key is None:
                parser.error(f"{args.action} requires the controller's --key path")
            print(encoded((check_key if args.action == "check-key" else check_paths)(args.key, data)))
            return
        if args.action == "build":
            if args.out is None:
                parser.error("build requires --out to a new, dedicated directory")
            args.out.mkdir(parents=True, exist_ok=False)
            for relative, text in packet_files(data).items():
                target = args.out / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text(text, encoding="utf-8", newline="\n")
            # Controller metadata lives outside either condition's packet.
            (args.out / "fact-map.json").write_text(encoded(data["fact_map"]), encoding="utf-8", newline="\n")
        print(encoded({"passed": True, "references": report["reference_count"],
                       "text_bytes": report["text_bytes"], "model_sessions": 0,
                       "live_isolation": "unverified", "actual_model_tokens": None}))


if __name__ == "__main__":
    main()
