"""Build matched reference views from a pinned Git object database; never run a model.

The packet manifest is a controller artifact, not an answering capability.
Raw source/receipt/input/trace units have identical bytes in both conditions.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import html
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
COMMIT = "cddf9cf1c2d06df36bc516fb0b461daf6365920e"
REGISTRIES = ("evidence/atlas.json", "evidence/atlas-claims.json",
              "evidence/tm-atlas-v1.json", "evidence/tm-atlas-traces-v1.json")
SHARED = (
    "evidence/atlas-review.json", "evidence/grouping-checker-v1/summary.json",
    "evidence/tm-port-v1/summary.json", "evidence/tm-port-v1/build/axioms.log",
    "evidence/N5-witness.json", "evidence/minimized-algebras.json",
    "evidence/search-results.json", "lean/evidence/bridge-run/result.json",
    "lean/CertificateData.lean", "lean/FiniteCongruenceChecks.lean",
    "lean/GroupingChecker.lean", "lean/upstream/ConcreteBridge.lean",
    "lean/upstream/OAI/Algebra/Universal/Congruence.lean",
    "lean/upstream/OAI/Algebra/Universal/GraphCriterion.lean",
    "lean/tm/MachineExtract.lean", "lean/tm/MachineChecks.lean",
    "lean/tm/source/manifest.json", "lean/tm/source/Machine.definitions.txt",
    "lean/tm/source/NavierStokesAlternating.lean", "lean/tm/lean-toolchain",
    "lean/tm/lake-manifest.json", "specs/unary-grouping-v1.json",
)
JSONL = ("evidence/tm-port-v1/inputs.jsonl", "evidence/tm-port-v1/lean.jsonl")


def encoded(value):
    return json.dumps(value, ensure_ascii=False, separators=(",", ":"))


def digest(value):
    if isinstance(value, str):
        value = value.encode("utf-8")
    return hashlib.sha256(value).hexdigest()


def blob(path):
    return subprocess.check_output(["git", "show", f"{COMMIT}:{path}"], cwd=ROOT)


def pointer_key(key):
    return str(key).replace("~", "~0").replace("/", "~1")


def leaves(value, path=""):
    """Include container shape, null, and empty values, not merely scalar strings."""
    if isinstance(value, dict):
        yield path, "object", list(value)
        for k, v in value.items():
            yield from leaves(v, path + "/" + pointer_key(k))
    elif isinstance(value, list):
        yield path, "array", len(value)
        for i, v in enumerate(value):
            yield from leaves(v, path + "/" + str(i))
    else:
        yield path, type(value).__name__, value


def documentation(value):
    """Deterministic reference documentation, with an offset map for every value.

    No task-aware paraphrase or generated conclusion. Keys are preserved exactly:
    some keys are file identities whose underscores and casing carry meaning.
    """
    chunks, spans = [], []
    size = 0

    def emit(text):
        nonlocal size
        start = size
        chunks.append(text)
        size += len(text)
        return [start, size]

    def visit(node, path, label, depth):
        begin = size
        heading = "#" * min(depth + 2, 6)
        if isinstance(node, dict):
            emit(f"{heading} {label}\n\n")
            if not node:
                emit("Empty object.\n\n")
            for key, item in node.items():
                visit(item, path + "/" + pointer_key(key), html.escape(key, quote=False), depth + 1)
        elif isinstance(node, list):
            emit(f"{heading} {label}\n\n")
            if not node:
                emit("Empty list.\n\n")
            elif all(not isinstance(v, (dict, list)) for v in node):
                # Explicit zero-based positions preserve label/table order.
                for i, item in enumerate(node):
                    start = size
                    emit(f"- Position {i}: {scalar(item)}\n")
                    spans.append({"pointer": path + "/" + str(i), "span": [start, size], "value": item})
                emit("\n")
            else:
                for i, item in enumerate(node):
                    visit(item, path + "/" + str(i), f"Position {i}", depth + 1)
        else:
            emit(f"**{label}:** {scalar(node)}\n\n")
        spans.append({"pointer": path, "span": [begin, size], "value_sha256": digest(encoded(node))})

    def scalar(node):
        if isinstance(node, str):
            return html.escape(node, quote=False).replace("\n", "<br>\n")
        return encoded(node)

    visit(value, "", "Record", 0)
    return "".join(chunks), spans


def factor_trace(side):
    """Losslessly factor repeated provenance; retain every row and line/link."""
    result = copy.deepcopy(side)
    sources = result.pop("trace_sources")
    bases, rows = [], []
    for source in sources:
        source = copy.deepcopy(source)
        inp = source.pop("input_source")
        row = {}
        for name, item in (("trace", source), ("input", inp)):
            line = item.pop("line")
            url = item.pop("url")
            # Factor only exact #L<number> links; fail closed on a different form.
            suffix = "#L" + str(line)
            if not url.endswith(suffix):
                raise ValueError("unexpected trace source URL")
            item["url_prefix"] = url[:-len(suffix)]
            if item not in bases:
                bases.append(item)
            row[name] = {"source": bases.index(item), "line": line}
        rows.append(row)
    result["trace_sources"] = {
        "representation": "For each row in order, select sources[source]; replace url_prefix with url_prefix + '#L' + line and restore line. Reassemble trace and input_source. No row is omitted.",
        "sources": bases, "rows": rows,
    }
    if expand_trace(result) != side:
        raise ValueError("trace provenance did not round trip")
    return result


def expand_trace(side):
    result = copy.deepcopy(side)
    factored = result.pop("trace_sources")
    sources = []
    for row in factored["rows"]:
        parts = {}
        for name in ("trace", "input"):
            item = copy.deepcopy(factored["sources"][row[name]["source"]])
            item["line"] = row[name]["line"]
            item["url"] = item.pop("url_prefix") + "#L" + str(item["line"])
            parts[name] = item
        parts["trace"]["input_source"] = parts["input"]
        sources.append(parts["trace"])
    result["trace_sources"] = sources
    return result


def build():
    units, fact_map, inputs = [], {}, {}

    def get(path):
        raw = blob(path)
        inputs[path] = {"sha256": digest(raw), "bytes": len(raw)}
        return raw

    def add(ref, title, path, pointer, value=None, raw=None, context=None, original=None):
        source = {"commit": COMMIT, "path": path,
                  "file_sha256": inputs[path]["sha256"], "hash_encoding": "exact Git blob bytes",
                  "url": f"https://github.com/Maverick0351a/finite-congruence-checks/blob/{COMMIT}/{path}"}
        if pointer.startswith("line:"):
            source["line"] = int(pointer.split(":")[1])
            source["url"] += "#L" + str(source["line"])
        elif raw is None or pointer:
            source["json_pointer"] = pointer
        payload = {"source": source, "context": context or {}, "record": value}
        if raw is None:
            atlas = encoded(payload) + "\n"
            docs, spans = documentation(payload)
            # Source leaf identity and document spans are controller-only audit data.
            fact_map[ref] = {"source": source, "original": list(leaves(original if original is not None else value)),
                             "rendered": list(leaves(payload)), "documentation_spans": spans,
                             "expanded_equals_source": original is None or expand_trace(value) == original}
        else:
            atlas = docs = raw.decode("utf-8")
            fact_map[ref] = {"source": source, "raw_sha256": digest(raw), "byte_identical": True}
        units.append({"id": ref, "title": title, "source": source,
                      "search_text": title + " " + encoded(value) if value is not None else title + " " + docs,
                      "granularity": "row" if pointer.startswith("line:") else "record",
                      "documentation": docs, "atlas": atlas, "shared_raw": raw is not None})

    group = json.loads(get(REGISTRIES[0]))
    context = {k: v for k, v in group.items() if k not in ("entries", "abstract_types", "carrier_summary")}
    add("grouping-context", "Grouping collection scope and encoding", REGISTRIES[0], "", value={k: v for k,v in group.items() if k != "entries"})
    for i, entry in enumerate(group["entries"]):
        add("grouping-" + entry["id"], "Grouping construction " + entry["id"] + " " + entry["name"], REGISTRIES[0], f"/entries/{i}", entry, context=context)
    claims = json.loads(get(REGISTRIES[1]))
    for i, claim in enumerate(claims["claims"]):
        add("grouping-claim-" + str(i), "Grouping claim " + claim["id"], REGISTRIES[1], f"/claims/{i}", claim,
            context={k: v for k,v in claims.items() if k != "claims"})
    # Both registries carry identical pairs. Compare the complete originals,
    # retain both provenance locations in the audit, serve each pair once.
    tm = json.loads(get(REGISTRIES[2]))
    trace = json.loads(get(REGISTRIES[3]))
    if tm["pairs"] != trace["pairs"]:
        raise ValueError("TM registry pair copies differ")
    for path, registry in ((REGISTRIES[2], tm), (REGISTRIES[3], trace)):
        add("tm-context-" + ("pairs" if path == REGISTRIES[2] else "traces"), "Turing collection " + path,
            path, "", {k:v for k,v in registry.items() if k not in ("pairs", "claims", "lemmas")})
    tmcontext = {k:v for k,v in tm.items() if k not in ("pairs", "claims", "sources")}
    for i, pair in enumerate(tm["pairs"]):
        ref = "tm-pair-" + str(i)
        meta = {k:v for k,v in pair.items() if k not in ("left", "right")}
        meta["left_reference"] = ref + "-left"
        meta["right_reference"] = ref + "-right"
        add(ref, "Machine pair " + pair["id"], REGISTRIES[2], f"/pairs/{i}", meta, context=tmcontext)
        fact_map[ref]["reconstruction"] = {
            "origins": [{"path":p,"pointer":f"/pairs/{i}"} for p in REGISTRIES[2:]],
            "rule":"Remove left_reference and right_reference; restore left/right from the expanded side prefix records.",
            "source_value_sha256":digest(encoded(pair)),
        }
        for side in ("left", "right"):
            record = factor_trace(pair[side])
            # Execution prefixes are raw shared evidence, identical in both arms.
            raw = (encoded({"context":tmcontext,"pair_id":pair["id"],"input":pair["input"],"record":record}) + "\n").encode()
            add(ref + "-" + side, "Machine prefix " + pair["id"] + " " + side + " " + pair[side]["case_id"],
                REGISTRIES[3], f"/pairs/{i}/{side}", value=record, raw=raw)
            fact_map[ref + "-" + side]["lossless_provenance_factoring"] = True
            fact_map[ref + "-" + side]["expanded_equals_source"] = expand_trace(record) == pair[side]
    for i, claim in enumerate(tm["claims"]):
        add("tm-claim-" + str(i), "Machine property claim " + claim["id"], REGISTRIES[2], f"/claims/{i}", claim, context=tmcontext)
    for i, lemma in enumerate(trace["lemmas"]):
        add("tm-lemma-" + str(i), "Machine lemma " + lemma["id"], REGISTRIES[3], f"/lemmas/{i}", lemma, context=tmcontext)
    for i, path in enumerate(SHARED):
        add("source-" + str(i), "Source " + path, path, "", raw=get(path))
    for i, path in enumerate(JSONL):
        raw = get(path)
        for line, record in enumerate(raw.splitlines(keepends=True), 1):
            case = json.loads(record)["id"]
            add(f"execution-{i}-{line}", f"Saved {path} line {line} {case}", path, f"line:{line}", raw=record)
    if len({u["id"] for u in units}) != len(units):
        raise ValueError("duplicate reference ID")
    return units, fact_map, inputs


def write_packets(directory):
    directory.mkdir(parents=True, exist_ok=False)
    units, fact_map, inputs = build()
    files = {}
    for name, value in (("inventory.json", [{k:v for k,v in u.items() if k not in ("documentation", "atlas")} for u in units]),
                        ("documentation.json", {u["id"]: u["documentation"] for u in units}),
                        ("atlas.json", {u["id"]:u["atlas"] for u in units}), ("fact-map.json", fact_map)):
        raw = (encoded(value) + "\n").encode()
        (directory/name).write_bytes(raw)
        files[name] = {"sha256":digest(raw), "bytes":len(raw)}
    manifest = {"status":"prepared_pending_independent_review_and_runner_preflight", "atlas_commit":COMMIT,
                "units":len(units), "shared_raw_units":sum(u["shared_raw"] for u in units),
                "inputs":inputs, "files":files, "renderer_sha256":digest(Path(__file__).read_bytes().replace(b"\r\n",b"\n")),
                "excluded":"All tasks, keys, old answers, retrieval reviews, protocol and preparation files.",
                "limits":"Mechanical value/span parity and lossless factoring do not establish semantic preservation."}
    (directory/"manifest.json").write_text(json.dumps(manifest,indent=2)+"\n",encoding="utf-8",newline="\n")
    return manifest


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(write_packets(args.out), indent=2))
