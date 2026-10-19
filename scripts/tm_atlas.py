"""Build/query four pinned machine pairs from replayed, saved native traces.

This is a deterministic projection of local execution evidence. It neither runs
Lean nor proves Python/Lean equivalence. Use ``python scripts/tm_atlas.py --check``
to check every generated copy; query_atlas.py supplies the public query CLI.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
NAMESPACE = "finite-congruence-atlas/tm-pairs-v1"
HASH_ENCODING = "SHA-256 of UTF-8 file bytes with CRLF normalized to LF; no other byte changes."
RAW_HASH_ENCODING = "SHA-256 of exact file bytes; no normalization."
GENERATOR_PATH = "scripts/tm_atlas.py"
TRACE_PATH = "evidence/tm-atlas-traces-v1.json"
DATA_PATH = "evidence/tm-atlas-v1.json"
OUTPUTS = (TRACE_PATH, DATA_PATH, "space/tm-atlas-data.json", "space/tm-atlas-data.js")
RECEIPT_PATH = "evidence/tm-port-v1/summary.json"
INPUT_PATH = "evidence/tm-port-v1/inputs.jsonl"
NATIVE_PATH = "evidence/tm-port-v1/lean.jsonl"
MANIFEST_PATH = "lean/tm/source/manifest.json"
LEMMA_PATH = "lean/tm/MachineChecks.lean"
SOURCE_COMMIT = "8b8401da69a77fde583d96c8dde8f750388c37dd"
SOURCE_URL = "https://github.com/Maverick0351a/finite-congruence-checks/blob/" + SOURCE_COMMIT + "/"
PINNED_SOURCE_SHA256 = {
    INPUT_PATH: "3a9c31df1b264250126a40067f6e3db49d06be11b4ef52617bdacfaf4fee2891",
    NATIVE_PATH: "f009d43cf40e26af81d62ab20b238bac60ffff2c1f98e71b3e1176372396d9be",
    LEMMA_PATH: "e4e3e86fad42f0dedc1f6017795e406094f7190641ea4ebd1b9329e61da1e43c",
}
PROPERTIES = ("halting_time", "tape", "head_position")
EVIDENCE_STATUS = "saved_native_execution_cross_checked_with_python"
SCOPE = "Four specified machine-encoding pairs on blank input; complete saved prefixes through the first halt and one subsequent fixed configuration."
ASSUMPTIONS = [
    "The pinned extracted Machine definitions determine the step semantics: a missing instruction changes only the state to the sentinel; an explicit instruction writes and moves before halting is observed.",
    "Each tape is the entire finite support, encoded as sorted [integer position, nonzero natural symbol] pairs; every unlisted cell contains zero.",
    "Saved native transcripts, build/kernel logs, executable bytes and source hashes pass the existing local offline replay; these files are reproducibility evidence, not authenticated remote attestations.",
]
LIMITS = [
    "These are bounded observations of the specified encodings and blank input, not general machine equivalence or a proof of the Python translation.",
    "The generic Lean lemmas explain individual transition rules under their hypotheses; no Lean theorem in this artifact proves a pair's observed halting time or final tape.",
    "The bb2/bb3/bb4 labels identify these saved tables and do not assert canonical Busy Beaver encodings or optimality.",
    "Only the extracted machine definitions were checked; no Navier-Stokes or other PDE claim is validated here.",
]
# These names select frozen inputs. The complete tables remain visible in each
# record and are checked against the frozen generator by run_tm_checks.replay.
PAIR_SPECS = (
    ("tiny-stay", "One-step halt: missing instruction or explicit write", "missing-rule", "write-stay-halt"),
    ("bb2", "BB2-labeled tables: missing instruction or explicit write/right halt", "bb2-missing", "bb2-write-right-halt"),
    ("bb3", "BB3-labeled tables: missing instruction or explicit write/right halt", "bb3-missing", "bb3-write-right-halt"),
    ("bb4", "BB4-labeled tables: missing instruction or explicit write/right halt", "bb4-missing", "bb4-write-right-halt"),
)
LEMMA_NAMES = ("missing_instruction", "instruction_step", "instruction_writes", "halted_fixed")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def parse_json(text):
    def unique(items):
        result = {}
        for key, value in items:
            require(key not in result, f"duplicate JSON key: {key}")
            result[key] = value
        return result

    def reject(value):
        raise ValueError(f"nonfinite JSON value: {value}")

    return json.loads(text, object_pairs_hook=unique, parse_constant=reject)


def normalized_bytes(path):
    content = Path(path).read_bytes()
    content.decode("utf-8")
    return content.replace(b"\r\n", b"\n")


def digest(path):
    return hashlib.sha256(normalized_bytes(path)).hexdigest()


def raw_digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def encode(value):
    return (json.dumps(value, ensure_ascii=False, indent=2, allow_nan=False) + "\n").encode("utf-8")


def read_json(root, path):
    return parse_json(normalized_bytes(root / path).decode("utf-8"))


def citation(root, path, pointer):
    return {"path": path, "json_pointer": pointer, "sha256": digest(root / path)}


def replay_evidence(root):
    """Reuse the frozen offline runner in its own process; no native executable runs.

    The command/path are fixed locally, never taken from an input artifact or
    a query filter. The runner verifies all source/artifact hashes, binary bytes,
    pinned extraction, build records, 2,857 snapshots and negative controls.
    """
    completed = subprocess.run(
        [sys.executable, str(root / "scripts/run_tm_checks.py"), "replay",
         "--out", str(root / "evidence/tm-port-v1")],
        cwd=root, capture_output=True, text=True, encoding="utf-8", timeout=90,
        check=False,
    )
    require(completed.returncode == 0,
            "saved TM evidence replay failed: " + (completed.stderr or completed.stdout)[-2000:].strip())


def indexed_lines(root, path):
    result = {}
    for line, text in enumerate((root / path).read_text(encoding="utf-8").splitlines(), 1):
        record = parse_json(text)
        require(type(record) is dict and type(record.get("id")) is str,
                f"{path}:{line}: missing record id")
        require(record["id"] not in result, f"{path}:{line}: duplicate record id")
        result[record["id"]] = (record, line)
    return result


def line_source(path, line, hashes):
    return {"path": path, "line": line, "sha256": hashes[path],
            "hash_encoding": RAW_HASH_ENCODING, "source_commit": SOURCE_COMMIT,
            "url": SOURCE_URL + path + f"#L{line}"}


def make_side(case_id, label, inputs, native, hashes):
    selected = [item for key, item in inputs.items() if key.startswith(case_id + "/step-")]
    require(bool(selected), f"missing named case: {case_id}")
    selected.sort(key=lambda item: item[0]["steps"])
    machine = selected[0][0]["machine"]
    trace, locators = [], []
    for step, (case, input_line) in enumerate(selected):
        identifier = f"{case_id}/step-{step}"
        require(case["id"] == identifier and type(case["steps"]) is int
                and case["steps"] == step and case["input"] == []
                and encode(case["machine"]) == encode(machine),
                f"{case_id}: incomplete prefix, nonblank input or changing machine")
        require(identifier in native, f"missing native record: {identifier}")
        record, native_line = native[identifier]
        require(type(record["steps"]) is int and record["steps"] == step,
                f"{identifier}: native step mismatch")
        trace.append(record)
        locators.append(dict(line_source(NATIVE_PATH, native_line, hashes),
                             input_source=line_source(INPUT_PATH, input_line, hashes)))
    halts = [record["steps"] for record in trace if record["halted"] is True]
    require(bool(halts), f"{case_id}: no saved halting configuration")
    first_halt = halts[0]
    require(first_halt > 0 and len(trace) == first_halt + 2,
            f"{case_id}: expected a complete prefix and exactly one post-halt record")
    final = trace[first_halt]
    require(all(record["halted"] is False for record in trace[:first_halt]),
            f"{case_id}: invalid pre-halt flag")
    require(all(trace[-1][key] == final[key] for key in ("state", "head", "tape", "halted")),
            f"{case_id}: post-halt configuration is not fixed")
    return {"case_id": case_id, "label": label, "machine": machine, "trace": trace,
            "trace_sources": locators, "first_halt": first_halt, "final": final}


def lemma_records(root, manifest):
    lines = (root / LEMMA_PATH).read_text(encoding="utf-8").splitlines()
    records = []
    for name in LEMMA_NAMES:
        matches = [i for i, line in enumerate(lines) if line.startswith("theorem " + name + " ")]
        require(len(matches) == 1, f"ambiguous or missing source lemma: {name}")
        start = matches[0]
        end = next((i for i in range(start + 1, len(lines)) if lines[i] == ""), len(lines))
        records.append({
            "id": "tm-lemma:" + name + ":v1", "theorem": "TMOracle.Checks." + name,
            "source": {"path": LEMMA_PATH, "line": start + 1, "last_line": end,
                       "sha256": raw_digest(root / LEMMA_PATH), "hash_encoding": RAW_HASH_ENCODING,
                       "source_commit": SOURCE_COMMIT,
                       "url": SOURCE_URL + LEMMA_PATH + f"#L{start + 1}-L{end}"},
            "definitions_origin": {key: manifest[key] for key in
                ("upstream_repository", "upstream_commit", "upstream_path", "upstream_url")},
            "qualification": "Local generic transition lemma over the pinned extracted definitions; the upstream commit identifies the definitions, not authorship of this local lemma.",
            "citations": [citation(root, RECEIPT_PATH, "/source_sha256/lean~1tm~1MachineChecks.lean"),
                          citation(root, RECEIPT_PATH, "/build_commands"),
                          citation(root, MANIFEST_PATH, "/upstream_commit"),
                          citation(root, MANIFEST_PATH, "/generated_module")],
        })
    return records


def instruction(machine, config):
    symbol = dict(config["tape"]).get(config["head"], 0)
    offset = config["state"] * (machine["n_alphabet_minus_one"] + 1) + symbol
    table = machine["table"]
    return table[offset] if offset < len(table) else None


def applicability(pair, lemmas):
    result = []
    lookup = {record["theorem"].rsplit(".", 1)[-1]: record for record in lemmas}
    for side_name in ("left", "right"):
        side = pair[side_name]
        t = side["first_halt"]
        before, after = side["trace"][t - 1:t + 1]
        rule = instruction(side["machine"], before)
        require(before["halted"] is False and after["halted"] is True, "bad final transition")
        require((rule is None) == (side_name == "left"), "pair has the wrong halt mechanism")
        names = ("missing_instruction",) if rule is None else ("instruction_step", "instruction_writes")
        for name in (*names, "halted_fixed"):
            lemma = copy.deepcopy(lookup[name])
            lemma["lemma_id"] = lemma.pop("id")
            fixed = name == "halted_fixed"
            lemma.update(side=side_name, case_id=side["case_id"],
                         at_steps={"before": t if fixed else t - 1, "after": t + 1 if fixed else t})
            if fixed:
                conditions = [f"At saved step {t}, M.isHalting c = true."]
                explanation = "The next step leaves state, head and every tape cell unchanged."
            elif rule is None:
                conditions = [f"At saved step {t - 1}, M.isHalting c = false.",
                              "The table lookup M.instruction c.state (c.tape c.head) is none."]
                explanation = "This transition sets the sentinel state and preserves the head and entire tape."
            else:
                conditions = [f"At saved step {t - 1}, M.isHalting c = false.",
                              f"The table lookup is some [next state, write symbol, move] = {rule}."]
                explanation = ("The transition writes at the old head position before halting is observed."
                               if name == "instruction_writes" else
                               "The transition sets the stated state, writes at the old head, and moves by move-1.")
            lemma.update(conditions=conditions, applicability=explanation,
                         evidence_boundary="Hypothesis applicability is read from the replayed concrete snapshots and table; this pair is not instantiated as a Lean theorem.")
            result.append(lemma)
    return result


def claim_record(identifier, statement, citations, **fields):
    # Same field contract as query_atlas.claim_record, with this domain's own
    # evidence class and scope. Keep the TM builder independent of that CLI.
    return {"id": identifier, "kind": "tm_pair_observation", "statement": statement,
            "evidence_status": EVIDENCE_STATUS, "scope": SCOPE,
            "assumptions": ASSUMPTIONS, "limits": LIMITS, **fields, "citations": citations}


def expected_outputs(root):
    root = Path(root).resolve()
    # These identities were compared byte-for-byte with SOURCE_COMMIT. Changing
    # the paired encodings, native transcript or lemma source needs a new pin,
    # and semantic changes need a new namespace/claim version.
    for path, expected in PINNED_SOURCE_SHA256.items():
        require(raw_digest(root / path) == expected, f"pinned TM atlas source changed: {path}")
    replay_evidence(root)
    receipt = read_json(root, RECEIPT_PATH)
    manifest = read_json(root, MANIFEST_PATH)
    # Bind the exact bytes consumed by projection to the just-replayed receipt.
    hashes = {path: raw_digest(root / path) for path in (INPUT_PATH, NATIVE_PATH)}
    for path, value in hashes.items():
        require(value == receipt["artifacts"][Path(path).name], f"source changed after replay: {path}")
    inputs, native = indexed_lines(root, INPUT_PATH), indexed_lines(root, NATIVE_PATH)
    lemmas = lemma_records(root, manifest)
    pairs = []
    for short, name, left, right in PAIR_SPECS:
        pair = {"id": f"tm-pair:{short}:v1", "name": name, "input": [],
                "left": make_side(left, "Missing halt instruction", inputs, native, hashes),
                "right": make_side(right, "Explicit write-1/stay halt" if short == "tiny-stay"
                                   else "Explicit write-1/right halt", inputs, native, hashes),
                "claim_ids": [f"tm:{short}:{prop}:v1" for prop in PROPERTIES]}
        pair["applicable_lemmas"] = applicability(pair, lemmas)
        pairs.append(pair)
    source_paths = {"native_receipt": RECEIPT_PATH, "input_records": INPUT_PATH,
                    "native_records": NATIVE_PATH, "source_manifest": MANIFEST_PATH,
                    "lemma_source": LEMMA_PATH, "generator": GENERATOR_PATH}
    sources = {name: {"path": path, "sha256": digest(root / path)} for name, path in source_paths.items()}
    trace_data = {"schema_version": 1, "namespace": "finite-congruence-atlas/tm-traces-v1",
                  "hash_encoding": HASH_ENCODING, "sources": sources,
                  "scope": SCOPE, "assumptions": ASSUMPTIONS, "limits": LIMITS,
                  "evidence_status": EVIDENCE_STATUS, "pairs": pairs, "lemmas": lemmas}
    trace_bytes = encode(trace_data)
    trace_sha = hashlib.sha256(trace_bytes).hexdigest()

    def trace_cite(pointer):
        return {"path": TRACE_PATH, "json_pointer": pointer, "sha256": trace_sha}

    claims = []
    for i, pair in enumerate(pairs):
        short = PAIR_SPECS[i][0]
        for prop in PROPERTIES:
            suffix = {"halting_time": "first_halt", "tape": "final/tape", "head_position": "final/head"}[prop]
            values = {side: pair[side]["first_halt"] if prop == "halting_time" else
                      pair[side]["final"]["tape" if prop == "tape" else "head"] for side in ("left", "right")}
            values["equal"] = values["left"] == values["right"]
            applications = []
            cites = [trace_cite(f"/pairs/{i}/{side}/{suffix}") for side in ("left", "right")]
            cites.extend(trace_cite(f"/pairs/{i}/{side}/machine") for side in ("left", "right"))
            cites.append(trace_cite(f"/pairs/{i}/input"))
            if prop == "halting_time":
                cites.extend(trace_cite(f"/pairs/{i}/{side}/trace") for side in ("left", "right"))
            for j, record in enumerate(pair["applicable_lemmas"]):
                if prop != "tape" and record["theorem"].endswith(".instruction_writes"):
                    continue
                application_cite = trace_cite(f"/pairs/{i}/applicable_lemmas/{j}")
                applications.append(dict(record, citations=[application_cite, *record["citations"]]))
                cites.append(application_cite)
            description = {"halting_time": "first halting times", "tape": "complete final tapes",
                           "head_position": "final head positions"}[prop]
            statement = (f"For the specified {short} pair on blank input, the {description} "
                         f"{'agree' if values['equal'] else 'differ'}: missing-instruction encoding "
                         f"{values['left']}; explicit-instruction encoding {values['right']}.")
            claims.append(claim_record(f"tm:{short}:{prop}:v1", statement, cites,
                pair_id=pair["id"], property=prop, observation=values,
                scope=f"The exact displayed {short} pair on blank input; final means the first halting configuration, and the trace includes every earlier step.",
                applicable_lemmas=applications))
    data = {"schema_version": 1, "namespace": NAMESPACE, "hash_encoding": HASH_ENCODING,
            "evidence_status": EVIDENCE_STATUS, "scope": SCOPE,
            "assumptions": ASSUMPTIONS, "limits": LIMITS,
            "sources": {**sources, "trace_records": {"path": TRACE_PATH, "sha256": trace_sha}},
            "pairs": pairs, "claims": claims}
    data_bytes = encode(data)
    return data, {TRACE_PATH: trace_bytes, DATA_PATH: data_bytes,
                  "space/tm-atlas-data.json": data_bytes,
                  "space/tm-atlas-data.js": b"window.TM_ATLAS_DATA = " + data_bytes.rstrip(b"\n") + b";\n"}


def verify_outputs(root, outputs, paths=OUTPUTS):
    for path in paths:
        content = normalized_bytes(root / path)
        if path.endswith(".json"):
            parse_json(content.decode("utf-8"))
        require(content == outputs[path], f"stale or altered TM atlas artifact: {path}; rebuild with build-tm")


def build(root=ROOT, check=False):
    root = Path(root).resolve()
    data, outputs = expected_outputs(root)
    if check:
        verify_outputs(root, outputs)
    else:
        for path, content in outputs.items():
            target = root / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(content)
    return data


def load_dataset(root=ROOT):
    """Replay native evidence, rebuild expected records, and reject stale JSON."""
    root = Path(root).resolve()
    data, outputs = expected_outputs(root)
    verify_outputs(root, outputs, (TRACE_PATH, DATA_PATH))
    return data


def query(dataset, pair_id=None, property=None):
    """Select claims from a verified dataset. Unknown filters fail explicitly."""
    require(type(dataset.get("schema_version")) is int and dataset["schema_version"] == 1
            and dataset.get("namespace") == NAMESPACE,
            "unsupported TM atlas dataset")
    require(property is None or type(property) is str and property in PROPERTIES,
            f"unknown TM property: {property}")
    identifiers = {f"tm-pair:{spec[0]}:v1" for spec in PAIR_SPECS}
    require(pair_id is None or type(pair_id) is str and pair_id in identifiers,
            f"unknown TM pair: {pair_id}")
    return [copy.deepcopy(claim) for claim in dataset["claims"]
            if (pair_id is None or claim["pair_id"] == pair_id)
            and (property is None or claim["property"] == property)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        result = build(check=args.check)
    except (ValueError, OSError, KeyError, subprocess.SubprocessError) as exc:
        parser.exit(1, f"TM atlas failed: {exc}\n")
    print(json.dumps({"schema_version": 1, "checked": args.check,
                      "pairs": len(result["pairs"]), "claims": len(result["claims"])}))


if __name__ == "__main__":
    main()
