"""Score the small TM evidence-selection exercise; prose still needs human review.

python scripts/check_tm_retrieval.py evidence/tm-retrieval-v1/answers.json
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
DATA = "evidence/tm-atlas-v1.json"
TASKS = "benchmarks/tm-evidence-v1/tasks.json"
EXPECTED = {
    "bb2-property-separation": ("refuted", "bb2", ("halting_time", "tape", "head_position")),
    "bb4-output-separation": ("refuted", "bb4", ("tape", "head_position")),
    "tiny-property-separation": ("refuted", "tiny-stay", ("halting_time", "tape", "head_position")),
    "missing-instruction-lemma": ("supported", "tiny-stay", ("tape",)),
    "bounded-to-universal": ("unsupported", None, ()),
    "unsupported-pair": ("unsupported", None, ()),
}


def digest(path):
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def resolve(value, pointer):
    if not pointer:
        return value
    if not pointer.startswith("/"):
        raise ValueError("citation needs a JSON pointer")
    for token in pointer[1:].split("/"):
        if re.search(r"~(?![01])", token):
            raise ValueError("invalid JSON pointer escape")
        key = token.replace("~1", "/").replace("~0", "~")
        if isinstance(value, list):
            if not re.fullmatch(r"0|[1-9][0-9]*", key):
                raise ValueError("invalid JSON pointer array index")
            value = value[int(key)]
        else:
            value = value[key]
    return value


def citation_key(citation):
    return tuple(citation[key] for key in ("path", "json_pointer", "sha256"))


def check_citation(citation, root):
    relative = Path(citation["path"])
    if relative.is_absolute() or ".." in relative.parts:
        raise ValueError("citation escapes repository")
    path = (root / relative).resolve()
    if not path.is_relative_to(root.resolve()) or digest(path) != citation["sha256"]:
        raise ValueError("citation source hash mismatch")
    return resolve(json.loads(path.read_text(encoding="utf-8")), citation["json_pointer"])


def grade(document, root=ROOT):
    # Always admit the evidence through the same checked query path.
    from tm_atlas import load_dataset
    dataset = load_dataset(root=root)
    claims = {claim["id"]: claim for claim in dataset["claims"]}
    answers = document["answers"]
    if len(answers) != len(EXPECTED) or {a["id"] for a in answers} != set(EXPECTED):
        raise ValueError("answers must cover each task exactly once")
    rows = []
    for answer in answers:
        errors = []
        verdict, pair, properties = EXPECTED[answer["id"]]
        wanted = {f"tm:{pair}:{prop}:v1" for prop in properties}
        if answer.get("verdict") != verdict:
            errors.append("wrong verdict")
        if answer.get("general_equivalence") is not False:
            errors.append("general equivalence must not be asserted")
        if not isinstance(answer.get("scope"), str) or not answer["scope"].strip():
            errors.append("scope is missing")
        if not isinstance(answer.get("explanation"), str) or not answer["explanation"].strip():
            errors.append("explanation is missing")
        identifiers = answer.get("claim_ids", [])
        if len(identifiers) != len(wanted) or set(identifiers) != wanted:
            errors.append("wrong pair or property claim selection")
        expected_observations = [{"claim_id": key, **claims[key]["observation"]} for key in sorted(wanted)]
        observations = answer.get("observations", [])
        # Canonical JSON comparison also distinguishes bools from numeric values.
        if json.dumps(sorted(observations, key=lambda x: x["claim_id"]), sort_keys=True) != json.dumps(expected_observations, sort_keys=True):
            errors.append("observations differ from exact claim records")
        citations = answer.get("citations", [])
        cited = set()
        for citation in citations:
            try:
                check_citation(citation, root)
                cited.add(citation_key(citation))
            except (OSError, ValueError, KeyError, TypeError, IndexError):
                errors.append("invalid citation")
        for key in wanted:
            # Require all recorded citations for a selected claim: final-only
            # evidence must not stand in for a complete first-halt prefix.
            if not {citation_key(c) for c in claims[key]["citations"]} <= cited:
                errors.append("missing supporting citations for " + key)
        allowed = {citation_key(c) for key in wanted for c in claims[key]["citations"]}
        allowed.add((DATA, "/limits", digest(root / DATA)))
        if not cited <= allowed:
            errors.append("citation belongs to another claim or scope")
        if not wanted and (DATA, "/limits", digest(root / DATA)) not in cited:
            errors.append("scope-only answer must cite the dataset limits")
        if answer["id"] == "missing-instruction-lemma":
            lemma = answer.get("lemma", {})
            if lemma.get("name") != "TMOracle.Checks.missing_instruction":
                errors.append("wrong source lemma")
            if not isinstance(lemma.get("hypotheses"), list) or len(lemma["hypotheses"]) < 2:
                errors.append("lemma hypotheses missing")
            try:
                record = check_citation(lemma["citation"], root)
                applicable = next(item for item in claims["tm:tiny-stay:tape:v1"]["applicable_lemmas"]
                                  if item["theorem"] == "TMOracle.Checks.missing_instruction"
                                  and item["side"] == "left" and item["case_id"] == "missing-rule")
                # Its first citation identifies this exact pair/side/step
                # applicability. A whole document mentioning the name is too broad.
                if (citation_key(lemma["citation"]) != citation_key(applicable["citations"][0])
                        or not isinstance(record, dict)
                        or record.get("theorem") != applicable["theorem"]
                        or record.get("case_id") != "missing-rule"
                        or record.get("at_steps") != {"before": 0, "after": 1}):
                    errors.append("lemma citation does not identify this exact applicability")
            except (OSError, ValueError, KeyError, TypeError, IndexError):
                errors.append("invalid lemma citation")
        rows.append({"id": answer["id"], "passed": not errors, "errors": errors})
    return {"schema_version": 1, "exercise": "tm-evidence-retrieval-v1",
            "passed": all(row["passed"] for row in rows), "correct": sum(row["passed"] for row in rows),
            "total": len(rows), "results": rows,
            "sources": {name: digest(root / name) for name in (DATA, TASKS, "scripts/check_tm_retrieval.py")},
            "limits": ["Structured answer, evidence-selection, value, and citation checks only.",
                       "Free-text reasoning and lemma hypotheses require separate reviewer judgment.",
                       "One same-session smoke test is not a blinded benchmark or general capability result."]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("answers", type=Path)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    try:
        report = grade(json.loads(args.answers.read_text(encoding="utf-8")))
        report["answers_sha256"] = digest(args.answers)
        content = json.dumps(report, indent=2) + "\n"
        if args.out:
            args.out.parent.mkdir(parents=True, exist_ok=True)
            args.out.write_text(content, encoding="utf-8", newline="\n")
        print(content, end="")
        return 0 if report["passed"] else 1
    except (OSError, ValueError, KeyError, TypeError, IndexError) as exc:
        print(f"TM retrieval check failed: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
