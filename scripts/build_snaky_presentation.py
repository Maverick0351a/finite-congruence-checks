"""Export a checked example play and exact claim with immutable evidence links.

Saved evidence is replayed; this command does not execute Lean or a model.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess

import check_snaky_play as play_check
import query_context as query
import snaky_proof as proof

ROOT = Path(__file__).resolve().parents[1]
PLAY = "evidence/snaky-play-v1/example.json"
ANCHOR = "specs/snaky-play-source-anchor.json"
OUTPUTS = ("space/snaky-play.json", "space/snaky-play-data.js")
GITHUB = "https://github.com/Maverick0351a/finite-congruence-checks/blob/"


def inputs(root=ROOT):
    receipt = proof.replay(root=root)
    record = query.explain_claim(proof.CLAIM_ID, root=root)
    proof.require(query.check_record(record, root=root)["status"] == "supported", "claim query differs")
    play = json.loads((root / PLAY).read_text(encoding="utf-8"))
    play_check.validate(play, root=root)
    proof.require(play["sources"]["root_claim_id"] == proof.CLAIM_ID, "play refers to another claim")
    proof.require(play["board"]["cells"] == record["claim"]["values"]["envelope"], "play board differs from proved envelope")
    paths = set(receipt["source_hashes"])
    paths.update(proof.RECEIPT + "/" + name for name in receipt["artifacts"])
    paths.update((proof.RECEIPT + "/summary.json", proof.finite.OUTPUT, PLAY,
                  "scripts/build_snaky_play.py", "scripts/check_snaky_play.py"))
    return play, record, sorted(paths)


def check_anchor(root, anchor, paths):
    proof.require(type(anchor) is dict and set(anchor) == {"schema_version", "revision", "files"}, "invalid source anchor fields")
    proof.require(type(anchor["schema_version"]) is int and anchor["schema_version"] == 1, "invalid source anchor version")
    proof.require(type(anchor.get("revision")) is str and re.fullmatch(r"[0-9a-f]{40}", anchor["revision"]), "invalid source revision")
    proof.require(type(anchor["files"]) is dict and all(type(value) is str and re.fullmatch(r"[0-9a-f]{64}", value) for value in anchor["files"].values()), "invalid source anchor hashes")
    proof.require(set(anchor["files"]) == set(paths), "source anchor coverage differs")
    for path in paths:
        proof.require(proof.digest(root / path) == anchor["files"][path], "local anchored source changed: " + path)
        result = subprocess.run(["git", "show", anchor["revision"] + ":" + path], cwd=root,
                                capture_output=True, timeout=30)
        proof.require(result.returncode == 0, "anchored Git file unavailable: " + path + "; use a full checkout")
        proof.require(proof.finite.raw_digest(result.stdout.replace(b"\r\n", b"\n")) == anchor["files"][path], "Git bytes differ: " + path)


def build(root=ROOT):
    play, record, paths = inputs(root)
    anchor = proof.read(root / ANCHOR)
    check_anchor(root, anchor, paths)
    base = GITHUB + anchor["revision"] + "/"
    evidence = [
        {"title": "The exact recorded execution", "description": "All chosen moves, complete ownership sets, certificate placements and the six-cell winning witness. The independent checker replays this one branch.", "path": PLAY},
        {"title": "The formal strategy guarantee", "description": "The Lean theorem covers every legal reply on the exact finite board, within 21 Maker claims. The source paper already states this finite-board result.", "path": proof.PROJECT + "/SnakyFinite.lean"},
        {"title": "The claim and its verification", "description": "The receipt records the build, kernel replay, allowed axioms and deliberate mismatched-claim rejections. Offline receipt replay is not a new proof execution.", "path": proof.RECEIPT + "/summary.json"},
    ]
    for entry in evidence:
        entry.update(url=base + entry["path"], sha256=anchor["files"][entry["path"]])
    return {"schema_version": 1, "id": "context:family-187:snaky:illustrative-play:v1",
            "source_revision": anchor["revision"], "play": play, "claim_record": record,
            "evidence": evidence,
            "commands": ["python scripts/check_snaky_play.py",
                         "python scripts/query_context.py explain " + proof.CLAIM_ID + " --out snaky.json",
                         "python scripts/query_context.py check snaky.json",
                         "python scripts/snaky_proof.py run --out runs/snaky-fresh"]}


def output_texts(data):
    payload = proof.encode(data).decode()
    return payload, "window.SNAKY_PLAY_DATA = " + payload.rstrip() + ";\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--anchor", help="Commit containing every checked proof and play input")
    args = parser.parse_args()
    if args.anchor:
        proof.require(not args.check, "anchor creation and checking are separate operations")
        _, _, paths = inputs()
        anchor = {"schema_version": 1, "revision": args.anchor,
                  "files": {path: proof.digest(ROOT / path) for path in paths}}
        check_anchor(ROOT, anchor, paths)
        (ROOT / ANCHOR).write_bytes(proof.encode(anchor))
    data = build()
    for path, text in zip(OUTPUTS, output_texts(data)):
        if args.check:
            proof.require((ROOT / path).read_text(encoding="utf-8") == text, "stale presentation: " + path)
        else:
            (ROOT / path).write_bytes(text.encode())
    print("PASS: illustrative Snaky play, exact claim, and immutable evidence links agree")


if __name__ == "__main__":
    main()
