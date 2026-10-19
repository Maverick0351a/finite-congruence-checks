"""Project one existing bounded TM claim into the shared context interface.

The original atlas records and evidence stay unchanged. Loading replays saved
evidence in Python; it does not run Lean, the native binary, or a model.
"""
from __future__ import annotations

import copy
from pathlib import Path

import tm_atlas

CLAIM_ID = "tm:tiny-stay:tape:v1"
PAIR_ID = "tm-pair:tiny-stay:v1"


def explain(root):
    root = Path(root)
    dataset = tm_atlas.load_dataset(root)
    # The authoritative records and both browser copies must agree. The loader
    # has already replayed the receipt and checked the canonical trace/registry.
    content = tm_atlas.encode(dataset)
    browser_outputs = {"space/tm-atlas-data.json": content,
                       "space/tm-atlas-data.js": b"window.TM_ATLAS_DATA = " + content.rstrip(b"\n") + b";\n"}
    tm_atlas.verify_outputs(root, browser_outputs, tuple(browser_outputs))
    claim_index, saved = next((i, c) for i, c in enumerate(dataset["claims"]) if c["id"] == CLAIM_ID)
    pair_index, pair = next((i, p) for i, p in enumerate(dataset["pairs"]) if p["id"] == saved["pair_id"])
    tm_atlas.require(pair["id"] == PAIR_ID and saved["property"] == "tape", "unexpected TM context identity")
    claim = copy.deepcopy(saved)
    claim.update({
        "construction_id": pair["id"],
        "predicate": "Compare the complete finite-support tapes of these two displayed machines at their first halting configurations on the specified blank input. This is a claim about the saved runs, not all inputs or all machines.",
        "values": {"input": copy.deepcopy(pair["input"]),
                   "tape_encoding": "Sorted [integer position, nonzero natural symbol] pairs; every unlisted cell is zero.",
                   **{side: copy.deepcopy(pair[side]) for side in ("left", "right")}},
        "proof_status": "The observed tape inequality is backed by saved native execution cross-checked with Python. The attached generic Lean lemmas explain transitions under their stated hypotheses; no pair-specific Lean theorem proves this observation here.",
    })
    registry_sha = tm_atlas.digest(root / tm_atlas.DATA_PATH)
    source = {"id": pair["id"], "namespace": dataset["namespace"],
              "path": tm_atlas.DATA_PATH, "json_pointer": f"/pairs/{pair_index}", "sha256": registry_sha,
              "claim_reference": {"path": tm_atlas.DATA_PATH, "json_pointer": f"/claims/{claim_index}", "sha256": registry_sha},
              "hash_encoding": dataset["hash_encoding"], "sources": copy.deepcopy(dataset["sources"])}
    return source, claim
