"""Build a small source-linked explanation of the exact saved N5 construction.

No inference calls or Lean execution. --check verifies freshness and mathematical
correspondence; --show prints the record for local readers/agents. This sidecar
does not alter the atlas claim schema or the frozen semantic benchmark.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LOCAL_REV = "cddf9cf1c2d06df36bc516fb0b461daf6365920e"
UPSTREAM_REV = "1581d4cbdd69a0faf34b2089614fe2a814316a6a"
LOCAL = f"https://github.com/Maverick0351a/finite-congruence-checks/blob/{LOCAL_REV}/"
UPSTREAM = f"https://github.com/openai/math/blob/{UPSTREAM_REV}/"
OUTPUTS = ("space/n5-context.json", "space/n5-context-data.js")
SAVED_CLAIM_ID = "context:family-206:saved-n5:classification:v1"
SAVED_CONSTRUCTION_ID = "saved:family-206:n5:v1"
ATLAS_CLAIM_ID = "construction:n4-E16709"
ATLAS_CONSTRUCTION_ID = "atlas:n4-E16709:displayed-operations:v1"
# These normalized hashes were checked against LOCAL_REV, not derived anew on
# regeneration. A source change needs an explicit revision-and-hash review.
PINNED_SOURCES = {
    "evidence/atlas.json": "9bd8976488b269a86468dfcdb9f9ebbf246cfe8e0ffe4960f86941369919c82a",
    "evidence/atlas-review.json": "f702ebcfd8addcb12aa8cf0434c074c8869a71ae738cd996727819d8f165cd26",
    "evidence/N5-witness.json": "2b6648c6842bf0742c3029c6c0ad7c906fbdb8d281d8e830a85c51c047ef2685",
    "evidence/minimized-algebras.json": "76671ae20ad76bc2507b9e0c822bb78862abf2ff507f1a3ab7ba8b40efe85cea",
    "lean/CertificateData.lean": "1db35c8b640f0ea0d73ea12cd14e5e1b4b3eef588d3eb5ed66fbec0be37258f3",
    "lean/FiniteCongruenceChecks.lean": "845615fe7be190dc733762a1b95828cffb4e09b6d3b6b0e334211000d93422e8",
    "lean/comparator/evidence/receipt.json": "e4321a3aeed7c2c4117569959d33ad0d26abb92f1d938902f0b88423845fbb28",
    "lean/evidence/bridge-run/result.json": "29666ea7b9c28a6a643dcaeef3666f692c0e062e775d5a5eda9b5986f04883a8",
    "lean/upstream/ConcreteBridge.lean": "8a7c9d8bc83b511026efb3b6949c6265d8ba00d85ca41ef0cc7c060cc3f1b1f6",
    "lean/upstream/OAI/Algebra/Universal/Congruence.lean": "30e9201344dcf4069ca9ace276c76dc3b1507d09f0f6bfbf5a7c5d693ac9716c",
    "lean/upstream/OAI/Algebra/Universal/GraphCriterion.lean": "bd80c2bea95ee1b4f7118fc8dc272aebac7b23038ba93cdafd386dc1b688fb50",
    "space/atlas-data.json": "9bd8976488b269a86468dfcdb9f9ebbf246cfe8e0ffe4960f86941369919c82a",
}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def normalize(labels):
    seen = {}
    return tuple(seen.setdefault(v, len(seen)) for v in labels)


def failure(partition, operations):
    for i, op in enumerate(operations):
        for x, y in itertools.combinations(range(4), 2):
            if partition[x] == partition[y] and partition[op[x]] != partition[op[y]]:
                return {"operation": i, "pair": [x, y], "outputs": [op[x], op[y]]}
    return None


def build(root=ROOT):
    def read(path):
        return json.loads((root / path).read_text(encoding="utf-8"))

    for path, expected in PINNED_SOURCES.items():
        require(digest(root / path) == expected, f"pinned source mismatch: {path}")
    comparator = read("lean/comparator/evidence/receipt.json")
    require(comparator["passed"] is True, "comparator receipt did not pass")
    checks = {c["name"]: c for c in comparator["checks"]}
    for name, accepted, code in [("official", True, 0), ("sorry-control", False, 1), ("mismatch-control", False, 1)]:
        c = checks.get(name, {})
        require(c.get("passed") is True and c.get("expected_acceptance") is accepted and c.get("exit_code") == code,
                f"comparator control disagrees: {name}")

    witness = read("evidence/N5-witness.json")
    minima = read("evidence/minimized-algebras.json")
    ci, concrete = next((i, c) for i, c in enumerate(minima["certificates"]) if c["lattice"] == "N5")
    operations = concrete["selected_unary_operations"]
    require(operations == [[1, 0, 3, 2], [0, 1, 0, 1]], "saved N5 operation tables changed")
    groupings = concrete["threshold_partitions"]
    require([g["partition"] for g in groupings] ==
            [[0, 1, 2, 3], [0, 0, 1, 2], [0, 0, 1, 1], [0, 1, 0, 1], [0, 0, 0, 0]],
            "saved N5 grouping correspondence changed")
    # Enumerate partitions independently of the search/minimizer implementation.
    partitions = sorted({normalize(p) for p in itertools.product(range(4), repeat=4)})
    audit = [{"partition": list(p), "valid": failure(p, operations) is None,
              "violation": failure(p, operations)} for p in partitions]
    require(len(partitions) == 15, "partition enumeration incomplete")
    require({tuple(a["partition"]) for a in audit if a["valid"]} ==
            {tuple(g["partition"]) for g in groupings}, "congruence classification disagrees")

    # Existing Lean receipt binds the concrete tables, proof, and upstream copy.
    receipt = read("lean/evidence/bridge-run/result.json")
    proof_paths = ["evidence/N5-witness.json", "evidence/minimized-algebras.json",
                   "lean/CertificateData.lean", "lean/FiniteCongruenceChecks.lean",
                   "lean/upstream/ConcreteBridge.lean",
                   "lean/upstream/OAI/Algebra/Universal/GraphCriterion.lean",
                   "lean/upstream/OAI/Algebra/Universal/Congruence.lean"]
    require(receipt["passed"] is True, "saved Lean run did not pass")
    for path in proof_paths:
        require(digest(root / path) == receipt["source_sha256"][path], f"Lean receipt mismatch: {path}")

    def citation(path, pointer=None, line=None):
        result = {"path": path, "sha256": PINNED_SOURCES[path], "url": LOCAL + path}
        if pointer is not None:
            result["json_pointer"] = pointer
        if line is not None:
            result["line"] = line
            result["url"] += f"#L{line}"
        return result

    atlas = read("space/atlas-data.json")
    entry = next(e for e in atlas["entries"] if e["id"] == "n4-E16709")
    perm = [1, 3, 2, 0]  # old saved point -> canonical atlas point
    inv = [perm.index(i) for i in range(4)]
    transformed_parts = {normalize([g["partition"][inv[j]] for j in range(4)]) for g in groupings}
    transformed_ops = [[perm[op[inv[j]]] for j in range(4)] for op in operations]
    require(transformed_parts == {tuple(p) for p in entry["partitions"]}, "atlas family correspondence changed")
    require(sorted(transformed_ops) != sorted(entry["operations"]), "reassess operation identity boundary")
    atlas_parts = {tuple(p) for p in partitions if failure(p, entry["operations"]) is None}
    require(atlas_parts == transformed_parts, "atlas operation classification disagrees")
    grouping_map = [entry["partitions"].index(list(normalize([g["partition"][inv[j]] for j in range(4)])))
                    for g in groupings]
    def included(p, q):
        return all(p[x] != p[y] or q[x] == q[y] for x in range(4) for y in range(4))
    require(all(included(a["partition"], b["partition"]) == entry["order"][grouping_map[i]][grouping_map[j]]
                for i, a in enumerate(groupings) for j, b in enumerate(groupings)),
            "atlas order correspondence disagrees")
    review = read("evidence/atlas-review.json")
    ri, reviewed = next((i, e) for i, e in enumerate(review["entries"]) if e["id"] == entry["id"])
    require(review["passed"] is True and reviewed["exact_operations_order_and_covers"] is True,
            "atlas independent review did not pass")

    sources = [
        {"id": "scope", "title": "Family 206 · selected scope", "role": "scope_note",
         "url": UPSTREAM + "lean/docs/206.md", "description": "The selected formalization covers the colored-graph equivalence. The paper's undecidability and subgroup-interval conclusions are outside it."},
        {"id": "paper", "title": "Original paper · §1.1 and Theorem 2.2", "role": "paper_context",
         "url": UPSTREAM + "preprints/Finite-Congruence-Lattices-Characterization-and-Undecidability-September-24-2026/paper.pdf",
         "pages": [4, 7, 8], "sha256": "d26d6cd6285de4f24158d37d1583bdee84a6426190e1b6df67853128e57d80f9",
         "description": "Page 4 defines representation onto the entire congruence lattice. Pages 7–8 state and prove the graph criterion. This context page does not audit the rest of the paper."},
        {"id": "target", "title": "Comparator · target statement with sorry", "role": "target_only",
         "url": UPSTREAM + "lean/ComparatorChallenges/FiniteCongruenceGraph.lean#L57",
         "description": "This challenge supplies the target statement and definitions. Its sorry placeholder is not a completed proof."},
        {"id": "definitions", "title": "Lean · algebra, congruence, representation", "role": "formal_definition",
         **citation("lean/upstream/OAI/Algebra/Universal/Congruence.lean", line=18),
         "description": "A finite list of total finite-arity operations on a nonempty finite carrier; representation is an order isomorphism with all compatible equivalence relations."},
        {"id": "criterion", "title": "Lean · completed graph_criterion", "role": "completed_proof",
         **citation("lean/upstream/OAI/Algebra/Universal/GraphCriterion.lean", line=291),
         "upstream_url": UPSTREAM + "lean/OAI/Algebra/Universal/GraphCriterion.lean#L291",
         "description": "The completed upstream proof of Representable Lat ↔ HasGraphWitness Lat. The local copy is bound by the recorded Lean run."},
        {"id": "tables", "title": "Saved N5 · exact operation tables", "role": "construction",
         **citation("evidence/minimized-algebras.json", pointer=f"/certificates/{ci}"),
         "description": "These four point labels, two operation tables, and five threshold partitions identify the example."},
        {"id": "classification", "title": "Lean · all N5 congruences", "role": "completed_proof",
         **citation("lean/FiniteCongruenceChecks.lean", line=142),
         "description": "The finite classification, relation completeness, and all_relations theorem establish exactly the five congruences of these operations."},
        {"id": "bridge", "title": "Lean · N5 bridge to the graph criterion", "role": "completed_proof",
         **citation("lean/upstream/ConcreteBridge.lean", line=130),
         "description": "Builds the upstream congruence order isomorphism, identifies the saved colors as principal colors, and proves isGraphWitness and representable."},
        {"id": "receipt", "title": "Saved Lean build and kernel replay", "role": "verification_receipt",
         **citation("lean/evidence/bridge-run/result.json"),
         "description": "Records the earlier build, Lean kernel replay, axiom checks, and source hashes. The browser does not run Lean."},
        {"id": "comparator", "title": "Official comparator run and negative controls", "role": "verification_receipt",
         **citation("lean/comparator/evidence/receipt.json"),
         "description": "Separate acceptance record for the upstream theorem, with placeholder-proof and changed-statement rejection controls; Nanoda was disabled."},
    ]
    claims = [{
        "id": SAVED_CLAIM_ID, "kind": "exact_construction", "construction_id": SAVED_CONSTRUCTION_ID,
        "statement": "On {0,1,2,3}, f=(1,0,3,2) and g=(0,1,0,1) have exactly the five displayed congruences, ordered as N5.",
        "evidence_status": "lean_proof_with_recorded_kernel_replay",
        "scope": "The exact saved four-point, two-operation algebra and its saved coloring.",
        "assumptions": ["Both operations are total unary maps.", "A grouping is an equivalence relation preserved by both operations.", "The recorded Lean toolchain, imported definitions and declared axioms are trusted as documented in the verification receipt."],
        "limits": ["This page and its explanatory graph are not a new formal proof.", "The minimum number of operations is a separate computational claim.", "A shared N5 shape name does not transfer this proof to different operation tables.", "No undecidability, subgroup-interval, or fluid-simulation conclusion follows from this example."],
        "values": {"carrier": [0, 1, 2, 3], "operations": operations, "groupings": groupings},
        "predicate": "For every equivalence relation r on {0,1,2,3}, r is preserved by both displayed operations if and only if it equals one of the five displayed groupings. Their inclusion order is the saved N5 order, and they are pairwise distinct.",
        "applicable_lemmas": [
            {"theorem": "FiniteCongruenceChecks.N5.all_relations", "role": "complete_classification",
             "statement": "theorem all_relations (r : V → V → Prop) : IsPropCongruence op1 op2 r ↔ ∃ a, ∀ x y, r x y ↔ theta a x y = true",
             "construction_id": SAVED_CONSTRUCTION_ID, "applicability": "curated_exact_binding",
             "citations": [citation("lean/FiniteCongruenceChecks.lean", line=159)]},
            {"theorem": "FiniteCongruenceChecks.N5.order_exact", "role": "inclusion_order",
             "statement": "theorem order_exact : ∀ a b : Fin 5, le a b = true ↔ Included (theta a) (theta b)",
             "construction_id": SAVED_CONSTRUCTION_ID, "applicability": "curated_exact_binding",
             "citations": [citation("lean/FiniteCongruenceChecks.lean", line=170)]},
            {"theorem": "FiniteCongruenceChecks.N5.theta_injective", "role": "distinct_groupings",
             "statement": "theorem theta_injective : ∀ a b : Fin 5, Same (theta a) (theta b) → a = b",
             "construction_id": SAVED_CONSTRUCTION_ID, "applicability": "curated_exact_binding",
             "citations": [citation("lean/FiniteCongruenceChecks.lean", line=173)]},
        ],
        "citations": [citation("evidence/N5-witness.json"), citation("evidence/minimized-algebras.json", f"/certificates/{ci}"), citation("lean/CertificateData.lean", line=68), citation("lean/FiniteCongruenceChecks.lean", line=142), citation("lean/upstream/ConcreteBridge.lean", line=130), citation("lean/evidence/bridge-run/result.json")],
    }]
    return {
        "schema_version": 1, "id": "context:family-206:saved-n5:v1", "family": "206",
        "title": "Why these two rules make N5", "source_revision": LOCAL_REV,
        "upstream_revision": UPSTREAM_REV,
        "hash_encoding": "SHA-256 of UTF-8 source bytes with CRLF normalized to LF; paper hash uses raw PDF bytes.",
        "annotation_status": "Source-linked explanation; manually curated relationships, not an extracted proof-dependency graph.",
        "question": "Which finite lattices occur as the full congruence lattice of a nonempty finite algebra?",
        "formal_statement": "theorem graph_criterion (Lat : Type) [Fintype Lat] [Lattice Lat] [OrderBot Lat] : Representable Lat ↔ HasGraphWitness Lat",
        "claims": claims, "sources": sources,
        "atlas_relation": {"entry_id": entry["id"], "saved_to_atlas": perm,
            "id": "context:family-206:saved-n5:atlas-comparison:v1",
            "claim_ids": [SAVED_CLAIM_ID, ATLAS_CLAIM_ID],
            "construction_ids": [SAVED_CONSTRUCTION_ID, ATLAS_CONSTRUCTION_ID],
            "relation": "same_grouping_family_after_relabeling", "evidence_status": "checked_by_finite_computation",
            "saved_grouping_index_to_atlas_index": grouping_map, "inclusion_order_preserved": True,
            "partition_checks": {"partitions_per_construction": len(partitions), "valid_per_construction": 5},
            "transformed_saved_operations": transformed_ops, "atlas_operations": entry["operations"],
            "same_operation_set": False, "formal_proof_transferred": False,
            "citations": [citation("space/atlas-data.json", f"/entries/{atlas['entries'].index(entry)}"),
                          citation("evidence/atlas.json", f"/entries/{atlas['entries'].index(entry)}"),
                          citation("evidence/atlas-review.json", f"/entries/{ri}")],
            "limits": ["Operation-set inequality is for the displayed bijection only; this comparison does not decide algebra isomorphism under every permutation.",
                       "The saved Lean classification applies to the saved tables. The atlas tables retain their independently checked computational evidence; no Lean proof is transported here."],
            "explanation": "The grouping families agree after this renaming, but the displayed operation sets differ. This link is a computational correspondence, not a Lean proof of the atlas entry."},
        "color": witness["color"], "lattice": witness["lattice"],
        "partition_audit": audit,
        "connections": [
            {"source": "paper", "target": "tables", "label": "illustrated by", "kind": "illustration"},
            {"source": "tables", "target": "classification", "label": "proved using", "kind": "proof_reference"},
            {"source": "classification", "target": "bridge", "label": "used by bridge", "kind": "proof_reference"},
            {"source": "bridge", "target": "criterion", "label": "shares definitions", "kind": "definition_reference"},
            {"source": "criterion", "target": "definitions", "label": "defined using", "kind": "definition_reference"},
            {"source": "criterion", "target": "target", "label": "matches target", "kind": "comparison_reference"},
        ],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--show", action="store_true")
    args = parser.parse_args()
    payload = json.dumps(build(), ensure_ascii=False, indent=2) + "\n"
    if args.show:
        print(payload, end="")
        return
    for path, content in zip(OUTPUTS, [payload, "window.N5_CONTEXT = " + payload.rstrip() + ";\n"]):
        if args.check:
            require((ROOT / path).read_text(encoding="utf-8") == content, f"stale context: {path}")
        else:
            (ROOT / path).write_text(content, encoding="utf-8", newline="\n")
    print("N5 context checked: 15 partitions, 5 valid, exact source bindings, separate atlas operation tables.")


if __name__ == "__main__":
    main()
