window.N5_CONTEXT = {
  "schema_version": 1,
  "id": "context:family-206:saved-n5:v1",
  "family": "206",
  "title": "Why these two rules make N5",
  "source_revision": "cddf9cf1c2d06df36bc516fb0b461daf6365920e",
  "upstream_revision": "1581d4cbdd69a0faf34b2089614fe2a814316a6a",
  "hash_encoding": "SHA-256 of UTF-8 source bytes with CRLF normalized to LF; paper hash uses raw PDF bytes.",
  "annotation_status": "Source-linked explanation; manually curated relationships, not an extracted proof-dependency graph.",
  "question": "Which finite lattices occur as the full congruence lattice of a nonempty finite algebra?",
  "formal_statement": "theorem graph_criterion (Lat : Type) [Fintype Lat] [Lattice Lat] [OrderBot Lat] : Representable Lat ↔ HasGraphWitness Lat",
  "claims": [
    {
      "id": "context:family-206:saved-n5:classification:v1",
      "kind": "exact_construction",
      "construction_id": "saved:family-206:n5:v1",
      "statement": "On {0,1,2,3}, f=(1,0,3,2) and g=(0,1,0,1) have exactly the five displayed congruences, ordered as N5.",
      "evidence_status": "lean_proof_with_recorded_kernel_replay",
      "scope": "The exact saved four-point, two-operation algebra and its saved coloring.",
      "assumptions": [
        "Both operations are total unary maps.",
        "A grouping is an equivalence relation preserved by both operations.",
        "The recorded Lean toolchain, imported definitions and declared axioms are trusted as documented in the verification receipt."
      ],
      "limits": [
        "This page and its explanatory graph are not a new formal proof.",
        "The minimum number of operations is a separate computational claim.",
        "A shared N5 shape name does not transfer this proof to different operation tables.",
        "No undecidability, subgroup-interval, or fluid-simulation conclusion follows from this example."
      ],
      "values": {
        "carrier": [
          0,
          1,
          2,
          3
        ],
        "operations": [
          [
            1,
            0,
            3,
            2
          ],
          [
            0,
            1,
            0,
            1
          ]
        ],
        "groupings": [
          {
            "element": "0",
            "partition": [
              0,
              1,
              2,
              3
            ]
          },
          {
            "element": "a",
            "partition": [
              0,
              0,
              1,
              2
            ]
          },
          {
            "element": "b",
            "partition": [
              0,
              0,
              1,
              1
            ]
          },
          {
            "element": "c",
            "partition": [
              0,
              1,
              0,
              1
            ]
          },
          {
            "element": "1",
            "partition": [
              0,
              0,
              0,
              0
            ]
          }
        ]
      },
      "predicate": "For every equivalence relation r on {0,1,2,3}, r is preserved by both displayed operations if and only if it equals one of the five displayed groupings. Their inclusion order is the saved N5 order, and they are pairwise distinct.",
      "applicable_lemmas": [
        {
          "theorem": "FiniteCongruenceChecks.N5.all_relations",
          "role": "complete_classification",
          "statement": "theorem all_relations (r : V → V → Prop) : IsPropCongruence op1 op2 r ↔ ∃ a, ∀ x y, r x y ↔ theta a x y = true",
          "construction_id": "saved:family-206:n5:v1",
          "applicability": "curated_exact_binding",
          "citations": [
            {
              "path": "lean/FiniteCongruenceChecks.lean",
              "sha256": "845615fe7be190dc733762a1b95828cffb4e09b6d3b6b0e334211000d93422e8",
              "url": "https://github.com/Maverick0351a/finite-congruence-checks/blob/cddf9cf1c2d06df36bc516fb0b461daf6365920e/lean/FiniteCongruenceChecks.lean#L159",
              "line": 159
            }
          ]
        },
        {
          "theorem": "FiniteCongruenceChecks.N5.order_exact",
          "role": "inclusion_order",
          "statement": "theorem order_exact : ∀ a b : Fin 5, le a b = true ↔ Included (theta a) (theta b)",
          "construction_id": "saved:family-206:n5:v1",
          "applicability": "curated_exact_binding",
          "citations": [
            {
              "path": "lean/FiniteCongruenceChecks.lean",
              "sha256": "845615fe7be190dc733762a1b95828cffb4e09b6d3b6b0e334211000d93422e8",
              "url": "https://github.com/Maverick0351a/finite-congruence-checks/blob/cddf9cf1c2d06df36bc516fb0b461daf6365920e/lean/FiniteCongruenceChecks.lean#L170",
              "line": 170
            }
          ]
        },
        {
          "theorem": "FiniteCongruenceChecks.N5.theta_injective",
          "role": "distinct_groupings",
          "statement": "theorem theta_injective : ∀ a b : Fin 5, Same (theta a) (theta b) → a = b",
          "construction_id": "saved:family-206:n5:v1",
          "applicability": "curated_exact_binding",
          "citations": [
            {
              "path": "lean/FiniteCongruenceChecks.lean",
              "sha256": "845615fe7be190dc733762a1b95828cffb4e09b6d3b6b0e334211000d93422e8",
              "url": "https://github.com/Maverick0351a/finite-congruence-checks/blob/cddf9cf1c2d06df36bc516fb0b461daf6365920e/lean/FiniteCongruenceChecks.lean#L173",
              "line": 173
            }
          ]
        }
      ],
      "citations": [
        {
          "path": "evidence/N5-witness.json",
          "sha256": "2b6648c6842bf0742c3029c6c0ad7c906fbdb8d281d8e830a85c51c047ef2685",
          "url": "https://github.com/Maverick0351a/finite-congruence-checks/blob/cddf9cf1c2d06df36bc516fb0b461daf6365920e/evidence/N5-witness.json"
        },
        {
          "path": "evidence/minimized-algebras.json",
          "sha256": "76671ae20ad76bc2507b9e0c822bb78862abf2ff507f1a3ab7ba8b40efe85cea",
          "url": "https://github.com/Maverick0351a/finite-congruence-checks/blob/cddf9cf1c2d06df36bc516fb0b461daf6365920e/evidence/minimized-algebras.json",
          "json_pointer": "/certificates/5"
        },
        {
          "path": "lean/CertificateData.lean",
          "sha256": "1db35c8b640f0ea0d73ea12cd14e5e1b4b3eef588d3eb5ed66fbec0be37258f3",
          "url": "https://github.com/Maverick0351a/finite-congruence-checks/blob/cddf9cf1c2d06df36bc516fb0b461daf6365920e/lean/CertificateData.lean#L68",
          "line": 68
        },
        {
          "path": "lean/FiniteCongruenceChecks.lean",
          "sha256": "845615fe7be190dc733762a1b95828cffb4e09b6d3b6b0e334211000d93422e8",
          "url": "https://github.com/Maverick0351a/finite-congruence-checks/blob/cddf9cf1c2d06df36bc516fb0b461daf6365920e/lean/FiniteCongruenceChecks.lean#L142",
          "line": 142
        },
        {
          "path": "lean/upstream/ConcreteBridge.lean",
          "sha256": "8a7c9d8bc83b511026efb3b6949c6265d8ba00d85ca41ef0cc7c060cc3f1b1f6",
          "url": "https://github.com/Maverick0351a/finite-congruence-checks/blob/cddf9cf1c2d06df36bc516fb0b461daf6365920e/lean/upstream/ConcreteBridge.lean#L130",
          "line": 130
        },
        {
          "path": "lean/evidence/bridge-run/result.json",
          "sha256": "29666ea7b9c28a6a643dcaeef3666f692c0e062e775d5a5eda9b5986f04883a8",
          "url": "https://github.com/Maverick0351a/finite-congruence-checks/blob/cddf9cf1c2d06df36bc516fb0b461daf6365920e/lean/evidence/bridge-run/result.json"
        }
      ]
    }
  ],
  "sources": [
    {
      "id": "scope",
      "title": "Family 206 · selected scope",
      "role": "scope_note",
      "url": "https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/docs/206.md",
      "description": "The selected formalization covers the colored-graph equivalence. The paper's undecidability and subgroup-interval conclusions are outside it."
    },
    {
      "id": "paper",
      "title": "Original paper · §1.1 and Theorem 2.2",
      "role": "paper_context",
      "url": "https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Finite-Congruence-Lattices-Characterization-and-Undecidability-September-24-2026/paper.pdf",
      "pages": [
        4,
        7,
        8
      ],
      "sha256": "d26d6cd6285de4f24158d37d1583bdee84a6426190e1b6df67853128e57d80f9",
      "description": "Page 4 defines representation onto the entire congruence lattice. Pages 7–8 state and prove the graph criterion. This context page does not audit the rest of the paper."
    },
    {
      "id": "target",
      "title": "Comparator · target statement with sorry",
      "role": "target_only",
      "url": "https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/FiniteCongruenceGraph.lean#L57",
      "description": "This challenge supplies the target statement and definitions. Its sorry placeholder is not a completed proof."
    },
    {
      "id": "definitions",
      "title": "Lean · algebra, congruence, representation",
      "role": "formal_definition",
      "path": "lean/upstream/OAI/Algebra/Universal/Congruence.lean",
      "sha256": "30e9201344dcf4069ca9ace276c76dc3b1507d09f0f6bfbf5a7c5d693ac9716c",
      "url": "https://github.com/Maverick0351a/finite-congruence-checks/blob/cddf9cf1c2d06df36bc516fb0b461daf6365920e/lean/upstream/OAI/Algebra/Universal/Congruence.lean#L18",
      "line": 18,
      "description": "A finite list of total finite-arity operations on a nonempty finite carrier; representation is an order isomorphism with all compatible equivalence relations."
    },
    {
      "id": "criterion",
      "title": "Lean · completed graph_criterion",
      "role": "completed_proof",
      "path": "lean/upstream/OAI/Algebra/Universal/GraphCriterion.lean",
      "sha256": "bd80c2bea95ee1b4f7118fc8dc272aebac7b23038ba93cdafd386dc1b688fb50",
      "url": "https://github.com/Maverick0351a/finite-congruence-checks/blob/cddf9cf1c2d06df36bc516fb0b461daf6365920e/lean/upstream/OAI/Algebra/Universal/GraphCriterion.lean#L291",
      "line": 291,
      "upstream_url": "https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Universal/GraphCriterion.lean#L291",
      "description": "The completed upstream proof of Representable Lat ↔ HasGraphWitness Lat. The local copy is bound by the recorded Lean run."
    },
    {
      "id": "tables",
      "title": "Saved N5 · exact operation tables",
      "role": "construction",
      "path": "evidence/minimized-algebras.json",
      "sha256": "76671ae20ad76bc2507b9e0c822bb78862abf2ff507f1a3ab7ba8b40efe85cea",
      "url": "https://github.com/Maverick0351a/finite-congruence-checks/blob/cddf9cf1c2d06df36bc516fb0b461daf6365920e/evidence/minimized-algebras.json",
      "json_pointer": "/certificates/5",
      "description": "These four point labels, two operation tables, and five threshold partitions identify the example."
    },
    {
      "id": "classification",
      "title": "Lean · all N5 congruences",
      "role": "completed_proof",
      "path": "lean/FiniteCongruenceChecks.lean",
      "sha256": "845615fe7be190dc733762a1b95828cffb4e09b6d3b6b0e334211000d93422e8",
      "url": "https://github.com/Maverick0351a/finite-congruence-checks/blob/cddf9cf1c2d06df36bc516fb0b461daf6365920e/lean/FiniteCongruenceChecks.lean#L142",
      "line": 142,
      "description": "The finite classification, relation completeness, and all_relations theorem establish exactly the five congruences of these operations."
    },
    {
      "id": "bridge",
      "title": "Lean · N5 bridge to the graph criterion",
      "role": "completed_proof",
      "path": "lean/upstream/ConcreteBridge.lean",
      "sha256": "8a7c9d8bc83b511026efb3b6949c6265d8ba00d85ca41ef0cc7c060cc3f1b1f6",
      "url": "https://github.com/Maverick0351a/finite-congruence-checks/blob/cddf9cf1c2d06df36bc516fb0b461daf6365920e/lean/upstream/ConcreteBridge.lean#L130",
      "line": 130,
      "description": "Builds the upstream congruence order isomorphism, identifies the saved colors as principal colors, and proves isGraphWitness and representable."
    },
    {
      "id": "receipt",
      "title": "Saved Lean build and kernel replay",
      "role": "verification_receipt",
      "path": "lean/evidence/bridge-run/result.json",
      "sha256": "29666ea7b9c28a6a643dcaeef3666f692c0e062e775d5a5eda9b5986f04883a8",
      "url": "https://github.com/Maverick0351a/finite-congruence-checks/blob/cddf9cf1c2d06df36bc516fb0b461daf6365920e/lean/evidence/bridge-run/result.json",
      "description": "Records the earlier build, Lean kernel replay, axiom checks, and source hashes. The browser does not run Lean."
    },
    {
      "id": "comparator",
      "title": "Official comparator run and negative controls",
      "role": "verification_receipt",
      "path": "lean/comparator/evidence/receipt.json",
      "sha256": "e4321a3aeed7c2c4117569959d33ad0d26abb92f1d938902f0b88423845fbb28",
      "url": "https://github.com/Maverick0351a/finite-congruence-checks/blob/cddf9cf1c2d06df36bc516fb0b461daf6365920e/lean/comparator/evidence/receipt.json",
      "description": "Separate acceptance record for the upstream theorem, with placeholder-proof and changed-statement rejection controls; Nanoda was disabled."
    }
  ],
  "atlas_relation": {
    "entry_id": "n4-E16709",
    "saved_to_atlas": [
      1,
      3,
      2,
      0
    ],
    "id": "context:family-206:saved-n5:atlas-comparison:v1",
    "claim_ids": [
      "context:family-206:saved-n5:classification:v1",
      "construction:n4-E16709"
    ],
    "construction_ids": [
      "saved:family-206:n5:v1",
      "atlas:n4-E16709:displayed-operations:v1"
    ],
    "relation": "same_grouping_family_after_relabeling",
    "evidence_status": "checked_by_finite_computation",
    "saved_grouping_index_to_atlas_index": [
      0,
      1,
      3,
      2,
      4
    ],
    "inclusion_order_preserved": true,
    "partition_checks": {
      "partitions_per_construction": 15,
      "valid_per_construction": 5
    },
    "transformed_saved_operations": [
      [
        2,
        3,
        0,
        1
      ],
      [
        3,
        1,
        1,
        3
      ]
    ],
    "atlas_operations": [
      [
        1,
        3,
        3,
        1
      ],
      [
        2,
        3,
        0,
        1
      ]
    ],
    "same_operation_set": false,
    "formal_proof_transferred": false,
    "citations": [
      {
        "path": "space/atlas-data.json",
        "sha256": "9bd8976488b269a86468dfcdb9f9ebbf246cfe8e0ffe4960f86941369919c82a",
        "url": "https://github.com/Maverick0351a/finite-congruence-checks/blob/cddf9cf1c2d06df36bc516fb0b461daf6365920e/space/atlas-data.json",
        "json_pointer": "/entries/22"
      },
      {
        "path": "evidence/atlas.json",
        "sha256": "9bd8976488b269a86468dfcdb9f9ebbf246cfe8e0ffe4960f86941369919c82a",
        "url": "https://github.com/Maverick0351a/finite-congruence-checks/blob/cddf9cf1c2d06df36bc516fb0b461daf6365920e/evidence/atlas.json",
        "json_pointer": "/entries/22"
      },
      {
        "path": "evidence/atlas-review.json",
        "sha256": "f702ebcfd8addcb12aa8cf0434c074c8869a71ae738cd996727819d8f165cd26",
        "url": "https://github.com/Maverick0351a/finite-congruence-checks/blob/cddf9cf1c2d06df36bc516fb0b461daf6365920e/evidence/atlas-review.json",
        "json_pointer": "/entries/22"
      }
    ],
    "limits": [
      "Operation-set inequality is for the displayed bijection only; this comparison does not decide algebra isomorphism under every permutation.",
      "The saved Lean classification applies to the saved tables. The atlas tables retain their independently checked computational evidence; no Lean proof is transported here."
    ],
    "explanation": "The grouping families agree after this renaming, but the displayed operation sets differ. This link is a computational correspondence, not a Lean proof of the atlas entry."
  },
  "color": [
    [
      0,
      1,
      3,
      4
    ],
    [
      1,
      0,
      4,
      3
    ],
    [
      3,
      4,
      0,
      2
    ],
    [
      4,
      3,
      2,
      0
    ]
  ],
  "lattice": {
    "name": "N5",
    "elements": [
      "0",
      "a",
      "b",
      "c",
      "1"
    ],
    "bottom": 0,
    "leq": [
      [
        true,
        true,
        true,
        true,
        true
      ],
      [
        false,
        true,
        true,
        false,
        true
      ],
      [
        false,
        false,
        true,
        false,
        true
      ],
      [
        false,
        false,
        false,
        true,
        true
      ],
      [
        false,
        false,
        false,
        false,
        true
      ]
    ],
    "join": [
      [
        0,
        1,
        2,
        3,
        4
      ],
      [
        1,
        1,
        2,
        4,
        4
      ],
      [
        2,
        2,
        2,
        4,
        4
      ],
      [
        3,
        4,
        4,
        3,
        4
      ],
      [
        4,
        4,
        4,
        4,
        4
      ]
    ]
  },
  "partition_audit": [
    {
      "partition": [
        0,
        0,
        0,
        0
      ],
      "valid": true,
      "violation": null
    },
    {
      "partition": [
        0,
        0,
        0,
        1
      ],
      "valid": false,
      "violation": {
        "operation": 0,
        "pair": [
          0,
          2
        ],
        "outputs": [
          1,
          3
        ]
      }
    },
    {
      "partition": [
        0,
        0,
        1,
        0
      ],
      "valid": false,
      "violation": {
        "operation": 0,
        "pair": [
          0,
          3
        ],
        "outputs": [
          1,
          2
        ]
      }
    },
    {
      "partition": [
        0,
        0,
        1,
        1
      ],
      "valid": true,
      "violation": null
    },
    {
      "partition": [
        0,
        0,
        1,
        2
      ],
      "valid": true,
      "violation": null
    },
    {
      "partition": [
        0,
        1,
        0,
        0
      ],
      "valid": false,
      "violation": {
        "operation": 0,
        "pair": [
          0,
          2
        ],
        "outputs": [
          1,
          3
        ]
      }
    },
    {
      "partition": [
        0,
        1,
        0,
        1
      ],
      "valid": true,
      "violation": null
    },
    {
      "partition": [
        0,
        1,
        0,
        2
      ],
      "valid": false,
      "violation": {
        "operation": 0,
        "pair": [
          0,
          2
        ],
        "outputs": [
          1,
          3
        ]
      }
    },
    {
      "partition": [
        0,
        1,
        1,
        0
      ],
      "valid": false,
      "violation": {
        "operation": 1,
        "pair": [
          0,
          3
        ],
        "outputs": [
          0,
          1
        ]
      }
    },
    {
      "partition": [
        0,
        1,
        1,
        1
      ],
      "valid": false,
      "violation": {
        "operation": 0,
        "pair": [
          1,
          2
        ],
        "outputs": [
          0,
          3
        ]
      }
    },
    {
      "partition": [
        0,
        1,
        1,
        2
      ],
      "valid": false,
      "violation": {
        "operation": 0,
        "pair": [
          1,
          2
        ],
        "outputs": [
          0,
          3
        ]
      }
    },
    {
      "partition": [
        0,
        1,
        2,
        0
      ],
      "valid": false,
      "violation": {
        "operation": 0,
        "pair": [
          0,
          3
        ],
        "outputs": [
          1,
          2
        ]
      }
    },
    {
      "partition": [
        0,
        1,
        2,
        1
      ],
      "valid": false,
      "violation": {
        "operation": 0,
        "pair": [
          1,
          3
        ],
        "outputs": [
          0,
          2
        ]
      }
    },
    {
      "partition": [
        0,
        1,
        2,
        2
      ],
      "valid": false,
      "violation": {
        "operation": 1,
        "pair": [
          2,
          3
        ],
        "outputs": [
          0,
          1
        ]
      }
    },
    {
      "partition": [
        0,
        1,
        2,
        3
      ],
      "valid": true,
      "violation": null
    }
  ],
  "connections": [
    {
      "source": "paper",
      "target": "tables",
      "label": "illustrated by",
      "kind": "illustration"
    },
    {
      "source": "tables",
      "target": "classification",
      "label": "proved using",
      "kind": "proof_reference"
    },
    {
      "source": "classification",
      "target": "bridge",
      "label": "used by bridge",
      "kind": "proof_reference"
    },
    {
      "source": "bridge",
      "target": "criterion",
      "label": "shares definitions",
      "kind": "definition_reference"
    },
    {
      "source": "criterion",
      "target": "definitions",
      "label": "defined using",
      "kind": "definition_reference"
    },
    {
      "source": "criterion",
      "target": "target",
      "label": "matches target",
      "kind": "comparison_reference"
    }
  ]
};
