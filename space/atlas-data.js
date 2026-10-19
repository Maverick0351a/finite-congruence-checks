window.ATLAS_DATA = {
  "schema_version": 1,
  "scope": "All full congruence relation families of unary algebras on labeled carriers of sizes 1 through 4; one representative per vertex-relabeling orbit, grouped by abstract lattice order isomorphism.",
  "source_sha256": {
    "evidence/operation-minima-audit.json": "2b543e8b5f824acc97f9eafa6d247a8ee3bf2451043307823f955e2a6c4ae349",
    "evidence/search-results.json": "d25ee157a0be410cd681f02b6792ecada5a2564b76cc01daf4e274fadf818472",
    "minimize_operations.py": "8979a6a9b7b53e069318b74633b3211f13af149e3aab2b9a7760eaa072c80f9b",
    "scripts/audit_operation_minima.py": "62a29dd46a940e6313551558f5020c88baaf0b440dd58df9437e336b45628819"
  },
  "generator_sha256": "6c5cf0b51d0f469a5843af7a0ab3e1f749e7631c0bd2c133d59531f9e90f824a",
  "hash_encoding": "SHA-256 of UTF-8 file bytes with CRLF normalized to LF; no other byte changes.",
  "encoding": "All indices are zero-based. Equal partition entries belong to one block. operation[x] is the image of object x. order[i][j] means partition i refines partition j. covers lists lower/upper partition indices. IDs are stable for this schema and enumeration order.",
  "evidence_status": "Exhaustive finite Python computation; the atlas entries and operation minima are not Lean proofs and carry no mathematical novelty claim.",
  "minimum_scope": "Minimum number of basic unary operations for the exact displayed relation family on its fixed carrier. The empty signature is permitted and has zero operations. This does not minimize over larger carriers, other embeddings, or higher-arity operations.",
  "method": "Binary equivalence tables; breadth-first intersections of invariant relation families for all total unary maps; all carrier permutations; exhaustive order-isomorphism backtracking; independent partition generation and two exact set-cover methods for each displayed representative.",
  "checks": {
    "passed": true,
    "negative_and_relabeling_controls": [
      "family missing equality rejected",
      "C4 distinguished from B2",
      "relabeled C4 recognized",
      "removing any selected operation changes its family"
    ]
  },
  "carrier_summary": [
    {
      "carrier_size": 1,
      "labeled_relation_families": 1,
      "embedding_orbits": 1,
      "abstract_types": 1
    },
    {
      "carrier_size": 2,
      "labeled_relation_families": 1,
      "embedding_orbits": 1,
      "abstract_types": 1
    },
    {
      "carrier_size": 3,
      "labeled_relation_families": 8,
      "embedding_orbits": 4,
      "abstract_types": 4
    },
    {
      "carrier_size": 4,
      "labeled_relation_families": 303,
      "embedding_orbits": 33,
      "abstract_types": 21
    }
  ],
  "abstract_types": [
    {
      "id": "T01",
      "name": "Shape T01",
      "lattice_elements": 1,
      "embedding_ids": [
        "n1-E1"
      ]
    },
    {
      "id": "T02",
      "name": "C2",
      "lattice_elements": 2,
      "embedding_ids": [
        "n2-E3",
        "n3-E17",
        "n4-E16385"
      ]
    },
    {
      "id": "T03",
      "name": "C3",
      "lattice_elements": 3,
      "embedding_ids": [
        "n3-E19",
        "n4-E16387",
        "n4-E16401",
        "n4-E16449"
      ]
    },
    {
      "id": "T04",
      "name": "B2",
      "lattice_elements": 4,
      "embedding_ids": [
        "n3-E23",
        "n4-E16433",
        "n4-E16451",
        "n4-E16705"
      ]
    },
    {
      "id": "T05",
      "name": "M3",
      "lattice_elements": 5,
      "embedding_ids": [
        "n3-E31",
        "n4-E18753"
      ]
    },
    {
      "id": "T06",
      "name": "C4",
      "lattice_elements": 4,
      "embedding_ids": [
        "n4-E16403",
        "n4-E16457"
      ]
    },
    {
      "id": "T07",
      "name": "Shape T07",
      "lattice_elements": 5,
      "embedding_ids": [
        "n4-E16407",
        "n4-E16489"
      ]
    },
    {
      "id": "T08",
      "name": "Shape T08",
      "lattice_elements": 6,
      "embedding_ids": [
        "n4-E16415"
      ]
    },
    {
      "id": "T09",
      "name": "Shape T09",
      "lattice_elements": 5,
      "embedding_ids": [
        "n4-E16473",
        "n4-E16915"
      ]
    },
    {
      "id": "T10",
      "name": "Shape T10",
      "lattice_elements": 6,
      "embedding_ids": [
        "n4-E16475",
        "n4-E16505",
        "n4-E16919"
      ]
    },
    {
      "id": "T11",
      "name": "Shape T11",
      "lattice_elements": 7,
      "embedding_ids": [
        "n4-E16479",
        "n4-E16927"
      ]
    },
    {
      "id": "T12",
      "name": "N5",
      "lattice_elements": 5,
      "embedding_ids": [
        "n4-E16709"
      ]
    },
    {
      "id": "T13",
      "name": "Shape T13",
      "lattice_elements": 7,
      "embedding_ids": [
        "n4-E16733"
      ]
    },
    {
      "id": "T14",
      "name": "Shape T14",
      "lattice_elements": 6,
      "embedding_ids": [
        "n4-E16745"
      ]
    },
    {
      "id": "T15",
      "name": "B3",
      "lattice_elements": 8,
      "embedding_ids": [
        "n4-E17019",
        "n4-E21047"
      ]
    },
    {
      "id": "T16",
      "name": "Shape T16",
      "lattice_elements": 7,
      "embedding_ids": [
        "n4-E18793"
      ]
    },
    {
      "id": "T17",
      "name": "Shape T17",
      "lattice_elements": 6,
      "embedding_ids": [
        "n4-E18963"
      ]
    },
    {
      "id": "T18",
      "name": "Shape T18",
      "lattice_elements": 7,
      "embedding_ids": [
        "n4-E18967",
        "n4-E19987"
      ]
    },
    {
      "id": "T19",
      "name": "Shape T19",
      "lattice_elements": 8,
      "embedding_ids": [
        "n4-E18975"
      ]
    },
    {
      "id": "T20",
      "name": "Shape T20",
      "lattice_elements": 9,
      "embedding_ids": [
        "n4-E19067"
      ]
    },
    {
      "id": "T21",
      "name": "Shape T21",
      "lattice_elements": 10,
      "embedding_ids": [
        "n4-E21119"
      ]
    },
    {
      "id": "T22",
      "name": "Shape T22",
      "lattice_elements": 15,
      "embedding_ids": [
        "n4-E32767"
      ]
    }
  ],
  "entries": [
    {
      "id": "n1-E1",
      "carrier_size": 1,
      "abstract_type": "T01",
      "name": "Shape T01",
      "partitions": [
        [
          0
        ]
      ],
      "operations": [],
      "minimum_unary_operations": 0,
      "orbit_size": 1,
      "order": [
        [
          true
        ]
      ],
      "covers": [],
      "named_targets": []
    },
    {
      "id": "n2-E3",
      "carrier_size": 2,
      "abstract_type": "T02",
      "name": "C2",
      "partitions": [
        [
          0,
          1
        ],
        [
          0,
          0
        ]
      ],
      "operations": [],
      "minimum_unary_operations": 0,
      "orbit_size": 1,
      "order": [
        [
          true,
          true
        ],
        [
          false,
          true
        ]
      ],
      "covers": [
        [
          0,
          1
        ]
      ],
      "named_targets": [
        "C2"
      ]
    },
    {
      "id": "n3-E17",
      "carrier_size": 3,
      "abstract_type": "T02",
      "name": "C2",
      "partitions": [
        [
          0,
          1,
          2
        ],
        [
          0,
          0,
          0
        ]
      ],
      "operations": [
        [
          1,
          2,
          0
        ]
      ],
      "minimum_unary_operations": 1,
      "orbit_size": 1,
      "order": [
        [
          true,
          true
        ],
        [
          false,
          true
        ]
      ],
      "covers": [
        [
          0,
          1
        ]
      ],
      "named_targets": [
        "C2"
      ]
    },
    {
      "id": "n3-E19",
      "carrier_size": 3,
      "abstract_type": "T03",
      "name": "C3",
      "partitions": [
        [
          0,
          1,
          2
        ],
        [
          0,
          1,
          1
        ],
        [
          0,
          0,
          0
        ]
      ],
      "operations": [
        [
          0,
          2,
          1
        ]
      ],
      "minimum_unary_operations": 1,
      "orbit_size": 3,
      "order": [
        [
          true,
          true,
          true
        ],
        [
          false,
          true,
          true
        ],
        [
          false,
          false,
          true
        ]
      ],
      "covers": [
        [
          0,
          1
        ],
        [
          1,
          2
        ]
      ],
      "named_targets": [
        "C3"
      ]
    },
    {
      "id": "n3-E23",
      "carrier_size": 3,
      "abstract_type": "T04",
      "name": "B2",
      "partitions": [
        [
          0,
          1,
          2
        ],
        [
          0,
          1,
          1
        ],
        [
          0,
          1,
          0
        ],
        [
          0,
          0,
          0
        ]
      ],
      "operations": [
        [
          0,
          2,
          2
        ]
      ],
      "minimum_unary_operations": 1,
      "orbit_size": 3,
      "order": [
        [
          true,
          true,
          true,
          true
        ],
        [
          false,
          true,
          false,
          true
        ],
        [
          false,
          false,
          true,
          true
        ],
        [
          false,
          false,
          false,
          true
        ]
      ],
      "covers": [
        [
          0,
          1
        ],
        [
          0,
          2
        ],
        [
          1,
          3
        ],
        [
          2,
          3
        ]
      ],
      "named_targets": [
        "B2"
      ]
    },
    {
      "id": "n3-E31",
      "carrier_size": 3,
      "abstract_type": "T05",
      "name": "M3",
      "partitions": [
        [
          0,
          1,
          2
        ],
        [
          0,
          1,
          1
        ],
        [
          0,
          1,
          0
        ],
        [
          0,
          0,
          1
        ],
        [
          0,
          0,
          0
        ]
      ],
      "operations": [],
      "minimum_unary_operations": 0,
      "orbit_size": 1,
      "order": [
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
          false,
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
      "covers": [
        [
          0,
          1
        ],
        [
          0,
          2
        ],
        [
          0,
          3
        ],
        [
          1,
          4
        ],
        [
          2,
          4
        ],
        [
          3,
          4
        ]
      ],
      "named_targets": [
        "M3"
      ]
    },
    {
      "id": "n4-E16385",
      "carrier_size": 4,
      "abstract_type": "T02",
      "name": "C2",
      "partitions": [
        [
          0,
          1,
          2,
          3
        ],
        [
          0,
          0,
          0,
          0
        ]
      ],
      "operations": [
        [
          0,
          3,
          3,
          3
        ],
        [
          1,
          0,
          1,
          2
        ]
      ],
      "minimum_unary_operations": 2,
      "orbit_size": 1,
      "order": [
        [
          true,
          true
        ],
        [
          false,
          true
        ]
      ],
      "covers": [
        [
          0,
          1
        ]
      ],
      "named_targets": [
        "C2"
      ]
    },
    {
      "id": "n4-E16387",
      "carrier_size": 4,
      "abstract_type": "T03",
      "name": "C3",
      "partitions": [
        [
          0,
          1,
          2,
          3
        ],
        [
          0,
          1,
          2,
          2
        ],
        [
          0,
          0,
          0,
          0
        ]
      ],
      "operations": [
        [
          0,
          3,
          3,
          3
        ],
        [
          1,
          0,
          2,
          2
        ]
      ],
      "minimum_unary_operations": 2,
      "orbit_size": 6,
      "order": [
        [
          true,
          true,
          true
        ],
        [
          false,
          true,
          true
        ],
        [
          false,
          false,
          true
        ]
      ],
      "covers": [
        [
          0,
          1
        ],
        [
          1,
          2
        ]
      ],
      "named_targets": [
        "C3"
      ]
    },
    {
      "id": "n4-E16401",
      "carrier_size": 4,
      "abstract_type": "T03",
      "name": "C3",
      "partitions": [
        [
          0,
          1,
          2,
          3
        ],
        [
          0,
          1,
          1,
          1
        ],
        [
          0,
          0,
          0,
          0
        ]
      ],
      "operations": [
        [
          0,
          2,
          3,
          1
        ]
      ],
      "minimum_unary_operations": 1,
      "orbit_size": 4,
      "order": [
        [
          true,
          true,
          true
        ],
        [
          false,
          true,
          true
        ],
        [
          false,
          false,
          true
        ]
      ],
      "covers": [
        [
          0,
          1
        ],
        [
          1,
          2
        ]
      ],
      "named_targets": [
        "C3"
      ]
    },
    {
      "id": "n4-E16403",
      "carrier_size": 4,
      "abstract_type": "T06",
      "name": "C4",
      "partitions": [
        [
          0,
          1,
          2,
          3
        ],
        [
          0,
          1,
          2,
          2
        ],
        [
          0,
          1,
          1,
          1
        ],
        [
          0,
          0,
          0,
          0
        ]
      ],
      "operations": [
        [
          1,
          2,
          3,
          3
        ]
      ],
      "minimum_unary_operations": 1,
      "orbit_size": 12,
      "order": [
        [
          true,
          true,
          true,
          true
        ],
        [
          false,
          true,
          true,
          true
        ],
        [
          false,
          false,
          true,
          true
        ],
        [
          false,
          false,
          false,
          true
        ]
      ],
      "covers": [
        [
          0,
          1
        ],
        [
          1,
          2
        ],
        [
          2,
          3
        ]
      ],
      "named_targets": [
        "C4"
      ]
    },
    {
      "id": "n4-E16407",
      "carrier_size": 4,
      "abstract_type": "T07",
      "name": "Shape T07",
      "partitions": [
        [
          0,
          1,
          2,
          3
        ],
        [
          0,
          1,
          2,
          2
        ],
        [
          0,
          1,
          2,
          1
        ],
        [
          0,
          1,
          1,
          1
        ],
        [
          0,
          0,
          0,
          0
        ]
      ],
      "operations": [
        [
          0,
          3,
          3,
          3
        ],
        [
          1,
          2,
          3,
          2
        ]
      ],
      "minimum_unary_operations": 2,
      "orbit_size": 12,
      "order": [
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
          false,
          true,
          true
        ],
        [
          false,
          false,
          true,
          true,
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
      "covers": [
        [
          0,
          1
        ],
        [
          0,
          2
        ],
        [
          1,
          3
        ],
        [
          2,
          3
        ],
        [
          3,
          4
        ]
      ],
      "named_targets": []
    },
    {
      "id": "n4-E16415",
      "carrier_size": 4,
      "abstract_type": "T08",
      "name": "Shape T08",
      "partitions": [
        [
          0,
          1,
          2,
          3
        ],
        [
          0,
          1,
          2,
          2
        ],
        [
          0,
          1,
          2,
          1
        ],
        [
          0,
          1,
          1,
          2
        ],
        [
          0,
          1,
          1,
          1
        ],
        [
          0,
          0,
          0,
          0
        ]
      ],
      "operations": [
        [
          1,
          2,
          2,
          2
        ],
        [
          1,
          3,
          3,
          3
        ]
      ],
      "minimum_unary_operations": 2,
      "orbit_size": 4,
      "order": [
        [
          true,
          true,
          true,
          true,
          true,
          true
        ],
        [
          false,
          true,
          false,
          false,
          true,
          true
        ],
        [
          false,
          false,
          true,
          false,
          true,
          true
        ],
        [
          false,
          false,
          false,
          true,
          true,
          true
        ],
        [
          false,
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
          false,
          true
        ]
      ],
      "covers": [
        [
          0,
          1
        ],
        [
          0,
          2
        ],
        [
          0,
          3
        ],
        [
          1,
          4
        ],
        [
          2,
          4
        ],
        [
          3,
          4
        ],
        [
          4,
          5
        ]
      ],
      "named_targets": []
    },
    {
      "id": "n4-E16433",
      "carrier_size": 4,
      "abstract_type": "T04",
      "name": "B2",
      "partitions": [
        [
          0,
          1,
          2,
          3
        ],
        [
          0,
          1,
          1,
          1
        ],
        [
          0,
          1,
          2,
          0
        ],
        [
          0,
          0,
          0,
          0
        ]
      ],
      "operations": [
        [
          1,
          2,
          3,
          1
        ]
      ],
      "minimum_unary_operations": 1,
      "orbit_size": 12,
      "order": [
        [
          true,
          true,
          true,
          true
        ],
        [
          false,
          true,
          false,
          true
        ],
        [
          false,
          false,
          true,
          true
        ],
        [
          false,
          false,
          false,
          true
        ]
      ],
      "covers": [
        [
          0,
          1
        ],
        [
          0,
          2
        ],
        [
          1,
          3
        ],
        [
          2,
          3
        ]
      ],
      "named_targets": [
        "B2"
      ]
    },
    {
      "id": "n4-E16449",
      "carrier_size": 4,
      "abstract_type": "T03",
      "name": "C3",
      "partitions": [
        [
          0,
          1,
          2,
          3
        ],
        [
          0,
          1,
          1,
          0
        ],
        [
          0,
          0,
          0,
          0
        ]
      ],
      "operations": [
        [
          1,
          3,
          0,
          2
        ]
      ],
      "minimum_unary_operations": 1,
      "orbit_size": 3,
      "order": [
        [
          true,
          true,
          true
        ],
        [
          false,
          true,
          true
        ],
        [
          false,
          false,
          true
        ]
      ],
      "covers": [
        [
          0,
          1
        ],
        [
          1,
          2
        ]
      ],
      "named_targets": [
        "C3"
      ]
    },
    {
      "id": "n4-E16451",
      "carrier_size": 4,
      "abstract_type": "T04",
      "name": "B2",
      "partitions": [
        [
          0,
          1,
          2,
          3
        ],
        [
          0,
          1,
          2,
          2
        ],
        [
          0,
          1,
          1,
          0
        ],
        [
          0,
          0,
          0,
          0
        ]
      ],
      "operations": [
        [
          0,
          3,
          3,
          3
        ],
        [
          1,
          0,
          3,
          2
        ]
      ],
      "minimum_unary_operations": 2,
      "orbit_size": 12,
      "order": [
        [
          true,
          true,
          true,
          true
        ],
        [
          false,
          true,
          false,
          true
        ],
        [
          false,
          false,
          true,
          true
        ],
        [
          false,
          false,
          false,
          true
        ]
      ],
      "covers": [
        [
          0,
          1
        ],
        [
          0,
          2
        ],
        [
          1,
          3
        ],
        [
          2,
          3
        ]
      ],
      "named_targets": [
        "B2"
      ]
    },
    {
      "id": "n4-E16457",
      "carrier_size": 4,
      "abstract_type": "T06",
      "name": "C4",
      "partitions": [
        [
          0,
          1,
          2,
          3
        ],
        [
          0,
          1,
          1,
          2
        ],
        [
          0,
          1,
          1,
          0
        ],
        [
          0,
          0,
          0,
          0
        ]
      ],
      "operations": [
        [
          0,
          3,
          3,
          3
        ],
        [
          2,
          0,
          0,
          1
        ]
      ],
      "minimum_unary_operations": 2,
      "orbit_size": 6,
      "order": [
        [
          true,
          true,
          true,
          true
        ],
        [
          false,
          true,
          true,
          true
        ],
        [
          false,
          false,
          true,
          true
        ],
        [
          false,
          false,
          false,
          true
        ]
      ],
      "covers": [
        [
          0,
          1
        ],
        [
          1,
          2
        ],
        [
          2,
          3
        ]
      ],
      "named_targets": [
        "C4"
      ]
    },
    {
      "id": "n4-E16473",
      "carrier_size": 4,
      "abstract_type": "T09",
      "name": "Shape T09",
      "partitions": [
        [
          0,
          1,
          2,
          3
        ],
        [
          0,
          1,
          1,
          2
        ],
        [
          0,
          1,
          1,
          1
        ],
        [
          0,
          1,
          1,
          0
        ],
        [
          0,
          0,
          0,
          0
        ]
      ],
      "operations": [
        [
          0,
          3,
          3,
          3
        ],
        [
          1,
          1,
          1,
          2
        ]
      ],
      "minimum_unary_operations": 2,
      "orbit_size": 12,
      "order": [
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
          true,
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
      "covers": [
        [
          0,
          1
        ],
        [
          1,
          2
        ],
        [
          1,
          3
        ],
        [
          2,
          4
        ],
        [
          3,
          4
        ]
      ],
      "named_targets": []
    },
    {
      "id": "n4-E16475",
      "carrier_size": 4,
      "abstract_type": "T10",
      "name": "Shape T10",
      "partitions": [
        [
          0,
          1,
          2,
          3
        ],
        [
          0,
          1,
          2,
          2
        ],
        [
          0,
          1,
          1,
          2
        ],
        [
          0,
          1,
          1,
          1
        ],
        [
          0,
          1,
          1,
          0
        ],
        [
          0,
          0,
          0,
          0
        ]
      ],
      "operations": [
        [
          1,
          3,
          3,
          2
        ]
      ],
      "minimum_unary_operations": 1,
      "orbit_size": 24,
      "order": [
        [
          true,
          true,
          true,
          true,
          true,
          true
        ],
        [
          false,
          true,
          false,
          true,
          false,
          true
        ],
        [
          false,
          false,
          true,
          true,
          true,
          true
        ],
        [
          false,
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
          false,
          true,
          true
        ],
        [
          false,
          false,
          false,
          false,
          false,
          true
        ]
      ],
      "covers": [
        [
          0,
          1
        ],
        [
          0,
          2
        ],
        [
          1,
          3
        ],
        [
          2,
          3
        ],
        [
          2,
          4
        ],
        [
          3,
          5
        ],
        [
          4,
          5
        ]
      ],
      "named_targets": []
    },
    {
      "id": "n4-E16479",
      "carrier_size": 4,
      "abstract_type": "T11",
      "name": "Shape T11",
      "partitions": [
        [
          0,
          1,
          2,
          3
        ],
        [
          0,
          1,
          2,
          2
        ],
        [
          0,
          1,
          2,
          1
        ],
        [
          0,
          1,
          1,
          2
        ],
        [
          0,
          1,
          1,
          1
        ],
        [
          0,
          1,
          1,
          0
        ],
        [
          0,
          0,
          0,
          0
        ]
      ],
      "operations": [
        [
          0,
          3,
          3,
          3
        ],
        [
          1,
          2,
          2,
          2
        ]
      ],
      "minimum_unary_operations": 2,
      "orbit_size": 12,
      "order": [
        [
          true,
          true,
          true,
          true,
          true,
          true,
          true
        ],
        [
          false,
          true,
          false,
          false,
          true,
          false,
          true
        ],
        [
          false,
          false,
          true,
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
          true,
          true,
          true
        ],
        [
          false,
          false,
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
          false,
          false,
          true
        ]
      ],
      "covers": [
        [
          0,
          1
        ],
        [
          0,
          2
        ],
        [
          0,
          3
        ],
        [
          1,
          4
        ],
        [
          2,
          4
        ],
        [
          3,
          4
        ],
        [
          3,
          5
        ],
        [
          4,
          6
        ],
        [
          5,
          6
        ]
      ],
      "named_targets": []
    },
    {
      "id": "n4-E16489",
      "carrier_size": 4,
      "abstract_type": "T07",
      "name": "Shape T07",
      "partitions": [
        [
          0,
          1,
          2,
          3
        ],
        [
          0,
          1,
          1,
          2
        ],
        [
          0,
          1,
          2,
          0
        ],
        [
          0,
          1,
          1,
          0
        ],
        [
          0,
          0,
          0,
          0
        ]
      ],
      "operations": [
        [
          0,
          3,
          3,
          3
        ],
        [
          3,
          2,
          1,
          0
        ]
      ],
      "minimum_unary_operations": 2,
      "orbit_size": 3,
      "order": [
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
          false,
          true,
          true
        ],
        [
          false,
          false,
          true,
          true,
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
      "covers": [
        [
          0,
          1
        ],
        [
          0,
          2
        ],
        [
          1,
          3
        ],
        [
          2,
          3
        ],
        [
          3,
          4
        ]
      ],
      "named_targets": []
    },
    {
      "id": "n4-E16505",
      "carrier_size": 4,
      "abstract_type": "T10",
      "name": "Shape T10",
      "partitions": [
        [
          0,
          1,
          2,
          3
        ],
        [
          0,
          1,
          1,
          2
        ],
        [
          0,
          1,
          1,
          1
        ],
        [
          0,
          1,
          2,
          0
        ],
        [
          0,
          1,
          1,
          0
        ],
        [
          0,
          0,
          0,
          0
        ]
      ],
      "operations": [
        [
          3,
          2,
          1,
          3
        ]
      ],
      "minimum_unary_operations": 1,
      "orbit_size": 12,
      "order": [
        [
          true,
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
          true,
          true
        ],
        [
          false,
          false,
          true,
          false,
          false,
          true
        ],
        [
          false,
          false,
          false,
          true,
          true,
          true
        ],
        [
          false,
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
          false,
          true
        ]
      ],
      "covers": [
        [
          0,
          1
        ],
        [
          0,
          3
        ],
        [
          1,
          2
        ],
        [
          1,
          4
        ],
        [
          2,
          5
        ],
        [
          3,
          4
        ],
        [
          4,
          5
        ]
      ],
      "named_targets": []
    },
    {
      "id": "n4-E16705",
      "carrier_size": 4,
      "abstract_type": "T04",
      "name": "B2",
      "partitions": [
        [
          0,
          1,
          2,
          3
        ],
        [
          0,
          1,
          1,
          0
        ],
        [
          0,
          1,
          0,
          1
        ],
        [
          0,
          0,
          0,
          0
        ]
      ],
      "operations": [
        [
          1,
          0,
          3,
          2
        ],
        [
          1,
          3,
          3,
          1
        ]
      ],
      "minimum_unary_operations": 2,
      "orbit_size": 3,
      "order": [
        [
          true,
          true,
          true,
          true
        ],
        [
          false,
          true,
          false,
          true
        ],
        [
          false,
          false,
          true,
          true
        ],
        [
          false,
          false,
          false,
          true
        ]
      ],
      "covers": [
        [
          0,
          1
        ],
        [
          0,
          2
        ],
        [
          1,
          3
        ],
        [
          2,
          3
        ]
      ],
      "named_targets": [
        "B2"
      ]
    },
    {
      "id": "n4-E16709",
      "carrier_size": 4,
      "abstract_type": "T12",
      "name": "N5",
      "partitions": [
        [
          0,
          1,
          2,
          3
        ],
        [
          0,
          1,
          2,
          1
        ],
        [
          0,
          1,
          1,
          0
        ],
        [
          0,
          1,
          0,
          1
        ],
        [
          0,
          0,
          0,
          0
        ]
      ],
      "operations": [
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
      "minimum_unary_operations": 2,
      "orbit_size": 12,
      "order": [
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
          false,
          true,
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
      "covers": [
        [
          0,
          1
        ],
        [
          0,
          2
        ],
        [
          1,
          3
        ],
        [
          2,
          4
        ],
        [
          3,
          4
        ]
      ],
      "named_targets": [
        "N5"
      ]
    },
    {
      "id": "n4-E16733",
      "carrier_size": 4,
      "abstract_type": "T13",
      "name": "Shape T13",
      "partitions": [
        [
          0,
          1,
          2,
          3
        ],
        [
          0,
          1,
          2,
          1
        ],
        [
          0,
          1,
          1,
          2
        ],
        [
          0,
          1,
          1,
          1
        ],
        [
          0,
          1,
          1,
          0
        ],
        [
          0,
          1,
          0,
          1
        ],
        [
          0,
          0,
          0,
          0
        ]
      ],
      "operations": [
        [
          1,
          3,
          3,
          1
        ],
        [
          1,
          2,
          1,
          2
        ]
      ],
      "minimum_unary_operations": 2,
      "orbit_size": 12,
      "order": [
        [
          true,
          true,
          true,
          true,
          true,
          true,
          true
        ],
        [
          false,
          true,
          false,
          true,
          false,
          true,
          true
        ],
        [
          false,
          false,
          true,
          true,
          true,
          false,
          true
        ],
        [
          false,
          false,
          false,
          true,
          false,
          false,
          true
        ],
        [
          false,
          false,
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
          false,
          false,
          true
        ]
      ],
      "covers": [
        [
          0,
          1
        ],
        [
          0,
          2
        ],
        [
          1,
          3
        ],
        [
          1,
          5
        ],
        [
          2,
          3
        ],
        [
          2,
          4
        ],
        [
          3,
          6
        ],
        [
          4,
          6
        ],
        [
          5,
          6
        ]
      ],
      "named_targets": []
    },
    {
      "id": "n4-E16745",
      "carrier_size": 4,
      "abstract_type": "T14",
      "name": "Shape T14",
      "partitions": [
        [
          0,
          1,
          2,
          3
        ],
        [
          0,
          1,
          1,
          2
        ],
        [
          0,
          1,
          2,
          0
        ],
        [
          0,
          1,
          1,
          0
        ],
        [
          0,
          1,
          0,
          1
        ],
        [
          0,
          0,
          0,
          0
        ]
      ],
      "operations": [
        [
          1,
          3,
          3,
          1
        ],
        [
          0,
          2,
          2,
          0
        ]
      ],
      "minimum_unary_operations": 2,
      "orbit_size": 6,
      "order": [
        [
          true,
          true,
          true,
          true,
          true,
          true
        ],
        [
          false,
          true,
          false,
          true,
          false,
          true
        ],
        [
          false,
          false,
          true,
          true,
          false,
          true
        ],
        [
          false,
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
          false,
          true,
          true
        ],
        [
          false,
          false,
          false,
          false,
          false,
          true
        ]
      ],
      "covers": [
        [
          0,
          1
        ],
        [
          0,
          2
        ],
        [
          0,
          4
        ],
        [
          1,
          3
        ],
        [
          2,
          3
        ],
        [
          3,
          5
        ],
        [
          4,
          5
        ]
      ],
      "named_targets": []
    },
    {
      "id": "n4-E16915",
      "carrier_size": 4,
      "abstract_type": "T09",
      "name": "Shape T09",
      "partitions": [
        [
          0,
          1,
          2,
          3
        ],
        [
          0,
          1,
          2,
          2
        ],
        [
          0,
          1,
          1,
          1
        ],
        [
          0,
          1,
          0,
          0
        ],
        [
          0,
          0,
          0,
          0
        ]
      ],
      "operations": [
        [
          0,
          3,
          3,
          3
        ],
        [
          0,
          3,
          2,
          2
        ]
      ],
      "minimum_unary_operations": 2,
      "orbit_size": 6,
      "order": [
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
          true,
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
      "covers": [
        [
          0,
          1
        ],
        [
          1,
          2
        ],
        [
          1,
          3
        ],
        [
          2,
          4
        ],
        [
          3,
          4
        ]
      ],
      "named_targets": []
    },
    {
      "id": "n4-E16919",
      "carrier_size": 4,
      "abstract_type": "T10",
      "name": "Shape T10",
      "partitions": [
        [
          0,
          1,
          2,
          3
        ],
        [
          0,
          1,
          2,
          2
        ],
        [
          0,
          1,
          2,
          1
        ],
        [
          0,
          1,
          1,
          1
        ],
        [
          0,
          1,
          0,
          0
        ],
        [
          0,
          0,
          0,
          0
        ]
      ],
      "operations": [
        [
          0,
          2,
          3,
          2
        ]
      ],
      "minimum_unary_operations": 1,
      "orbit_size": 24,
      "order": [
        [
          true,
          true,
          true,
          true,
          true,
          true
        ],
        [
          false,
          true,
          false,
          true,
          true,
          true
        ],
        [
          false,
          false,
          true,
          true,
          false,
          true
        ],
        [
          false,
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
          false,
          true,
          true
        ],
        [
          false,
          false,
          false,
          false,
          false,
          true
        ]
      ],
      "covers": [
        [
          0,
          1
        ],
        [
          0,
          2
        ],
        [
          1,
          3
        ],
        [
          1,
          4
        ],
        [
          2,
          3
        ],
        [
          3,
          5
        ],
        [
          4,
          5
        ]
      ],
      "named_targets": []
    },
    {
      "id": "n4-E16927",
      "carrier_size": 4,
      "abstract_type": "T11",
      "name": "Shape T11",
      "partitions": [
        [
          0,
          1,
          2,
          3
        ],
        [
          0,
          1,
          2,
          2
        ],
        [
          0,
          1,
          2,
          1
        ],
        [
          0,
          1,
          1,
          2
        ],
        [
          0,
          1,
          1,
          1
        ],
        [
          0,
          1,
          0,
          0
        ],
        [
          0,
          0,
          0,
          0
        ]
      ],
      "operations": [
        [
          0,
          3,
          3,
          3
        ],
        [
          0,
          2,
          2,
          2
        ]
      ],
      "minimum_unary_operations": 2,
      "orbit_size": 12,
      "order": [
        [
          true,
          true,
          true,
          true,
          true,
          true,
          true
        ],
        [
          false,
          true,
          false,
          false,
          true,
          true,
          true
        ],
        [
          false,
          false,
          true,
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
          true,
          false,
          true
        ],
        [
          false,
          false,
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
          false,
          false,
          true
        ]
      ],
      "covers": [
        [
          0,
          1
        ],
        [
          0,
          2
        ],
        [
          0,
          3
        ],
        [
          1,
          4
        ],
        [
          1,
          5
        ],
        [
          2,
          4
        ],
        [
          3,
          4
        ],
        [
          4,
          6
        ],
        [
          5,
          6
        ]
      ],
      "named_targets": []
    },
    {
      "id": "n4-E17019",
      "carrier_size": 4,
      "abstract_type": "T15",
      "name": "B3",
      "partitions": [
        [
          0,
          1,
          2,
          3
        ],
        [
          0,
          1,
          2,
          2
        ],
        [
          0,
          1,
          1,
          2
        ],
        [
          0,
          1,
          1,
          1
        ],
        [
          0,
          1,
          2,
          0
        ],
        [
          0,
          1,
          1,
          0
        ],
        [
          0,
          1,
          0,
          0
        ],
        [
          0,
          0,
          0,
          0
        ]
      ],
      "operations": [
        [
          0,
          3,
          3,
          3
        ],
        [
          0,
          2,
          2,
          3
        ]
      ],
      "minimum_unary_operations": 2,
      "orbit_size": 12,
      "order": [
        [
          true,
          true,
          true,
          true,
          true,
          true,
          true,
          true
        ],
        [
          false,
          true,
          false,
          true,
          false,
          false,
          true,
          true
        ],
        [
          false,
          false,
          true,
          true,
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
          false,
          false,
          false,
          true
        ],
        [
          false,
          false,
          false,
          false,
          true,
          true,
          true,
          true
        ],
        [
          false,
          false,
          false,
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
          false,
          false,
          false,
          true
        ]
      ],
      "covers": [
        [
          0,
          1
        ],
        [
          0,
          2
        ],
        [
          0,
          4
        ],
        [
          1,
          3
        ],
        [
          1,
          6
        ],
        [
          2,
          3
        ],
        [
          2,
          5
        ],
        [
          3,
          7
        ],
        [
          4,
          5
        ],
        [
          4,
          6
        ],
        [
          5,
          7
        ],
        [
          6,
          7
        ]
      ],
      "named_targets": [
        "B3"
      ]
    },
    {
      "id": "n4-E18753",
      "carrier_size": 4,
      "abstract_type": "T05",
      "name": "M3",
      "partitions": [
        [
          0,
          1,
          2,
          3
        ],
        [
          0,
          1,
          1,
          0
        ],
        [
          0,
          1,
          0,
          1
        ],
        [
          0,
          0,
          1,
          1
        ],
        [
          0,
          0,
          0,
          0
        ]
      ],
      "operations": [
        [
          1,
          0,
          3,
          2
        ],
        [
          2,
          3,
          0,
          1
        ]
      ],
      "minimum_unary_operations": 2,
      "orbit_size": 1,
      "order": [
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
          false,
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
      "covers": [
        [
          0,
          1
        ],
        [
          0,
          2
        ],
        [
          0,
          3
        ],
        [
          1,
          4
        ],
        [
          2,
          4
        ],
        [
          3,
          4
        ]
      ],
      "named_targets": [
        "M3"
      ]
    },
    {
      "id": "n4-E18793",
      "carrier_size": 4,
      "abstract_type": "T16",
      "name": "Shape T16",
      "partitions": [
        [
          0,
          1,
          2,
          3
        ],
        [
          0,
          1,
          1,
          2
        ],
        [
          0,
          1,
          2,
          0
        ],
        [
          0,
          1,
          1,
          0
        ],
        [
          0,
          1,
          0,
          1
        ],
        [
          0,
          0,
          1,
          1
        ],
        [
          0,
          0,
          0,
          0
        ]
      ],
      "operations": [
        [
          3,
          2,
          1,
          0
        ]
      ],
      "minimum_unary_operations": 1,
      "orbit_size": 3,
      "order": [
        [
          true,
          true,
          true,
          true,
          true,
          true,
          true
        ],
        [
          false,
          true,
          false,
          true,
          false,
          false,
          true
        ],
        [
          false,
          false,
          true,
          true,
          false,
          false,
          true
        ],
        [
          false,
          false,
          false,
          true,
          false,
          false,
          true
        ],
        [
          false,
          false,
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
          false,
          false,
          true
        ]
      ],
      "covers": [
        [
          0,
          1
        ],
        [
          0,
          2
        ],
        [
          0,
          4
        ],
        [
          0,
          5
        ],
        [
          1,
          3
        ],
        [
          2,
          3
        ],
        [
          3,
          6
        ],
        [
          4,
          6
        ],
        [
          5,
          6
        ]
      ],
      "named_targets": []
    },
    {
      "id": "n4-E18963",
      "carrier_size": 4,
      "abstract_type": "T17",
      "name": "Shape T17",
      "partitions": [
        [
          0,
          1,
          2,
          3
        ],
        [
          0,
          1,
          2,
          2
        ],
        [
          0,
          1,
          1,
          1
        ],
        [
          0,
          1,
          0,
          0
        ],
        [
          0,
          0,
          1,
          1
        ],
        [
          0,
          0,
          0,
          0
        ]
      ],
      "operations": [
        [
          2,
          3,
          3,
          3
        ],
        [
          2,
          3,
          2,
          2
        ]
      ],
      "minimum_unary_operations": 2,
      "orbit_size": 6,
      "order": [
        [
          true,
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
          true,
          true,
          true
        ],
        [
          false,
          false,
          true,
          false,
          false,
          true
        ],
        [
          false,
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
          false,
          true,
          true
        ],
        [
          false,
          false,
          false,
          false,
          false,
          true
        ]
      ],
      "covers": [
        [
          0,
          1
        ],
        [
          1,
          2
        ],
        [
          1,
          3
        ],
        [
          1,
          4
        ],
        [
          2,
          5
        ],
        [
          3,
          5
        ],
        [
          4,
          5
        ]
      ],
      "named_targets": []
    },
    {
      "id": "n4-E18967",
      "carrier_size": 4,
      "abstract_type": "T18",
      "name": "Shape T18",
      "partitions": [
        [
          0,
          1,
          2,
          3
        ],
        [
          0,
          1,
          2,
          2
        ],
        [
          0,
          1,
          2,
          1
        ],
        [
          0,
          1,
          1,
          1
        ],
        [
          0,
          1,
          0,
          0
        ],
        [
          0,
          0,
          1,
          1
        ],
        [
          0,
          0,
          0,
          0
        ]
      ],
      "operations": [
        [
          0,
          1,
          3,
          3
        ],
        [
          2,
          3,
          3,
          3
        ]
      ],
      "minimum_unary_operations": 2,
      "orbit_size": 24,
      "order": [
        [
          true,
          true,
          true,
          true,
          true,
          true,
          true
        ],
        [
          false,
          true,
          false,
          true,
          true,
          true,
          true
        ],
        [
          false,
          false,
          true,
          true,
          false,
          false,
          true
        ],
        [
          false,
          false,
          false,
          true,
          false,
          false,
          true
        ],
        [
          false,
          false,
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
          false,
          false,
          true
        ]
      ],
      "covers": [
        [
          0,
          1
        ],
        [
          0,
          2
        ],
        [
          1,
          3
        ],
        [
          1,
          4
        ],
        [
          1,
          5
        ],
        [
          2,
          3
        ],
        [
          3,
          6
        ],
        [
          4,
          6
        ],
        [
          5,
          6
        ]
      ],
      "named_targets": []
    },
    {
      "id": "n4-E18975",
      "carrier_size": 4,
      "abstract_type": "T19",
      "name": "Shape T19",
      "partitions": [
        [
          0,
          1,
          2,
          3
        ],
        [
          0,
          1,
          2,
          2
        ],
        [
          0,
          1,
          2,
          1
        ],
        [
          0,
          1,
          1,
          2
        ],
        [
          0,
          1,
          1,
          1
        ],
        [
          0,
          1,
          0,
          0
        ],
        [
          0,
          0,
          1,
          1
        ],
        [
          0,
          0,
          0,
          0
        ]
      ],
      "operations": [
        [
          2,
          3,
          3,
          3
        ]
      ],
      "minimum_unary_operations": 1,
      "orbit_size": 12,
      "order": [
        [
          true,
          true,
          true,
          true,
          true,
          true,
          true,
          true
        ],
        [
          false,
          true,
          false,
          false,
          true,
          true,
          true,
          true
        ],
        [
          false,
          false,
          true,
          false,
          true,
          false,
          false,
          true
        ],
        [
          false,
          false,
          false,
          true,
          true,
          false,
          false,
          true
        ],
        [
          false,
          false,
          false,
          false,
          true,
          false,
          false,
          true
        ],
        [
          false,
          false,
          false,
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
          false,
          false,
          false,
          true
        ]
      ],
      "covers": [
        [
          0,
          1
        ],
        [
          0,
          2
        ],
        [
          0,
          3
        ],
        [
          1,
          4
        ],
        [
          1,
          5
        ],
        [
          1,
          6
        ],
        [
          2,
          4
        ],
        [
          3,
          4
        ],
        [
          4,
          7
        ],
        [
          5,
          7
        ],
        [
          6,
          7
        ]
      ],
      "named_targets": []
    },
    {
      "id": "n4-E19067",
      "carrier_size": 4,
      "abstract_type": "T20",
      "name": "Shape T20",
      "partitions": [
        [
          0,
          1,
          2,
          3
        ],
        [
          0,
          1,
          2,
          2
        ],
        [
          0,
          1,
          1,
          2
        ],
        [
          0,
          1,
          1,
          1
        ],
        [
          0,
          1,
          2,
          0
        ],
        [
          0,
          1,
          1,
          0
        ],
        [
          0,
          1,
          0,
          0
        ],
        [
          0,
          0,
          1,
          1
        ],
        [
          0,
          0,
          0,
          0
        ]
      ],
      "operations": [
        [
          2,
          3,
          3,
          2
        ]
      ],
      "minimum_unary_operations": 1,
      "orbit_size": 12,
      "order": [
        [
          true,
          true,
          true,
          true,
          true,
          true,
          true,
          true,
          true
        ],
        [
          false,
          true,
          false,
          true,
          false,
          false,
          true,
          true,
          true
        ],
        [
          false,
          false,
          true,
          true,
          false,
          true,
          false,
          false,
          true
        ],
        [
          false,
          false,
          false,
          true,
          false,
          false,
          false,
          false,
          true
        ],
        [
          false,
          false,
          false,
          false,
          true,
          true,
          true,
          false,
          true
        ],
        [
          false,
          false,
          false,
          false,
          false,
          true,
          false,
          false,
          true
        ],
        [
          false,
          false,
          false,
          false,
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
          false,
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
          false,
          false,
          false,
          false,
          true
        ]
      ],
      "covers": [
        [
          0,
          1
        ],
        [
          0,
          2
        ],
        [
          0,
          4
        ],
        [
          1,
          3
        ],
        [
          1,
          6
        ],
        [
          1,
          7
        ],
        [
          2,
          3
        ],
        [
          2,
          5
        ],
        [
          3,
          8
        ],
        [
          4,
          5
        ],
        [
          4,
          6
        ],
        [
          5,
          8
        ],
        [
          6,
          8
        ],
        [
          7,
          8
        ]
      ],
      "named_targets": []
    },
    {
      "id": "n4-E19987",
      "carrier_size": 4,
      "abstract_type": "T18",
      "name": "Shape T18",
      "partitions": [
        [
          0,
          1,
          2,
          3
        ],
        [
          0,
          1,
          2,
          2
        ],
        [
          0,
          1,
          1,
          1
        ],
        [
          0,
          1,
          0,
          0
        ],
        [
          0,
          0,
          1,
          2
        ],
        [
          0,
          0,
          1,
          1
        ],
        [
          0,
          0,
          0,
          0
        ]
      ],
      "operations": [
        [
          0,
          1,
          3,
          2
        ]
      ],
      "minimum_unary_operations": 1,
      "orbit_size": 6,
      "order": [
        [
          true,
          true,
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
          true,
          false,
          true,
          true
        ],
        [
          false,
          false,
          true,
          false,
          false,
          false,
          true
        ],
        [
          false,
          false,
          false,
          true,
          false,
          false,
          true
        ],
        [
          false,
          false,
          false,
          false,
          true,
          true,
          true
        ],
        [
          false,
          false,
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
          false,
          false,
          true
        ]
      ],
      "covers": [
        [
          0,
          1
        ],
        [
          0,
          4
        ],
        [
          1,
          2
        ],
        [
          1,
          3
        ],
        [
          1,
          5
        ],
        [
          2,
          6
        ],
        [
          3,
          6
        ],
        [
          4,
          5
        ],
        [
          5,
          6
        ]
      ],
      "named_targets": []
    },
    {
      "id": "n4-E21047",
      "carrier_size": 4,
      "abstract_type": "T15",
      "name": "B3",
      "partitions": [
        [
          0,
          1,
          2,
          3
        ],
        [
          0,
          1,
          2,
          2
        ],
        [
          0,
          1,
          2,
          1
        ],
        [
          0,
          1,
          1,
          1
        ],
        [
          0,
          1,
          2,
          0
        ],
        [
          0,
          1,
          0,
          0
        ],
        [
          0,
          0,
          1,
          0
        ],
        [
          0,
          0,
          0,
          0
        ]
      ],
      "operations": [
        [
          0,
          3,
          3,
          3
        ],
        [
          0,
          3,
          2,
          3
        ]
      ],
      "minimum_unary_operations": 2,
      "orbit_size": 4,
      "order": [
        [
          true,
          true,
          true,
          true,
          true,
          true,
          true,
          true
        ],
        [
          false,
          true,
          false,
          true,
          false,
          true,
          false,
          true
        ],
        [
          false,
          false,
          true,
          true,
          false,
          false,
          true,
          true
        ],
        [
          false,
          false,
          false,
          true,
          false,
          false,
          false,
          true
        ],
        [
          false,
          false,
          false,
          false,
          true,
          true,
          true,
          true
        ],
        [
          false,
          false,
          false,
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
          false,
          false,
          false,
          true
        ]
      ],
      "covers": [
        [
          0,
          1
        ],
        [
          0,
          2
        ],
        [
          0,
          4
        ],
        [
          1,
          3
        ],
        [
          1,
          5
        ],
        [
          2,
          3
        ],
        [
          2,
          6
        ],
        [
          3,
          7
        ],
        [
          4,
          5
        ],
        [
          4,
          6
        ],
        [
          5,
          7
        ],
        [
          6,
          7
        ]
      ],
      "named_targets": [
        "B3"
      ]
    },
    {
      "id": "n4-E21119",
      "carrier_size": 4,
      "abstract_type": "T21",
      "name": "Shape T21",
      "partitions": [
        [
          0,
          1,
          2,
          3
        ],
        [
          0,
          1,
          2,
          2
        ],
        [
          0,
          1,
          2,
          1
        ],
        [
          0,
          1,
          1,
          2
        ],
        [
          0,
          1,
          1,
          1
        ],
        [
          0,
          1,
          2,
          0
        ],
        [
          0,
          1,
          1,
          0
        ],
        [
          0,
          1,
          0,
          0
        ],
        [
          0,
          0,
          1,
          0
        ],
        [
          0,
          0,
          0,
          0
        ]
      ],
      "operations": [
        [
          0,
          3,
          3,
          3
        ]
      ],
      "minimum_unary_operations": 1,
      "orbit_size": 12,
      "order": [
        [
          true,
          true,
          true,
          true,
          true,
          true,
          true,
          true,
          true,
          true
        ],
        [
          false,
          true,
          false,
          false,
          true,
          false,
          false,
          true,
          false,
          true
        ],
        [
          false,
          false,
          true,
          false,
          true,
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
          true,
          true,
          false,
          true,
          false,
          false,
          true
        ],
        [
          false,
          false,
          false,
          false,
          true,
          false,
          false,
          false,
          false,
          true
        ],
        [
          false,
          false,
          false,
          false,
          false,
          true,
          true,
          true,
          true,
          true
        ],
        [
          false,
          false,
          false,
          false,
          false,
          false,
          true,
          false,
          false,
          true
        ],
        [
          false,
          false,
          false,
          false,
          false,
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
          false,
          false,
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
          false,
          false,
          false,
          false,
          false,
          true
        ]
      ],
      "covers": [
        [
          0,
          1
        ],
        [
          0,
          2
        ],
        [
          0,
          3
        ],
        [
          0,
          5
        ],
        [
          1,
          4
        ],
        [
          1,
          7
        ],
        [
          2,
          4
        ],
        [
          2,
          8
        ],
        [
          3,
          4
        ],
        [
          3,
          6
        ],
        [
          4,
          9
        ],
        [
          5,
          6
        ],
        [
          5,
          7
        ],
        [
          5,
          8
        ],
        [
          6,
          9
        ],
        [
          7,
          9
        ],
        [
          8,
          9
        ]
      ],
      "named_targets": []
    },
    {
      "id": "n4-E32767",
      "carrier_size": 4,
      "abstract_type": "T22",
      "name": "Shape T22",
      "partitions": [
        [
          0,
          1,
          2,
          3
        ],
        [
          0,
          1,
          2,
          2
        ],
        [
          0,
          1,
          2,
          1
        ],
        [
          0,
          1,
          1,
          2
        ],
        [
          0,
          1,
          1,
          1
        ],
        [
          0,
          1,
          2,
          0
        ],
        [
          0,
          1,
          1,
          0
        ],
        [
          0,
          1,
          0,
          2
        ],
        [
          0,
          1,
          0,
          1
        ],
        [
          0,
          1,
          0,
          0
        ],
        [
          0,
          0,
          1,
          2
        ],
        [
          0,
          0,
          1,
          1
        ],
        [
          0,
          0,
          1,
          0
        ],
        [
          0,
          0,
          0,
          1
        ],
        [
          0,
          0,
          0,
          0
        ]
      ],
      "operations": [],
      "minimum_unary_operations": 0,
      "orbit_size": 1,
      "order": [
        [
          true,
          true,
          true,
          true,
          true,
          true,
          true,
          true,
          true,
          true,
          true,
          true,
          true,
          true,
          true
        ],
        [
          false,
          true,
          false,
          false,
          true,
          false,
          false,
          false,
          false,
          true,
          false,
          true,
          false,
          false,
          true
        ],
        [
          false,
          false,
          true,
          false,
          true,
          false,
          false,
          false,
          true,
          false,
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
          true,
          false,
          true,
          false,
          false,
          false,
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
          true,
          false,
          false,
          false,
          false,
          false,
          false,
          false,
          false,
          false,
          true
        ],
        [
          false,
          false,
          false,
          false,
          false,
          true,
          true,
          false,
          false,
          true,
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
          false,
          false,
          false,
          true,
          false,
          false,
          false,
          false,
          false,
          false,
          false,
          true
        ],
        [
          false,
          false,
          false,
          false,
          false,
          false,
          false,
          true,
          true,
          true,
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
          false,
          false,
          false,
          false,
          true,
          false,
          false,
          false,
          false,
          false,
          true
        ],
        [
          false,
          false,
          false,
          false,
          false,
          false,
          false,
          false,
          false,
          true,
          false,
          false,
          false,
          false,
          true
        ],
        [
          false,
          false,
          false,
          false,
          false,
          false,
          false,
          false,
          false,
          false,
          true,
          true,
          true,
          true,
          true
        ],
        [
          false,
          false,
          false,
          false,
          false,
          false,
          false,
          false,
          false,
          false,
          false,
          true,
          false,
          false,
          true
        ],
        [
          false,
          false,
          false,
          false,
          false,
          false,
          false,
          false,
          false,
          false,
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
          false,
          false,
          false,
          false,
          false,
          false,
          false,
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
          false,
          false,
          false,
          false,
          false,
          false,
          false,
          false,
          false,
          false,
          true
        ]
      ],
      "covers": [
        [
          0,
          1
        ],
        [
          0,
          2
        ],
        [
          0,
          3
        ],
        [
          0,
          5
        ],
        [
          0,
          7
        ],
        [
          0,
          10
        ],
        [
          1,
          4
        ],
        [
          1,
          9
        ],
        [
          1,
          11
        ],
        [
          2,
          4
        ],
        [
          2,
          8
        ],
        [
          2,
          12
        ],
        [
          3,
          4
        ],
        [
          3,
          6
        ],
        [
          3,
          13
        ],
        [
          4,
          14
        ],
        [
          5,
          6
        ],
        [
          5,
          9
        ],
        [
          5,
          12
        ],
        [
          6,
          14
        ],
        [
          7,
          8
        ],
        [
          7,
          9
        ],
        [
          7,
          13
        ],
        [
          8,
          14
        ],
        [
          9,
          14
        ],
        [
          10,
          11
        ],
        [
          10,
          12
        ],
        [
          10,
          13
        ],
        [
          11,
          14
        ],
        [
          12,
          14
        ],
        [
          13,
          14
        ]
      ],
      "named_targets": []
    }
  ]
};
