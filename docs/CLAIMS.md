# Claim ledger

Each claim below has a specific scope and an inspectable record. A green check
for one row does not establish a stronger claim from another row.

| Claim | Evidence | Scope |
|:--|:--|:--|
| Every selected coloring was enumerated | `evidence/search-results.json` | Eight named lattices; carrier sizes 1–4; 143,685 labeled candidates |
| A separate implementation agrees | `evidence/independent-review-results.json` | All 32 lattice/size rows, rejection counts, 217 witnesses and 22 vertex classes |
| Seven saved graphs satisfy the finite predicate | Seven `*.verification.json` files | Literal nonempty ordered seed sets, including loops; all total self-maps |
| Seven explicit algebras have the target congruence lattices | `evidence/verified-algebras.json` | All partitions and admissible unary maps on the saved finite carriers |
| Positive examples attain minimum carrier sizes | `METHOD.md`, search and algebra records | The attained size equals the elementary chain-height lower bound |
| Minimum unary operation counts are 0,1,1,1,0,2,2 | `evidence/minimized-algebras.json` | C2,C3,C4,B2,M3,N5,B3; fixed carriers and exact saved relation families |
| The minimizer agrees with a third exhaustive method | `evidence/operation-minima-audit.json` | All 313 representable exact relation families on carriers 1–4; 60 impossible controls |
| M4 has no graph witness in the searched range | Search and replay records | At most four carrier vertices; larger carriers are outside this claim |
| Concrete examples have additional formal checks | [Lean verification record](LEAN_VERIFICATION.md) | Read the exact theorem statements and compilation status there |

No claim of a new mathematical theorem or classification is made. These small
lattices are control examples. The negative M4 result is bounded. The project
does not verify all of OpenAI's math corpus, nor the undecidability or subgroup
interval conclusions explicitly outside family 206's selected formalization.

The upstream comparator is a specification file ending in an intentional
`sorry`; the actual upstream solution lives in a separate module. A source
inspection, Lean compilation, axiom inspection, and comparator run are different
checks. Their individual status belongs in LEAN_VERIFICATION.md.

AI-assisted review and multiple independent algorithms provide useful assurance.
They do not establish Python implementation correctness by formal proof or count
as outside peer review. Novelty would require a separate literature investigation.
