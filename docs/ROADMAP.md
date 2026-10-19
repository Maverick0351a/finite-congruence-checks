# Research and engineering roadmap

## The first release

Reproduce the complete eight-lattice search through four carrier vertices,
preserve certificates and all rejection counts, independently verify the
congruences and operation minima, and provide inspectable charts and Lean checks.
The exact delivered verification boundary is in LEAN_VERIFICATION.md.

## Completed formal bridge

The exact saved N5/B3 graphs now satisfy upstream `IsGraphWitness` in Lean.
Their generated tables, congruence classifications, lattice instances, and
principal-color equalities are checked together by a reproducible runner and
CI job. The original upstream theorem also passed its official comparator,
including two rejection controls. [Proofs and recorded checks](LEAN_VERIFICATION.md).

## Highest-value follow-ups

The engineering direction is an [evidence interface for people and agents](INFRASTRUCTURE.md).
Versioned JSON, stable entry identities, claim-level evidence, and a local query
tool provide the first contract. The Cytoscape map exposes the same records
visually. Expand the interface only after retrieval tests show that agents can
answer with correct citations and limits. Remote services and databases should
follow demonstrated consumer needs.

The [four-object checker](GROUPING_CHECKER.md) implements the first steps of the
[certificate-checking foundation](CHECKER_FOUNDATION.md): source proofs for
decoding, acceptance, and returned counterexamples; an exhaustive native
comparison runner; and a proposal/repair demo with individual evidence records.
The first [constrained agent repair pilot](REPAIR_BENCHMARK.md) permits merges
only, retains a required separation, and includes impossible cases. Both feedback
arms scored 12/12 on the locally held-out tasks, so this pilot demonstrated the
connection and scoring process without establishing a feedback advantage. Next,
specify a six-object experiment with more possible conflicts and extend the
checker assurance to match before running it. Machine-code refinement remains
a separate research direction. Extend to exact congruence families only with
explicit completeness obligations.

## Next milestones: feedback and translation evidence

[PR #6](https://github.com/Maverick0351a/finite-congruence-checks/pull/6) is merged.
Its scanner incident was a dummy test marker, classified as “Not a secret” in
GitGuardian; the rerun passed before merging. No scanner bypass was required.

Keep the completed grouping checker as the foundation and pursue two bounded
tracks described in the [second-domain pilot proposal](TM_HALT_PILOT.md):

1. **Harder repair feedback.** Specify six objects, merges only, a required
   separation, and exactly two final groups; include multiple-conflict and
   impossible cases. Extend checker assurance to the new interface, independently
   validate the oracle, then freeze a fair feedback comparison before running it.
2. **Two Turing-machine halt behaviors.** Pin the source definitions, construct
   a tiny missing-instruction/write-and-halt pair, and connect traces and an
   English explanation to Lean proofs of exact observations. Agreement on
   halting must not be presented as agreement on the final tape.

The [archive review](ARCHIVE_REVIEW.md) sets evidence-admission requirements.
Treat `formal-audit` as lexical screening: dependencies supporting proof claims
must come from elaborated Lean declarations. Keep the older 616-row Snaky
comparator certificate separate from the 728-card theorem certificate. Every
record must identify its exact source, object, certificate, and claim.
The TM Python benchmark was not rerun in this archive review; older local run
logs are separate historical evidence. Neither those logs nor the proposal
establish general translation correctness. No general Lean translator,
universal verification, or verified fluid simulation is claimed.

## Continuing the finite atlas

The [readable atlas](ATLAS.md) now develops the classification direction through
four objects, with complete relation-family coverage, minimum operations for
each representative, and a C4 comparison. This extends the exploration beyond
one saved embedding per target. The following research steps build on it.

1. **External replication.** Ask a researcher to run a tagged release in a fresh
   environment and review one certificate against the mathematical definition.
   Success: an independently reported result with exact versions and commands.
2. **Extend the atlas deliberately.** Independently review the five-point pilot,
   improved constructions, and the known six-point M4 benchmark before adding
   them to the published catalog. Check prior literature before presenting any
   improved bound or classification as new. Test narrowly stated conjectures
   against the catalog and save counterexamples as well as positive evidence.
3. **Extend formal coverage.** Add the remaining saved positive examples to the
   concrete bridge. Separately investigate a general correctness proof relating
   the verifier's connectivity algorithm to upstream `Relation.EqvGen`; the
   existing concrete proofs do not establish Python implementation correctness.
4. **Add harder targets deliberately.** Define a mathematically motivated target
   and resource budget, estimate the search space, and save verifiable witnesses.
   Search beyond four vertices requires algorithm changes: the literal verifier
   has exponentially many seed subsets.
5. **Export richer certificates.** Emit proof objects for rejection reasons and
   compact operation choices so verification can remain small as search grows.

## Release and visibility

The repository became public on 18 October 2026 after successful CI runs and
preparation of tagged source, a checked archive, a short walkthrough, and precise
claims in CLAIMS.md. The prepared announcement remains a draft; no outreach is automated.
An upstream contribution depends on the maintainers' process and acceptance.

The [static Hugging Face explorer](https://huggingface.co/spaces/Maverick03511/finite-congruence-checks)
opens the readable atlas, with an illustrated lesson and a catalog of constructions.
The linked original graph explorer lets readers inspect colored graphs, compare
passing and failing examples, and download the corresponding certificate.
GitHub remains the source of record for code, proofs, and versioned evidence.
The demo displays precomputed results with their exact scope and reproduction
commands. Browsing it does not rerun the search or check a Lean proof.
See [the demo maintenance record](HUGGING_FACE_DEMO.md).
