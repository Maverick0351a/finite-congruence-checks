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

1. **External replication.** Ask a researcher to run a tagged release in a fresh
   environment and review one certificate against the mathematical definition.
   Success: an independently reported result with exact versions and commands.
2. **Explore all minimum-carrier embeddings.** Extend operation minimization
   beyond the single saved embedding per lattice. Check prior literature before
   presenting any improved bound or classification as new.
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
lets readers select a lattice, inspect its colored graph and unary operations,
compare passing and failing examples, and download the corresponding certificate.
GitHub remains the source of record for code, proofs, and versioned evidence.
The demo displays precomputed results with their exact scope and reproduction
commands. Browsing it does not rerun the search or check a Lean proof.
See [the demo maintenance record](HUGGING_FACE_DEMO.md).
