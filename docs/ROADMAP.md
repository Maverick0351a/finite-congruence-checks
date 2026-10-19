# Research and engineering roadmap

## The first release

Reproduce the complete eight-lattice search through four carrier vertices,
preserve certificates and all rejection counts, independently verify the
congruences and operation minima, and provide inspectable charts and Lean checks.
The exact delivered verification boundary is in LEAN_VERIFICATION.md.

## Highest-value follow-ups

1. **External replication.** Ask a researcher to run a tagged release in a fresh
   environment and review one certificate against the mathematical definition.
   Success: an independently reported result with exact versions and commands.
2. **Complete the formal connection.** Connect concrete witnesses to the exact
   upstream predicate and check the upstream comparator workflow. Keep core Lean
   proofs, upstream compilation, and comparator success as separate statuses.
3. **Explore all minimum-carrier embeddings.** Extend operation minimization
   beyond the single saved embedding per lattice. Check prior literature before
   presenting any improved bound or classification as new.
4. **Add harder targets deliberately.** Define a mathematically motivated target
   and resource budget, estimate the search space, and save verifiable witnesses.
   Search beyond four vertices requires algorithm changes: the literal verifier
   has exponentially many seed subsets.
5. **Export richer certificates.** Emit proof objects for rejection reasons and
   compact operation choices so verification can remain small as search grows.

## Release and visibility

This repository starts private. A public release should include a successful CI
run, tagged source, checked archive, a short walkthrough, and the precise claims
in CLAIMS.md. The prepared announcement is a draft; no outreach is automated.
An upstream contribution depends on the maintainers' process and acceptance.

After a public release, an optional static Hugging Face Space could let readers
select a saved lattice, inspect its colored graph and unary operations, and open
the corresponding certificate. GitHub would remain the source of record for
code, proofs, and versioned evidence. A demo should display precomputed results
with their exact scope and link to reproduction commands; it should not imply
that browsing the visualization reruns the search or checks a Lean proof.
