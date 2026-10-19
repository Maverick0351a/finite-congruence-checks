# Protecting the verification chain

GitHub branch protection for `main` was enabled and read back on 19 October
2026. Changes must arrive through pull requests whose required checks pass
against the current base. The rules also apply to administrators. Force pushes
and branch deletion are blocked, and review conversations must be resolved.

The [policy file](../.github/main-protection.json) records the applied settings.
It is documentation, not an automatically enforced configuration file; the
GitHub repository setting is authoritative. A maintainer changing either one
must compare it with a fresh API readback.

## Required checks

These nine jobs run unconditionally in [verify.yml](../.github/workflows/verify.yml).
Each required context is bound to the GitHub Actions app ID `15368`:

- Concrete Lean certificates
- Python 3.10 / ubuntu-latest
- Python 3.12 / ubuntu-latest
- Python 3.12 / windows-latest
- Generic grouping checker and native agreement
- Pinned TM configuration agreement
- Upstream N5/B3 witness bridge
- Exact TM pair proof and atlas binding
- N5 renaming proof and atlas binding

Renaming or conditionally skipping a required job needs a corresponding policy
review. A path-filtered preparation workflow is intentionally not required for
every PR: an unrelated change can skip that workflow and leave its required
context pending indefinitely.

Required approving review count is zero so the sole maintainer can merge a checked PR.
PRs, checks and resolved conversations are still required. Independent review
is recorded when performed, but this policy does not assert that a second human
approved a change. Existing merge methods are unchanged.

## Inspect without modifying

```sh
gh api repos/Maverick0351a/finite-congruence-checks/branches/main
gh api repos/Maverick0351a/finite-congruence-checks/branches/main/protection
```

Confirm `protected: true`, strict required checks with all nine app-bound
contexts, administrator enforcement, PR requirements, resolved conversations,
and disabled force pushes/deletions. No destructive push or deletion is needed
to inspect the setting. Repository administrators can change protection later;
this is a workflow safeguard, not an immutable attestation.

GitHub's [branch-protection API](https://docs.github.com/en/rest/branches/branch-protection#update-branch-protection)
documents these settings, including a required approval count of zero.
