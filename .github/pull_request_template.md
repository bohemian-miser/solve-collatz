## Summary

<!-- Describe what this PR proves, disproves, formalizes, or refutes in 2–4 crisp sentences. -->

- **Track:** <!-- Core | Known | Track A (Prove) | Track B (Disprove) | Search / Tooling | Negative Result (REFUTED) -->
- **Frontier node(s):** <!-- e.g., CORE-001, KNOWN-001, PROVE-A1, DISPROVE-002, or NEW -->
- **Main Lean declaration(s):** <!-- exact theorem / def names -->

## Barrier & Nontriviality Check

<!-- For Track A (Prove) PRs: explicitly explain how this argument avoids every barrier in `frontier/BARRIERS.md` (or why this lemma is a pure foundational building block). -->
<!-- For Track B (Disprove) PRs: specify the counterexample certificate or search bounds and reproducibility parameters. -->

## Verification

- [ ] `python3 scripts/check_challenge_frozen.py origin/main HEAD`
- [ ] `python3 scripts/check_source_guards.py`
- [ ] `lake build` (zero errors, zero warnings)
- [ ] `python3 scripts/check_all.py` passes (same steps as CI)
- [ ] `bash search/ci_checks.sh` (problem-specific barrier & search hook)
- [ ] `frontier/FRONTIER.toml` and/or `frontier/REFUTED.md` updated if applicable

## Quality pass

<!-- Fill out after completing the 5 rubrics in review/ -->
Quality pass:
- Q1 (Trust & Soundness):
- Q2 (Frontier Impact):
- Q3 (Barrier Check):
- Q4 (Decomposition & Readability):
- Q5 (Swarm Hygiene):
