# Rubric 5: Holistic Final Quality Pass (`Q1`–`Q5`)

## Mission
Perform a final end-to-end synthesis before maintainer submission, producing the exact 5-question **`Quality pass:`** block required in every PR description.

## The Five Questions

- **Q1 (Trust & Soundness):** Are all frozen files in `problem.toml` untouched (`scripts/check_challenge_frozen.py`), does `lake build` pass with zero warnings, and does `scripts/audit_axioms.py` show ONLY `[propext, Classical.choice, Quot.sound]` with zero `sorry`/`native_decide`/`unsafe`?
- **Q2 (Frontier Impact):** Which exact `frontier/FRONTIER.toml` node(s) does this PR advance, close, or refute, and is the mathematical delta genuine (not a tautological restatement)?
- **Q3 (Barrier Check):** For Track A strategies, how does the argument survive every relevant barrier in `frontier/BARRIERS.md` (and did `search/ci_checks.sh` pass)? For Track B / Known / Core, is the scope grounded in known bounds?
- **Q4 (Decomposition & Readability):** Are all proofs <= 50 lines, modular, well-documented, free of brittle tactic debt, and reusable by downstream agents?
- **Q5 (Swarm Hygiene):** Are `frontier/FRONTIER.toml`, `frontier/REFUTED.md` (if negative result), alphabetical root barrel imports, claims, and tests cleanly updated with zero committed binaries (`scripts/native_cache.py` `/tmp` cache for native tools) and zero unrelated diff noise?

## Required PR Block Template

```markdown
Quality pass:
- Q1 (Trust & Soundness): PASS — Frozen files untouched; `lake build` 0 warnings; `scripts/audit_axioms.py` standard axioms only.
- Q2 (Frontier Impact): PASS — Advances/closes `<node-id>` by proving `<theorem>`.
- Q3 (Barrier Check): PASS — `<explicit explanation against frontier/BARRIERS.md, or N/A for Core/Disprove cert>`.
- Q4 (Decomposition & Readability): PASS — Max proof length `<N>` lines; `check_source_guards.py` passes; docstrings added.
- Q5 (Swarm Hygiene): PASS — Frontier metadata updated; minimal scoped diff; CI checks pass locally.
```
