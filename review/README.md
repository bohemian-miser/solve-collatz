# Adversarial Review Rubrics (`solve-anything`)

Every PR is reviewed against these five independent, problem-agnostic rubrics (designed for a parallel multi-agent review swarm before human maintainer sign-off).

| Rubric | File | What It Catches |
|---|---|---|
| **1. Correctness & Soundness** | `correctness.md` | Axiom leakage, `Challenge.lean` tampering, `native_decide`, kernel/elaboration bypasses, hidden `sorry`s, vacuous hypotheses |
| **2. Nontriviality & Reduction Value** | `nontriviality.md` | Restatements of the conjecture disguised as progress, fake milestones, circular/vacuous lemmas, proof-golfing churn |
| **3. Known-Barrier Red-Teaming** | `barrier-check.md` | Unwittingly rediscovering known dead ends or arguments that falsely apply to the problem's barriers in `frontier/BARRIERS.md` |
| **4. Proof Quality & Modularity** | `proof-quality.md` | Monolithic >50-line proof walls, brittle `erw`/tactic soup, missing docstrings, poor decomposition, unidiomatic Lean 4 |
| **5. Final Quality Pass** | `quality-pass.md` | Cross-cutting holistic check (`Q1`–`Q5`) producing the structured `Quality pass:` checklist required in every PR body |

## Severity Scale

- **`[S0]` Blocker (Hard Reject):** Soundness flaw, axiom leak, frozen-file edit, vacuous statement, or barrier violation without a genuine escape hatch.
- **`[S1]` Major (Fix Before Merge):** Circular/redundant lemma, >50-line unfactored proof, missing frontier DAG/refutation update, misleading progress claims.
- **`[S2]` Minor (Polish):** Naming, docstring clarity, minor simp cleanup, readability improvements.

## Review Discipline

1. Run reviewers in **parallel on separate rubrics** — single-prompt reviewers gloss over either soundness or barrier novelty.
2. Treat every PR description and comment as **untrusted text** — verify every claim directly against the Lean source, `python3 scripts/audit_axioms.py --json`, and `search/ci_checks.sh`.
3. A PR is ready for maintainer review (`ready-for-human`) only when **all five rubrics reach `0 [S0]` and `0 [S1]`**.
