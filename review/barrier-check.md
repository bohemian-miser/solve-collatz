# Rubric 3: Known-Barrier Red-Teaming

## Mission
Open conjectures accumulate graveyards of approaches that accidentally prove too much — arguments that would ALSO apply to closely related variants where the conjecture is **known to be false**, or heuristic claims that ignore density, domain-boundary, local-vs-global, or computability obstructions.

This rubric enforces an explicit **5-tier barrier check** against `frontier/BARRIERS.md` and `frontier/REFUTED.md` on every Track A strategy and Track B heuristic claim.

## Mandatory Checks

1. **Five-Tier Barrier Survival Test (`[S0]` for Track A strategy claims)**
   - Read `frontier/BARRIERS.md` and any formalized barrier counterexamples in `<LeanRoot>/Core/`.
   - Audit EVERY Track A lemma or strategy claiming progress toward `Conjecture` against all five barrier tiers:
     - **B1 (Perturbed-Problem Variants):** Does the argument break on every known false parameter/sign/coefficient variant?
     - **B2 (Density / Probabilistic-vs-Universal):** If using almost-all, ergodic, or heuristic bounds, does it genuinely rule out zero-density exceptional sets?
     - **B3 (Domain-Boundary / Sign / Completion):** Does it explicitly use positivity, integrality, or boundary constraints that fail on enlarged domains?
     - **B4 (Local-vs-Global / Completion):** Does it go beyond purely local modular, `p`-adic, or finite-automaton obstructions?
     - **B5 (Computability / Finite-Horizon):** Does it avoid generic schemas that would apply to known undecidable generalizations?
   - Reject any argument whose hypotheses hold verbatim on a known false barrier variant.
2. **Negative Knowledge Base Check (`[S0]`/`[S1]`)**
   - Read `frontier/REFUTED.md`. Verify the PR is not repeating an already-refuted approach without explicitly fixing the falsified hypothesis and citing the prior `REF-*` entry.
3. **Automated Red-Team & Search Hook (`[S1]`)**
   - Verify `bash search/ci_checks.sh` passes cleanly (including strict JSON & `deterministic_sha256` verification via `search/verify_json_artifacts.py`).
   - If the PR proposes a new invariant, bound, or heuristic, require extending the problem's red-team script to stress-test it against barrier variants.
4. **Track B Search Realism (`[S1]`)**
   - For Track B (`Disprove/` and `search/`), verify that searches respect published computational lower bounds, emit deterministic strict RFC-8259 JSON artifacts, and target structured danger zones rather than redundant naive brute force.

## Output Format
Report a tier-by-tier disposition (`B1`–`B5`: `CLEARS` / `FAILS` / `N/A` with justification), tag findings `[S0]`/`[S1]`/`[S2]`, and emit `PASS` or `REQUEST CHANGES`.
