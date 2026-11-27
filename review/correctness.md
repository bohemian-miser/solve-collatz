# Rubric 1: Correctness, Soundness & Trust Boundary

## Mission
Ensure the PR preserves the mathematical integrity of `Challenge.lean` and adds zero unsoundness, axiom leakage, or hidden escape hatches.

## Mandatory Checks

1. **Frozen Challenge & Verification Files (`[S0]`)**
   - Every file listed in `problem.toml` (`[guards].frozen_files`, including `Challenge.lean`, `scripts/PrintAxioms.lean`, and `.github/workflows/*.yml`) MUST be untouched — verify via `python3 scripts/check_challenge_frozen.py <base_ref> <head_ref>`.
   - Any theorem claiming to prove the conjecture or its disproof MUST reference the exact frozen declarations in `problem.toml` (`conjecture_decl` / `disproof_decl`) — never a local redefinition.
2. **Axiom Audit (`[S0]`)**
   - Every exported theorem must depend ONLY on Lean's standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`).
   - Reject ANY occurrence of `sorry`, `admit`, `axiom`, `native_decide`, `Lean.ofReduceBool`, `Lean.trustCompiler`, `implemented_by`, `extern`, `unsafe`, `partial` in proofs, or metaprogramming escape hatches.
3. **Vacuity & Type-Signature Traps (`[S0]`)**
   - Check every `theorem` and `structure` for silently vacuous hypotheses (e.g., `Nat` subtraction truncating to `0`, contradictory typeclass assumptions, unintended edge cases, or trivial degenerate witnesses).
   - For Track B (`Disprove/`), verify that every certificate genuinely satisfies all preconditions required to imply the frozen `Disproof` statement.
4. **Compiler & Warning Hygiene (`[S0]`/`[S1]`)**
   - `lake build` must succeed with `warningAsError = true` (zero warnings, zero `set_option` suppressions or `maxHeartbeats` overrides).
5. **Cross-Track Isolation (`[S1]`)**
   - Track A (`Prove/`) and Track B (`Disprove/`) must stay cleanly decoupled via `Challenge.lean` and `Core/`. No speculative axioms from one track leaking into `Core/` or `Known/`.

## Output Format
List findings tagged `[S0]`, `[S1]`, or `[S2]` with exact `file:line` references, plus a binary verdict: `PASS` or `REQUEST CHANGES`.
