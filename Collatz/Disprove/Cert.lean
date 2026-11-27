/-
Copyright (c) 2026 The solve-collatz contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Collatz.Core.Basic

/-!
# Formal Counterexample Certificate Verifier (Track B: `Disprove/`)

Any high-speed search engine (Python, Rust, GPU, SAT/SMT) in `search/` that discovers a candidate
non-trivial Collatz cycle `(n, k)` can emit a `NontrivialCycleCert`. Checking `cert.check = true`
via Lean's kernel immediately constructs a kernel-verified proof of `SolveCollatz.CollatzDisproof`
with zero `sorry` and standard axioms only.
-/

@[expose] public section

namespace SolveCollatz.Disprove

/-- Boolean check that none of `collatzIter 0 n, …, collatzIter (k - 1) n` equals `1`. -/
def avoidsOneLoop : Nat → Nat → Bool
  | 0, _ => true
  | k + 1, cur => (cur != 1) && avoidsOneLoop k (collatzStep cur)

/-- Soundness of `avoidsOneLoop`. -/
theorem avoidsOneLoop_sound (k cur : Nat) (h : avoidsOneLoop k cur = true) :
    ∀ j : Nat, j < k → collatzIter j cur ≠ 1 := by
  induction k generalizing cur with
  | zero => intro j hj; exact absurd hj (Nat.not_lt_zero j)
  | succ k ih =>
    simp only [avoidsOneLoop, Bool.and_eq_true, bne_iff_ne] at h
    intro j hj
    cases j with
    | zero => exact h.1
    | succ j => exact ih (collatzStep cur) h.2 j (Nat.lt_of_succ_lt_succ hj)

/-- A compact, self-contained certificate for a non-trivial positive Collatz cycle. -/
structure NontrivialCycleCert where
  /-- Starting positive integer `n`. -/
  start : Nat
  /-- Positive cycle length `k`. -/
  period : Nat
  /-- Witness that `0 < start`. -/
  start_pos : 0 < start
  /-- Witness that `0 < period`. -/
  period_pos : 0 < period
  /-- Witness that `collatzIter period start = start`. -/
  returns : collatzIter period start = start
  /-- Witness that no iterate in `[0, period)` hits `1`. -/
  avoids_one : avoidsOneLoop period start = true

/-- **Main Track B Certificate Theorem:** any valid `NontrivialCycleCert` proves
`SolveCollatz.CollatzDisproof`. -/
theorem NontrivialCycleCert.disproves_collatz (c : NontrivialCycleCert) : CollatzDisproof :=
  collatzDisproof_of_hasNontrivialCycle
    ⟨c.start, c.period, c.start_pos, c.period_pos, c.returns,
      avoidsOneLoop_sound c.period c.start c.avoids_one⟩

end SolveCollatz.Disprove
