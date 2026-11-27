/-
Copyright (c) 2026 The solve-collatz contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# Formalized Barrier Counterexamples (`3n - 1`, `5n + 1`, and `ℤ_{<0}`)

Any Track A (`Prove/`) argument for the Collatz conjecture (`3n + 1` on `ℕ⁺`) **must** fail when
applied to `3n - 1` on `ℕ⁺`, `5n + 1` on `ℕ⁺`, or `3n + 1` on `ℤ_{<0}`, because all three admit
explicit non-trivial cycles proved directly in Lean below.

These kernel-checked counterexamples anchor `frontier/BARRIERS.md` and `review/barrier-check.md`.
-/

@[expose] public section

namespace SolveCollatz.Barriers

/-- Generalized integer Collatz map `T_{a, b}(n) = n / 2` if even, `a * n + b` if odd. -/
def genStep (a b n : Int) : Int :=
  if n % 2 = 0 then n / 2 else a * n + b

/-- `k`-th iterate of `genStep a b`. -/
def genIter (a b : Int) : Nat → Int → Int
  | 0, n => n
  | k + 1, n => genIter a b k (genStep a b n)

/-- **Barrier 1 (`3n - 1` on `ℕ⁺`):** `5 → 14 → 7 → 20 → 10 → 5` is a 5-step positive cycle
avoiding `1`. -/
theorem three_n_minus_one_cycle_5 :
    genIter 3 (-1) 5 5 = 5 ∧ ∀ j : Nat, j < 5 → genIter 3 (-1) j 5 ≠ 1 := by
  refine ⟨by decide, fun j hj => ?_⟩
  match j, hj with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | 4, _ => decide

/-- **Barrier 2 (`5n + 1` on `ℕ⁺`):** `13 → 66 → 33 → 166 → 83 → 416 → 208 → 104 → 52 → 26 → 13`
is a 10-step positive cycle avoiding `1`. -/
theorem five_n_plus_one_cycle_13 :
    genIter 5 1 10 13 = 13 ∧ ∀ j : Nat, j < 10 → genIter 5 1 j 13 ≠ 1 := by
  refine ⟨by decide, fun j hj => ?_⟩
  match j, hj with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | 4, _ => decide
  | 5, _ => decide
  | 6, _ => decide
  | 7, _ => decide
  | 8, _ => decide
  | 9, _ => decide

/-- **Barrier 3 (`3n + 1` on `ℤ_{<0}`):** `-5 → -14 → -7 → -20 → -10 → -5` is a 5-step negative
cycle avoiding `1` and `-1`. -/
theorem neg_int_cycle_neg5 :
    genIter 3 1 5 (-5) = -5 ∧ ∀ j : Nat, j < 5 → genIter 3 1 j (-5) ≠ 1 := by
  refine ⟨by decide, fun j hj => ?_⟩
  match j, hj with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | 4, _ => decide

end SolveCollatz.Barriers
