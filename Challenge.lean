/-
Copyright (c) 2026 The solve-collatz contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# Frozen Challenge Statements for `solve-collatz`

This file is **FROZEN** and human-owned. Automated CI rejects any PR that modifies it.

Both tracks of `solve-collatz` target the exact statements below, using ONLY Lean core
definitions (`Nat`) with zero Mathlib or external-library dependencies so any human or
independent kernel checker can verify the statements by inspection in 10 seconds.

* **Track A (`Collatz/Prove/`):** Prove `SolveCollatz.CollatzConjecture`.
* **Track B (`Collatz/Disprove/`):** Prove `SolveCollatz.CollatzDisproof` (equivalently, exhibit a
  non-trivial positive cycle or a divergent positive orbit).
-/

@[expose] public section

namespace SolveCollatz

/-- One step of the standard Collatz map on `ℕ`: `n / 2` if `n` is even, `3 * n + 1` if odd. -/
def collatzStep (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- The `k`-th iterate of `collatzStep` starting from `n`. -/
def collatzIter : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => collatzIter k (collatzStep n)

/-- **The Collatz Conjecture (Track A target):** every positive integer eventually reaches `1`. -/
def CollatzConjecture : Prop :=
  ∀ n : Nat, 0 < n → ∃ k : Nat, collatzIter k n = 1

/-- **Disproof of the Collatz Conjecture (Track B target):** negation of `CollatzConjecture`. -/
def CollatzDisproof : Prop :=
  ¬ CollatzConjecture

/-- A positive integer `n` lies on a non-trivial cycle if it returns to `n` in `k > 0` steps
without ever visiting `1`, `2`, or `4`. -/
def HasNontrivialCycle : Prop :=
  ∃ n k : Nat, 0 < n ∧ 0 < k ∧ collatzIter k n = n ∧ ∀ j : Nat, j < k → collatzIter j n ≠ 1

/-- A positive integer `n` has a divergent orbit if its trajectory is unbounded. -/
def HasDivergentOrbit : Prop :=
  ∃ n : Nat, 0 < n ∧ ∀ B : Nat, ∃ k : Nat, B < collatzIter k n

end SolveCollatz
