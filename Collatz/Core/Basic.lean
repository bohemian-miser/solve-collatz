/-
Copyright (c) 2026 The solve-collatz contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Challenge

/-!
# Core Collatz Dynamics & Dichotomy

Shared core lemmas used by **both** Track A (`Collatz/Prove/`) and Track B (`Collatz/Disprove/`):
- Basic properties of `collatzIter` (addition law, positivity preservation, the trivial cycle
  `1 → 4 → 2 → 1`).
- **Disproof equivalence:** any non-trivial cycle (`HasNontrivialCycle`) or divergent orbit
  (`HasDivergentOrbit`) immediately implies `CollatzDisproof`.
-/

public section

namespace SolveCollatz

/-- Iterating `k` times and then `m` times equals iterating `k + m` times. -/
theorem collatzIter_add (k m n : Nat) :
    collatzIter m (collatzIter k n) = collatzIter (k + m) n := by
  induction k generalizing n with
  | zero => simp [collatzIter]
  | succ k ih =>
    simp only [collatzIter, Nat.succ_add]
    exact ih (collatzStep n)

/-- `collatzStep` preserves positivity (`0 < n → 0 < collatzStep n`). -/
theorem collatzStep_pos {n : Nat} (hn : 0 < n) : 0 < collatzStep n := by
  unfold collatzStep
  split
  · omega
  · omega

/-- Every iterate of a positive integer remains positive. -/
theorem collatzIter_pos (k : Nat) {n : Nat} (hn : 0 < n) : 0 < collatzIter k n := by
  induction k generalizing n with
  | zero => exact hn
  | succ k ih => exact ih (collatzStep_pos hn)

/-- The trivial cycle `1 → 4 → 2 → 1` has period `3`. -/
theorem collatzIter_three_one : collatzIter 3 1 = 1 := rfl

/-- If `collatzIter k n = n` with `0 < k`, then `collatzIter m n = collatzIter (m % k) n`. -/
theorem collatzIter_mod_of_cycle {n k : Nat} (hk : 0 < k) (hcyc : collatzIter k n = n) (m : Nat) :
    collatzIter m n = collatzIter (m % k) n := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    by_cases hm : m < k
    · rw [Nat.mod_eq_of_lt hm]
    · have hge : k ≤ m := Nat.le_of_not_lt hm
      have hstep : collatzIter m n = collatzIter (m - k) n := by
        calc collatzIter m n
            = collatzIter (k + (m - k)) n := by rw [Nat.add_sub_of_le hge]
          _ = collatzIter (m - k) (collatzIter k n) := (collatzIter_add k (m - k) n).symm
          _ = collatzIter (m - k) n := by rw [hcyc]
      rw [hstep, ih (m - k) (by omega), Nat.mod_eq_sub_mod hge]

/-- Once an orbit reaches `1`, every subsequent iterate stays in `{1, 2, 4}` (bounded by `4`). -/
theorem collatzIter_one_le_four (j : Nat) : collatzIter j 1 ≤ 4 := by
  rw [collatzIter_mod_of_cycle (by decide : 0 < 3) collatzIter_three_one j]
  have hlt : j % 3 < 3 := Nat.mod_lt j (by decide)
  match h : j % 3, hlt with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide

/-- **Bridge Lemma (Track B — Cycles):** any non-trivial cycle disproves the Collatz conjecture. -/
theorem collatzDisproof_of_hasNontrivialCycle (h : HasNontrivialCycle) : CollatzDisproof := by
  intro hconj
  rcases h with ⟨n, k, hn, hk, hcyc, hne⟩
  rcases hconj n hn with ⟨m, hm⟩
  have hmod := collatzIter_mod_of_cycle hk hcyc m
  rw [hm] at hmod
  exact hne (m % k) (Nat.mod_lt m hk) hmod.symm

/-- **Bridge Lemma (Track B — Divergence):** any divergent orbit disproves
the Collatz conjecture. -/
theorem collatzDisproof_of_hasDivergentOrbit (h : HasDivergentOrbit) : CollatzDisproof := by
  intro hconj
  rcases h with ⟨n, hn, hdiv⟩
  rcases hconj n hn with ⟨k₀, hk₀⟩
  -- Bound the first `k₀` steps explicitly; after `k₀` the orbit stays `≤ 4`.
  suffices hbd : ∃ B : Nat, ∀ m : Nat, collatzIter m n ≤ B by
    rcases hbd with ⟨B, hB⟩
    rcases hdiv B with ⟨m, hm⟩
    exact Nat.not_lt_of_ge (hB m) hm
  have hfin : ∀ N : Nat, ∃ B : Nat, ∀ m : Nat, m ≤ N → collatzIter m n ≤ B := by
    intro N
    induction N with
    | zero =>
      exact ⟨n, fun m hm => by rw [Nat.eq_zero_of_le_zero hm]; exact Nat.le_refl n⟩
    | succ N ih =>
      rcases ih with ⟨B, hB⟩
      refine ⟨max B (collatzIter (N + 1) n), fun m hm => ?_⟩
      by_cases hle : m ≤ N
      · exact Nat.le_trans (hB m hle) (Nat.le_max_left _ _)
      · have heq : m = N + 1 := by omega
        subst heq
        exact Nat.le_max_right _ _
  rcases hfin k₀ with ⟨B₀, hB₀⟩
  refine ⟨max B₀ 4, fun m => ?_⟩
  by_cases hm : m ≤ k₀
  · exact Nat.le_trans (hB₀ m hm) (Nat.le_max_left _ _)
  · have hge : k₀ ≤ m := Nat.le_of_not_lt (fun hlt => hm (Nat.le_of_lt hlt))
    have hstep : collatzIter m n = collatzIter (m - k₀) 1 := by
      calc collatzIter m n
          = collatzIter (k₀ + (m - k₀)) n := by rw [Nat.add_sub_of_le hge]
        _ = collatzIter (m - k₀) (collatzIter k₀ n) := (collatzIter_add k₀ (m - k₀) n).symm
        _ = collatzIter (m - k₀) 1 := by rw [hk₀]
    rw [hstep]
    exact Nat.le_trans (collatzIter_one_le_four (m - k₀)) (Nat.le_max_right _ _)

end SolveCollatz
