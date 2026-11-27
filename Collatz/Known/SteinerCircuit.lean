/-
Copyright (c) 2026 The solve-collatz contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Collatz.Core.Syracuse

/-!
# Steiner (1977) 1-Circuit Equation & Bounded 1-Cycle Elimination (`KNOWN-002`)

Formalization of the algebraic, Diophantine, and bounded-elimination core of:
R. P. Steiner (1977), *A theorem on the syracuse problem*, Proceedings of the 7th Manitoba
Conference on Numerical Mathematics and Computing, pp. 553–559.

Main results (pure Lean 4 core, zero Mathlib):
1. Canonical 1-circuit parity vector `oneCircuitVec m e = List.replicate m 1 ++ [e]` (representing
   `k = m + 1` odd Syracuse steps with `m` initial unit halvings followed by `e` halvings, total
   halvings `S = m + e`) and closed-form numerator identity
   `parityOffset (oneCircuitVec m e) = 3 ^ (m + 1) - 2 ^ (m + 1)`.
2. Steiner's 1-circuit cycle equation
   `(2 ^ (m + e) - 3 ^ (m + 1)) * n = 3 ^ (m + 1) - 2 ^ (m + 1)`, exact divisibility equivalence
   `(2 ^ (m + e) - 3 ^ (m + 1)) ∣ (3 ^ (m + 1) - 2 ^ (m + 1)) ↔`
   `(2 ^ (m + e) - 3 ^ (m + 1)) ∣ (2 ^ (e - 1) - 1)` (certifying `search/cycle_hunter.py`),
   2-adic congruence `2 ^ (m + 1) ∣ n + 1`, and exponential Diophantine upper bound
   `2 ^ (m + 1) * (2 ^ (m + e) - 3 ^ (m + 1)) < 2 ^ (m + e)`.
3. Steiner's gap bound `2 ^ (m + e) - 3 ^ (m + 1) < (3 ^ (m + 1) - 2 ^ (m + 1)) / 2` and
   `2 ^ (m + e) < 2 * 3 ^ (m + 1)` for non-trivial 1-circuits (`1 < n`), proving that ONLY the
   unique minimal exponent `S = minHalvings (m + 1)` can host a non-trivial 1-circuit.
4. Kernel-verified elimination of all non-trivial 1-circuits for `1 ≤ k ≤ 20` (zero
   `native_decide`) and the conditional Steiner reduction
   `no_nontrivial_oneCircuit_of_diophantine_bound`, leaving only Baker's / Rhin's effective lower
   bound on `2 ^ S - 3 ^ k` for `k > 20` open.
-/

@[expose] public section

namespace SolveCollatz

/-! ### 1. Elementary Power & Parity Helpers -/

/-- For every positive `k`, `2 ^ k < 3 ^ k`. -/
theorem two_pow_lt_three_pow {k : Nat} (hk : 0 < k) : 2 ^ k < 3 ^ k := by
  induction k with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => decide
    | succ k =>
      have hprev : 2 ^ (k + 1) < 3 ^ (k + 1) := ih (Nat.succ_pos k)
      rw [Nat.pow_succ, Nat.pow_succ]
      omega

/-- Every power of `3` is odd. -/
theorem three_pow_odd (k : Nat) : 3 ^ k % 2 = 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ]
    omega

/-- Every positive power of `2` is even. -/
theorem two_pow_even {s : Nat} (hs : 0 < s) : 2 ^ s % 2 = 0 := by
  cases s with
  | zero => omega
  | succ s =>
    rw [Nat.pow_succ]
    omega

/-- For `k ≥ 2`, `5 ≤ 3 ^ k - 2 ^ k`. -/
theorem five_le_three_pow_sub_two_pow {k : Nat} (hk : 2 ≤ k) : 5 ≤ 3 ^ k - 2 ^ k := by
  induction k with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero => decide
      | succ k =>
        have hprev : 5 ≤ 3 ^ (k + 2) - 2 ^ (k + 2) := ih (by omega)
        have hlt : 2 ^ (k + 2) < 3 ^ (k + 2) := two_pow_lt_three_pow (by omega)
        rw [Nat.pow_succ, Nat.pow_succ]
        omega

/-- If an odd integer `d` divides `2 * a`, then `d` divides `a`. -/
theorem dvd_of_odd_dvd_two_mul {d a : Nat} (hodd : d % 2 = 1) (hdvd : d ∣ 2 * a) : d ∣ a := by
  rcases hdvd with ⟨q, hq⟩
  refine ⟨q / 2, ?_⟩
  have hqeven : q % 2 = 0 := by
    by_cases h : q % 2 = 0
    · exact h
    · have hqodd : q % 2 = 1 := by omega
      have hprod : (d * q) % 2 = 1 := by
        rw [Nat.mul_mod, hodd, hqodd]
      omega
  have h2q : 2 * (q / 2) = q := by omega
  have h2a : 2 * a = 2 * (d * (q / 2)) := by
    calc 2 * a = d * q := hq
      _ = d * (2 * (q / 2)) := by rw [h2q]
      _ = 2 * (d * (q / 2)) := by rw [Nat.mul_left_comm]
  omega

/-- If an odd integer `d` divides `2 ^ k * a`, then `d` divides `a`. -/
theorem dvd_of_odd_dvd_two_pow_mul {d a : Nat} (hodd : d % 2 = 1) (k : Nat)
    (hdvd : d ∣ 2 ^ k * a) : d ∣ a := by
  induction k with
  | zero =>
    simpa [Nat.pow_zero, Nat.one_mul] using hdvd
  | succ k ih =>
    apply ih
    apply dvd_of_odd_dvd_two_mul hodd
    simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hdvd

/-- If `2 ^ k` divides `c * a` with `c` odd, then `2 ^ k` divides `a`. -/
theorem two_pow_dvd_of_dvd_odd_mul {c : Nat} (hc : c % 2 = 1) (k : Nat) :
    ∀ a : Nat, 2 ^ k ∣ c * a → 2 ^ k ∣ a := by
  induction k with
  | zero =>
    intro a _
    exact Nat.one_dvd a
  | succ k ih =>
    intro a hdvd
    rcases hdvd with ⟨q, hq⟩
    have haeven : a % 2 = 0 := by
      by_cases h : a % 2 = 0
      · exact h
      · have haodd : a % 2 = 1 := by omega
        have hprod : (c * a) % 2 = 1 := by
          rw [Nat.mul_mod, hc, haodd]
        have hpow : (2 ^ (k + 1) * q) % 2 = 0 := by
          rw [Nat.pow_succ, Nat.mul_right_comm]
          omega
        omega
    have hhalf : 2 ^ k ∣ c * (a / 2) := by
      refine ⟨q, ?_⟩
      have h2a : a = (a / 2) * 2 := by omega
      have hmul : (c * (a / 2)) * 2 = (2 ^ k * q) * 2 := by
        calc (c * (a / 2)) * 2 = c * ((a / 2) * 2) := by rw [Nat.mul_assoc]
          _ = c * a := by rw [← h2a]
          _ = 2 ^ (k + 1) * q := hq
          _ = (2 ^ k * q) * 2 := by rw [Nat.pow_succ, Nat.mul_right_comm]
      omega
    rcases ih (a / 2) hhalf with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    have h2a : a = (a / 2) * 2 := by omega
    calc a = (a / 2) * 2 := h2a
      _ = (2 ^ k * r) * 2 := by rw [hr]
      _ = 2 ^ (k + 1) * r := by rw [Nat.pow_succ, Nat.mul_right_comm]

/-- Factoring identity `2 ^ (m + e) - 2 ^ (m + 1) = 2 ^ (m + 1) * (2 ^ (e - 1) - 1)` for `1 ≤ e`. -/
theorem two_pow_add_sub_two_pow (m : Nat) {e : Nat} (he : 1 ≤ e) :
    2 ^ (m + e) - 2 ^ (m + 1) = 2 ^ (m + 1) * (2 ^ (e - 1) - 1) := by
  have hsplit : m + e = (m + 1) + (e - 1) := by omega
  rw [hsplit, Nat.pow_add, Nat.mul_sub, Nat.mul_one]

/-! ### 2. Canonical 1-Circuit Parity Vector & Steiner Numerator Identity -/

/-- Canonical Steiner 1-circuit parity vector with `m` initial unit halvings followed by `e`
halvings, representing `k = m + 1` odd Syracuse steps and total halving sum `S = m + e`. -/
def oneCircuitVec (m e : Nat) : List Nat :=
  List.replicate m 1 ++ [e]

/-- A positive odd integer `n` forms a Steiner 1-circuit Syracuse cycle of parameters `(m, e)`
(odd length `k = m + 1`, final halving exponent `e`) if `syracuseIter (m + 1) n = n` with parity
vector `oneCircuitVec m e`. -/
def IsOneCircuitCycle (n m e : Nat) : Prop :=
  syracuseIter (m + 1) n = n ∧ syracuseValVec (m + 1) n = oneCircuitVec m e

/-- The length of `oneCircuitVec m e` is `m + 1`. -/
theorem oneCircuitVec_length (m e : Nat) : (oneCircuitVec m e).length = m + 1 := by
  simp [oneCircuitVec]

/-- The halving sum of `m` consecutive unit halvings equals `m`. -/
theorem paritySum_replicate_one (m : Nat) : paritySum (List.replicate m 1) = m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [List.replicate_succ, paritySum, ih]
    omega

/-- The total halving count of `oneCircuitVec m e` is `m + e`. -/
theorem paritySum_oneCircuitVec (m e : Nat) : paritySum (oneCircuitVec m e) = m + e := by
  simp [oneCircuitVec, paritySum_append, paritySum_replicate_one, paritySum]

/-- **Steiner's Closed-Form Numerator Identity (Subtraction-Free Form, Steiner 1977):**
`parityOffset (oneCircuitVec m e) + 2 ^ (m + 1) = 3 ^ (m + 1)`. -/
theorem parityOffset_oneCircuitVec_add (m e : Nat) :
    parityOffset (oneCircuitVec m e) + 2 ^ (m + 1) = 3 ^ (m + 1) := by
  induction m with
  | zero =>
    simp [oneCircuitVec, parityOffset]
  | succ m ih =>
    have hcons : oneCircuitVec (m + 1) e = 1 :: oneCircuitVec m e := by
      simp [oneCircuitVec, List.replicate_succ]
    calc parityOffset (oneCircuitVec (m + 1) e) + 2 ^ (m + 2)
        = (3 ^ (oneCircuitVec m e).length + 2 ^ 1 * parityOffset (oneCircuitVec m e)) +
            2 ^ (m + 2) := by
            rw [hcons, parityOffset]
      _ = 3 ^ (m + 1) + 2 * (parityOffset (oneCircuitVec m e) + 2 ^ (m + 1)) := by
            rw [oneCircuitVec_length, Nat.pow_one, Nat.pow_succ 2 (m + 1),
              Nat.mul_comm (2 ^ (m + 1)) 2, Nat.add_assoc, ← Nat.mul_add]
      _ = 3 ^ (m + 1) + 2 * 3 ^ (m + 1) := by
            rw [ih]
      _ = 3 ^ (m + 2) := by
            rw [Nat.pow_succ 3 (m + 1)]
            omega

/-- **Steiner's Closed-Form Numerator Identity (Steiner 1977, Section 2):**
`parityOffset (oneCircuitVec m e) = 3 ^ (m + 1) - 2 ^ (m + 1)`. -/
theorem parityOffset_oneCircuitVec (m e : Nat) :
    parityOffset (oneCircuitVec m e) = 3 ^ (m + 1) - 2 ^ (m + 1) := by
  have h := parityOffset_oneCircuitVec_add m e
  omega

/-! ### 3. Steiner's 1-Circuit Cycle Equation & Algebraic Divisibility Equivalence -/

/-- Any 1-circuit Syracuse cycle starting point `n` is odd (and hence positive). -/
theorem IsOneCircuitCycle.odd {n m e : Nat} (h : IsOneCircuitCycle n m e) : n % 2 = 1 := by
  rw [← h.1]
  exact syracuseIter_odd (Nat.succ_pos m) n

/-- Along a 1-circuit cycle, the total halving count equals `m + e`. -/
theorem IsOneCircuitCycle.totalVal_eq {n m e : Nat} (h : IsOneCircuitCycle n m e) :
    syracuseTotalVal (m + 1) n = m + e := by
  rw [← paritySum_syracuseValVec, h.2, paritySum_oneCircuitVec]

/-- Along a 1-circuit cycle, the affine numerator equals `3 ^ (m + 1) - 2 ^ (m + 1)`. -/
theorem IsOneCircuitCycle.offset_eq {n m e : Nat} (h : IsOneCircuitCycle n m e) :
    syracuseOffset (m + 1) n = 3 ^ (m + 1) - 2 ^ (m + 1) := by
  rw [← parityOffset_syracuseValVec, h.2, parityOffset_oneCircuitVec]

/-- Archimedean positivity inequality for 1-circuits: `3 ^ (m + 1) < 2 ^ (m + e)`. -/
theorem IsOneCircuitCycle.pow_lt {n m e : Nat} (h : IsOneCircuitCycle n m e) :
    3 ^ (m + 1) < 2 ^ (m + e) := by
  have hlt := syracuse_cycle_pow_lt (Nat.succ_pos m) h.1
  rwa [h.totalVal_eq] at hlt

/-- Any `(m, e)` satisfying `3 ^ (m + 1) < 2 ^ (m + e)` forces `2 ≤ e`. -/
theorem two_le_of_three_pow_lt_two_pow {m e : Nat} (hpow : 3 ^ (m + 1) < 2 ^ (m + e)) :
    2 ≤ e := by
  have h23 : 2 ^ (m + 1) < 3 ^ (m + 1) := two_pow_lt_three_pow (Nat.succ_pos m)
  by_cases hge : 2 ≤ e
  · exact hge
  · have hle : m + e ≤ m + 1 := by omega
    have hpowle : 2 ^ (m + e) ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by decide) hle
    omega

/-- The final halving exponent of any 1-circuit satisfies `2 ≤ e`. -/
theorem IsOneCircuitCycle.two_le_e {n m e : Nat} (h : IsOneCircuitCycle n m e) : 2 ≤ e :=
  two_le_of_three_pow_lt_two_pow h.pow_lt

/-- The Steiner cycle denominator `2 ^ (m + e) - 3 ^ (m + 1)` is odd whenever
`3 ^ (m + 1) < 2 ^ (m + e)`. -/
theorem steiner_denom_odd {m e : Nat} (hpow : 3 ^ (m + 1) < 2 ^ (m + e)) :
    (2 ^ (m + e) - 3 ^ (m + 1)) % 2 = 1 := by
  have he : 2 ≤ e := two_le_of_three_pow_lt_two_pow hpow
  have h2 : 2 ^ (m + e) % 2 = 0 := two_pow_even (by omega)
  have h3 : 3 ^ (m + 1) % 2 = 1 := three_pow_odd (m + 1)
  omega

/-- **Steiner's 1-Circuit Cycle Equation (Steiner 1977, Theorem 1):**
`(2 ^ (m + e) - 3 ^ (m + 1)) * n = 3 ^ (m + 1) - 2 ^ (m + 1)`. -/
theorem steiner_cycle_equation {n m e : Nat} (h : IsOneCircuitCycle n m e) :
    (2 ^ (m + e) - 3 ^ (m + 1)) * n = 3 ^ (m + 1) - 2 ^ (m + 1) := by
  have heq := syracuse_cycle_equation h.1
  rwa [h.totalVal_eq, h.offset_eq] at heq

/-- **Subtraction-Free `(n + 1)` Cycle Identity (Steiner 1977):**
`2 ^ (m + e) * n + 2 ^ (m + 1) = 3 ^ (m + 1) * (n + 1)`. -/
theorem steiner_cycle_add_eq {n m e : Nat} (h : IsOneCircuitCycle n m e) :
    2 ^ (m + e) * n + 2 ^ (m + 1) = 3 ^ (m + 1) * (n + 1) := by
  have hmul : 2 ^ (m + e) * n = 3 ^ (m + 1) * n + parityOffset (oneCircuitVec m e) := by
    have hm := syracuse_cycle_mul_eq h.1
    rw [h.totalVal_eq, ← parityOffset_syracuseValVec, h.2] at hm
    exact hm
  calc 2 ^ (m + e) * n + 2 ^ (m + 1)
      = 3 ^ (m + 1) * n + (parityOffset (oneCircuitVec m e) + 2 ^ (m + 1)) := by
          rw [hmul, Nat.add_assoc]
    _ = 3 ^ (m + 1) * n + 3 ^ (m + 1) := by
          rw [parityOffset_oneCircuitVec_add]
    _ = 3 ^ (m + 1) * (n + 1) := by
          rw [Nat.mul_add, Nat.mul_one]

/-- **Shifted Steiner Identity:**
`(2 ^ (m + e) - 3 ^ (m + 1)) * (n + 1) = 2 ^ (m + e) - 2 ^ (m + 1)`. -/
theorem steiner_cycle_succ_mul {n m e : Nat} (h : IsOneCircuitCycle n m e) :
    (2 ^ (m + e) - 3 ^ (m + 1)) * (n + 1) = 2 ^ (m + e) - 2 ^ (m + 1) := by
  have h23 : 2 ^ (m + 1) < 3 ^ (m + 1) := two_pow_lt_three_pow (Nat.succ_pos m)
  have hpow : 3 ^ (m + 1) < 2 ^ (m + e) := h.pow_lt
  have heq : (2 ^ (m + e) - 3 ^ (m + 1)) * n = 3 ^ (m + 1) - 2 ^ (m + 1) :=
    steiner_cycle_equation h
  rw [Nat.mul_add, Nat.mul_one, heq]
  omega

/-- Divisibility consequence of `steiner_cycle_succ_mul`:
`(2 ^ (m + e) - 3 ^ (m + 1)) ∣ (2 ^ (m + e) - 2 ^ (m + 1))`. -/
theorem steiner_cycle_dvd_pow_sub {n m e : Nat} (h : IsOneCircuitCycle n m e) :
    (2 ^ (m + e) - 3 ^ (m + 1)) ∣ (2 ^ (m + e) - 2 ^ (m + 1)) :=
  ⟨n + 1, (steiner_cycle_succ_mul h).symm⟩

/-- **Exact Divisibility Equivalence (certifying `search/cycle_hunter.py`):**
whenever `3 ^ (m + 1) < 2 ^ (m + e)`,
`(2 ^ (m + e) - 3 ^ (m + 1)) ∣ (3 ^ (m + 1) - 2 ^ (m + 1))` holds if and only if
`(2 ^ (m + e) - 3 ^ (m + 1)) ∣ (2 ^ (e - 1) - 1)`. -/
theorem steiner_dvd_iff_two_pow_sub_one {m e : Nat} (hpow : 3 ^ (m + 1) < 2 ^ (m + e)) :
    (2 ^ (m + e) - 3 ^ (m + 1)) ∣ (3 ^ (m + 1) - 2 ^ (m + 1)) ↔
      (2 ^ (m + e) - 3 ^ (m + 1)) ∣ (2 ^ (e - 1) - 1) := by
  have h23 : 2 ^ (m + 1) < 3 ^ (m + 1) := two_pow_lt_three_pow (Nat.succ_pos m)
  have he : 2 ≤ e := two_le_of_three_pow_lt_two_pow hpow
  have hodd : (2 ^ (m + e) - 3 ^ (m + 1)) % 2 = 1 := steiner_denom_odd hpow
  have hsum :
      (3 ^ (m + 1) - 2 ^ (m + 1)) + (2 ^ (m + e) - 3 ^ (m + 1)) =
        2 ^ (m + 1) * (2 ^ (e - 1) - 1) := by
    rw [← two_pow_add_sub_two_pow m (by omega)]
    omega
  constructor
  · intro hdvd
    have hmul : (2 ^ (m + e) - 3 ^ (m + 1)) ∣ 2 ^ (m + 1) * (2 ^ (e - 1) - 1) := by
      rw [← hsum]
      exact Nat.dvd_add hdvd (Nat.dvd_refl _)
    exact dvd_of_odd_dvd_two_pow_mul hodd (m + 1) hmul
  · intro hdvd
    have hmul : (2 ^ (m + e) - 3 ^ (m + 1)) ∣ 2 ^ (m + 1) * (2 ^ (e - 1) - 1) :=
      Nat.dvd_mul_left_of_dvd hdvd (2 ^ (m + 1))
    rw [← hsum] at hmul
    exact (Nat.dvd_add_left (Nat.dvd_refl _)).mp hmul

/-- Every 1-circuit Syracuse cycle satisfies
`(2 ^ (m + e) - 3 ^ (m + 1)) ∣ (2 ^ (e - 1) - 1)`. -/
theorem steiner_cycle_dvd_two_pow_sub_one {n m e : Nat} (h : IsOneCircuitCycle n m e) :
    (2 ^ (m + e) - 3 ^ (m + 1)) ∣ (2 ^ (e - 1) - 1) :=
  (steiner_dvd_iff_two_pow_sub_one h.pow_lt).mp ⟨n, (steiner_cycle_equation h).symm⟩

/-- **2-adic Valuation Constraint of a 1-Circuit (Steiner 1977):**
performing `m` consecutive unit-halving steps requires `2 ^ (m + 1) ∣ (n + 1)`. -/
theorem steiner_two_pow_dvd_succ {n m e : Nat} (h : IsOneCircuitCycle n m e) :
    2 ^ (m + 1) ∣ n + 1 := by
  have he : 1 ≤ e := by have := h.two_le_e; omega
  have hsplit : m + e = (m + 1) + (e - 1) := by omega
  have hdvd : 2 ^ (m + 1) ∣ 3 ^ (m + 1) * (n + 1) := by
    refine ⟨2 ^ (e - 1) * n + 1, ?_⟩
    calc 3 ^ (m + 1) * (n + 1)
        = 2 ^ (m + e) * n + 2 ^ (m + 1) := (steiner_cycle_add_eq h).symm
      _ = 2 ^ (m + 1) * (2 ^ (e - 1) * n) + 2 ^ (m + 1) * 1 := by
          rw [hsplit, Nat.pow_add, Nat.mul_assoc, Nat.mul_one]
      _ = 2 ^ (m + 1) * (2 ^ (e - 1) * n + 1) := by rw [← Nat.mul_add]
  exact two_pow_dvd_of_dvd_odd_mul (three_pow_odd (m + 1)) (m + 1) (n + 1) hdvd

/-- **Steiner's Exponential Diophantine Upper Bound (Steiner 1977):**
every 1-circuit satisfies `2 ^ (m + 1) * (2 ^ (m + e) - 3 ^ (m + 1)) < 2 ^ (m + e)`
(equivalently `2 ^ S - 3 ^ k < 2 ^ (S - k)`). -/
theorem steiner_exp_gap_bound {n m e : Nat} (h : IsOneCircuitCycle n m e) :
    2 ^ (m + 1) * (2 ^ (m + e) - 3 ^ (m + 1)) < 2 ^ (m + e) := by
  have hdvd : (2 ^ (m + e) - 3 ^ (m + 1)) ∣ (2 ^ (e - 1) - 1) :=
    steiner_cycle_dvd_two_pow_sub_one h
  have he : 2 ≤ e := h.two_le_e
  have hpos : 0 < 2 ^ (e - 1) - 1 := by
    have hge : 2 ^ 1 ≤ 2 ^ (e - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hle : 2 ^ (m + e) - 3 ^ (m + 1) ≤ 2 ^ (e - 1) - 1 := Nat.le_of_dvd hpos hdvd
  have hmul :
      2 ^ (m + 1) * (2 ^ (m + e) - 3 ^ (m + 1)) ≤ 2 ^ (m + 1) * (2 ^ (e - 1) - 1) :=
    Nat.mul_le_mul_left _ hle
  rw [← two_pow_add_sub_two_pow m (by omega)] at hmul
  have h2pos : 0 < 2 ^ (m + 1) := Nat.two_pow_pos (m + 1)
  have h2lt : 2 ^ (m + 1) < 2 ^ (m + e) :=
    Nat.lt_trans (two_pow_lt_three_pow (Nat.succ_pos m)) h.pow_lt
  omega

/-! ### 4. Trivial Cycle Witness, Steiner Gap Bound, & Uniqueness of `S = min_s(k)` -/

/-- Non-vacuity witness: the trivial Collatz cycle `1 → 4 → 2 → 1` is a 1-circuit with
`m = 0, e = 2` (`k = 1, S = 2`). -/
theorem isOneCircuitCycle_one : IsOneCircuitCycle 1 0 2 := by
  constructor
  · exact syracuseIter_one 1
  · simp [syracuseValVec, syracuseVal_one, oneCircuitVec]

/-- Bridge to frozen `Challenge.lean`: any non-trivial 1-circuit (`1 < n`) yields a
`HasNontrivialCycle` witness (and hence `CollatzDisproof`). -/
theorem IsOneCircuitCycle.hasNontrivialCycle {n m e : Nat}
    (h : IsOneCircuitCycle n m e) (hn : 1 < n) : HasNontrivialCycle := by
  refine hasNontrivialCycle_of_syracuse_cycle (Nat.succ_pos m) h.1 ?_
  intro i hi h1
  have hreach : syracuseIter (m + 1) n = 1 := by
    calc syracuseIter (m + 1) n
        = syracuseIter (i + (m + 1 - i)) n := by rw [Nat.add_sub_of_le (Nat.le_of_lt hi)]
      _ = syracuseIter (m + 1 - i) (syracuseIter i n) := (syracuseIter_add i _ n).symm
      _ = syracuseIter (m + 1 - i) 1 := by rw [h1]
      _ = 1 := syracuseIter_one _
  rw [h.1] at hreach
  omega

/-- Any 1-circuit with `m = 0` (`k = 1`) must be the trivial cycle `n = 1, e = 2`. -/
theorem IsOneCircuitCycle.one_of_m_eq_zero {n e : Nat} (h : IsOneCircuitCycle n 0 e) :
    n = 1 ∧ e = 2 := by
  have heq : (2 ^ e - 3) * n = 1 := by
    simpa [Nat.zero_add, Nat.pow_one] using steiner_cycle_equation h
  have hdpos : 0 < 2 ^ e - 3 := by
    have hpow : 3 < 2 ^ e := by simpa [Nat.zero_add, Nat.pow_one] using h.pow_lt
    omega
  have hn1 : n = 1 := by
    by_cases h1 : n = 1
    · exact h1
    · have hodd := h.odd
      have hmul : 1 * 2 ≤ (2 ^ e - 3) * n := Nat.mul_le_mul (by omega) (by omega)
      omega
  have h2e : 2 ^ e = 4 := by
    have hpow : 3 < 2 ^ e := by simpa [Nat.zero_add, Nat.pow_one] using h.pow_lt
    rw [hn1, Nat.mul_one] at heq
    omega
  have he2 : e = 2 := by
    by_cases hlt : e < 2
    · have : 2 ^ e ≤ 2 ^ 1 := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    · by_cases hgt : 2 < e
      · have : 2 ^ 3 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      · omega
  exact ⟨hn1, he2⟩

/-- Any non-trivial 1-circuit (`1 < n`) has `3 ≤ n` (since `n` is odd). -/
theorem IsOneCircuitCycle.three_le_of_one_lt {n m e : Nat}
    (h : IsOneCircuitCycle n m e) (hn : 1 < n) : 3 ≤ n := by
  have hodd := h.odd
  omega

/-- Strong factor-of-3 Steiner gap inequality for non-trivial 1-circuits (`1 < n`):
`3 * (2 ^ (m + e) - 3 ^ (m + 1)) ≤ 3 ^ (m + 1) - 2 ^ (m + 1)`. -/
theorem steiner_three_mul_gap_le {n m e : Nat}
    (h : IsOneCircuitCycle n m e) (hn : 1 < n) :
    3 * (2 ^ (m + e) - 3 ^ (m + 1)) ≤ 3 ^ (m + 1) - 2 ^ (m + 1) := by
  have h3 : 3 ≤ n := h.three_le_of_one_lt hn
  have heq := steiner_cycle_equation h
  have hmul : (2 ^ (m + e) - 3 ^ (m + 1)) * 3 ≤ (2 ^ (m + e) - 3 ^ (m + 1)) * n :=
    Nat.mul_le_mul_left _ h3
  rw [Nat.mul_comm] at hmul
  omega

/-- **Steiner Upper Bound on the Gap `2 ^ S - 3 ^ k` (Steiner 1977):**
for any non-trivial 1-circuit (`1 < n`),
`2 ^ (m + e) - 3 ^ (m + 1) < (3 ^ (m + 1) - 2 ^ (m + 1)) / 2`. -/
theorem steiner_gap_bound {n m e : Nat}
    (h : IsOneCircuitCycle n m e) (hn : 1 < n) :
    2 ^ (m + e) - 3 ^ (m + 1) < (3 ^ (m + 1) - 2 ^ (m + 1)) / 2 := by
  have hm : 1 ≤ m := by
    cases m with
    | zero =>
      have h1 := (h.one_of_m_eq_zero).1
      omega
    | succ m => omega
  have h5 : 5 ≤ 3 ^ (m + 1) - 2 ^ (m + 1) := five_le_three_pow_sub_two_pow (by omega)
  have h3d : 3 * (2 ^ (m + e) - 3 ^ (m + 1)) ≤ 3 ^ (m + 1) - 2 ^ (m + 1) :=
    steiner_three_mul_gap_le h hn
  have hpos : 0 < 2 ^ (m + e) - 3 ^ (m + 1) := by
    have := h.pow_lt
    omega
  omega

/-- **Steiner Search-Band Upper Bound:** every non-trivial 1-circuit (`1 < n`) satisfies
`2 ^ (m + e) < 2 * 3 ^ (m + 1)`. -/
theorem steiner_two_pow_lt_two_mul_three_pow {n m e : Nat}
    (h : IsOneCircuitCycle n m e) (hn : 1 < n) :
    2 ^ (m + e) < 2 * 3 ^ (m + 1) := by
  have h3d := steiner_three_mul_gap_le h hn
  have h23 : 2 ^ (m + 1) < 3 ^ (m + 1) := two_pow_lt_three_pow (Nat.succ_pos m)
  have hpos : 0 < 2 ^ (m + 1) := Nat.two_pow_pos (m + 1)
  omega

/-- **Steiner Diophantine Upper Bound (3^k Form):** every non-trivial 1-circuit (`1 < n`) satisfies
`2 ^ m * (2 ^ (m + e) - 3 ^ (m + 1)) < 3 ^ (m + 1)`. -/
theorem steiner_three_pow_gap_bound {n m e : Nat}
    (h : IsOneCircuitCycle n m e) (hn : 1 < n) :
    2 ^ m * (2 ^ (m + e) - 3 ^ (m + 1)) < 3 ^ (m + 1) := by
  have hexp := steiner_exp_gap_bound h
  have hlt := steiner_two_pow_lt_two_mul_three_pow h hn
  have hcomb : 2 ^ (m + 1) * (2 ^ (m + e) - 3 ^ (m + 1)) < 2 * 3 ^ (m + 1) :=
    Nat.lt_trans hexp hlt
  rw [Nat.pow_succ 2 m, Nat.mul_comm (2 ^ m) 2, Nat.mul_assoc] at hcomb
  exact Nat.lt_of_mul_lt_mul_left hcomb

/-- Structurally recursive helper locating the minimal `s` with `x < 2 ^ s` using accumulator
`p = 2 ^ s` (fast in Lean's kernel with zero well-founded recursion overhead). -/
def findTwoExpAux : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, s => s
  | fuel + 1, x, p, s =>
    if x < p then s else findTwoExpAux fuel x (2 * p) (s + 1)

/-- The unique minimal halving count `S = min_s(k)` satisfying `3 ^ k < 2 ^ S`
(matching `pow3.bit_length()` in `search/cycle_hunter.py`). -/
def minHalvings (k : Nat) : Nat :=
  findTwoExpAux (2 * k + 1) (3 ^ k) 1 0

/-- Elementary ceiling bound `3 ^ k < 2 ^ (2 * k + 1)` providing fuel for `minHalvings`. -/
theorem three_pow_lt_two_pow_double_succ (k : Nat) : 3 ^ k < 2 ^ (2 * k + 1) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hsplit : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
    rw [hsplit, Nat.pow_add 2 (2 * k + 1) 2, Nat.pow_succ 3 k]
    omega

/-- Invariant specification for `findTwoExpAux`. -/
theorem findTwoExpAux_spec (fuel x s : Nat) (hlo : s = 0 ∨ 2 ^ (s - 1) ≤ x)
    (hhi : x < 2 ^ (s + fuel)) :
    x < 2 ^ findTwoExpAux fuel x (2 ^ s) s ∧
      (findTwoExpAux fuel x (2 ^ s) s = 0 ∨
        2 ^ (findTwoExpAux fuel x (2 ^ s) s - 1) ≤ x) := by
  induction fuel generalizing s with
  | zero =>
    simpa [findTwoExpAux] using And.intro hhi hlo
  | succ fuel ih =>
    unfold findTwoExpAux
    split
    · exact ⟨by assumption, hlo⟩
    · rename_i hnot
      have hle : 2 ^ s ≤ x := Nat.le_of_not_lt hnot
      have hpow : 2 * 2 ^ s = 2 ^ (s + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm]
      have hhi' : x < 2 ^ ((s + 1) + fuel) := by
        have hadd : (s + 1) + fuel = s + (fuel + 1) := by omega
        rwa [hadd]
      rw [hpow]
      exact ih (s + 1) (Or.inr (by simpa using hle)) hhi'

/-- Lower-bound specification of `minHalvings`: `3 ^ k < 2 ^ minHalvings k`. -/
theorem lt_two_pow_minHalvings (k : Nat) : 3 ^ k < 2 ^ minHalvings k := by
  have hspec :=
    findTwoExpAux_spec (2 * k + 1) (3 ^ k) 0 (Or.inl rfl)
      (by simpa [Nat.zero_add] using three_pow_lt_two_pow_double_succ k)
  simpa [minHalvings] using hspec.1

/-- Upper-bound specification of `minHalvings`: for `0 < k`, `2 ^ minHalvings k < 2 * 3 ^ k`. -/
theorem two_pow_minHalvings_lt_two_mul {k : Nat} (hk : 0 < k) :
    2 ^ minHalvings k < 2 * 3 ^ k := by
  have hspec :=
    findTwoExpAux_spec (2 * k + 1) (3 ^ k) 0 (Or.inl rfl)
      (by simpa [Nat.zero_add] using three_pow_lt_two_pow_double_succ k)
  have hgt : 3 ^ k < 2 ^ minHalvings k := by simpa [minHalvings] using hspec.1
  have hlo : minHalvings k = 0 ∨ 2 ^ (minHalvings k - 1) ≤ 3 ^ k := by
    simpa [minHalvings] using hspec.2
  have h3ge : 3 ≤ 3 ^ k := by
    have : 3 ^ 1 ≤ 3 ^ k := Nat.pow_le_pow_right (by decide) hk
    simpa using this
  have hge2 : 2 ≤ minHalvings k := by
    by_cases h2 : 2 ≤ minHalvings k
    · exact h2
    · have : 2 ^ minHalvings k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by decide) (by omega)
      omega
  have hprev_le : 2 ^ (minHalvings k - 1) ≤ 3 ^ k := by
    rcases hlo with h0 | hle
    · omega
    · exact hle
  have hprev_ne : 2 ^ (minHalvings k - 1) ≠ 3 ^ k := by
    have heven : 2 ^ (minHalvings k - 1) % 2 = 0 := two_pow_even (by omega)
    have hodd : 3 ^ k % 2 = 1 := three_pow_odd k
    omega
  have hsub : minHalvings k = (minHalvings k - 1) + 1 := by omega
  rw [hsub, Nat.pow_succ]
  omega

/-- **Uniqueness of the Power-of-Two Band:** at most one exponent `S` satisfies
`3 ^ k < 2 ^ S < 2 * 3 ^ k`. -/
theorem steiner_band_unique {k S₁ S₂ : Nat}
    (h1l : 3 ^ k < 2 ^ S₁) (h1u : 2 ^ S₁ < 2 * 3 ^ k)
    (h2l : 3 ^ k < 2 ^ S₂) (h2u : 2 ^ S₂ < 2 * 3 ^ k) : S₁ = S₂ := by
  by_cases hlt : S₁ < S₂
  · have hstep : 2 ^ (S₁ + 1) ≤ 2 ^ S₂ := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.pow_succ] at hstep
    omega
  · by_cases hgt : S₂ < S₁
    · have hstep : 2 ^ (S₂ + 1) ≤ 2 ^ S₁ := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.pow_succ] at hstep
      omega
    · omega

/-- **Uniqueness of `S = min_s(k)` for Non-Trivial 1-Circuits (certifying
`search/cycle_hunter.py`):** for every non-trivial 1-circuit (`1 < n`), the total halving count
`m + e` is uniquely forced to equal `minHalvings (m + 1)`. -/
theorem steiner_totalVal_eq_minHalvings {n m e : Nat}
    (h : IsOneCircuitCycle n m e) (hn : 1 < n) :
    m + e = minHalvings (m + 1) :=
  steiner_band_unique h.pow_lt (steiner_two_pow_lt_two_mul_three_pow h hn)
    (lt_two_pow_minHalvings (m + 1)) (two_pow_minHalvings_lt_two_mul (Nat.succ_pos m))

/-! ### 5. Exact Bounded Elimination (`1 ≤ k ≤ 20`) & Conditional Steiner Reduction -/

/-- Kernel-computable test certifying that no non-trivial 1-circuit of odd length `k` exists:
at the unique admissible `S = minHalvings k`, either `3 * (2 ^ S - 3 ^ k) > 3 ^ k - 2 ^ k`
or `(2 ^ S - 3 ^ k)` fails to divide `(3 ^ k - 2 ^ k)`. -/
def steinerCandidateRuledOut (k : Nat) : Bool :=
  let p3 := 3 ^ k
  let p2 := 2 ^ k
  let s := minHalvings k
  let d := 2 ^ s - p3
  let c := p3 - p2
  decide (c < 3 * d ∨ c % d ≠ 0)

/-- Kernel-computable test verifying `steinerCandidateRuledOut k = true` for all `1 ≤ k ≤ K`. -/
def allOneCircuitsRuledOut : Nat → Bool
  | 0 => true
  | k + 1 => steinerCandidateRuledOut (k + 1) && allOneCircuitsRuledOut k

/-- Soundness of `allOneCircuitsRuledOut` over the range `1 ≤ k ≤ K`. -/
theorem allOneCircuitsRuledOut_sound (K : Nat) (h : allOneCircuitsRuledOut K = true) :
    ∀ k : Nat, 0 < k → k ≤ K → steinerCandidateRuledOut k = true := by
  induction K with
  | zero =>
    intro k hk hle
    omega
  | succ K ih =>
    simp only [allOneCircuitsRuledOut, Bool.and_eq_true] at h
    intro k hk hle
    by_cases heq : k = K + 1
    · subst heq
      exact h.1
    · exact ih h.2 k hk (by omega)

/-- Soundness of `steinerCandidateRuledOut`: if the boolean check succeeds for `k = m + 1`, then
no non-trivial 1-circuit of length `m + 1` exists. -/
theorem no_nontrivial_oneCircuit_of_ruledOut {n m e : Nat}
    (hcheck : steinerCandidateRuledOut (m + 1) = true) (hn : 1 < n) :
    ¬ IsOneCircuitCycle n m e := by
  intro hcyc
  have hs : m + e = minHalvings (m + 1) := steiner_totalVal_eq_minHalvings hcyc hn
  have h3d : 3 * (2 ^ minHalvings (m + 1) - 3 ^ (m + 1)) ≤ 3 ^ (m + 1) - 2 ^ (m + 1) := by
    rw [← hs]
    exact steiner_three_mul_gap_le hcyc hn
  have hdvd : (2 ^ minHalvings (m + 1) - 3 ^ (m + 1)) ∣ (3 ^ (m + 1) - 2 ^ (m + 1)) := by
    rw [← hs]
    exact ⟨n, (steiner_cycle_equation hcyc).symm⟩
  have hmod : (3 ^ (m + 1) - 2 ^ (m + 1)) % (2 ^ minHalvings (m + 1) - 3 ^ (m + 1)) = 0 :=
    Nat.mod_eq_zero_of_dvd hdvd
  have hprop :
      3 ^ (m + 1) - 2 ^ (m + 1) < 3 * (2 ^ minHalvings (m + 1) - 3 ^ (m + 1)) ∨
        (3 ^ (m + 1) - 2 ^ (m + 1)) % (2 ^ minHalvings (m + 1) - 3 ^ (m + 1)) ≠ 0 := by
    simpa [steinerCandidateRuledOut] using hcheck
  rcases hprop with hlt | hne
  · omega
  · exact hne hmod

/-- General bounded elimination theorem driven by `allOneCircuitsRuledOut`. -/
theorem no_nontrivial_oneCircuit_of_allRuledOut (K : Nat)
    (hcheck : allOneCircuitsRuledOut K = true) :
    ∀ n m e : Nat, m + 1 ≤ K → 1 < n → ¬ IsOneCircuitCycle n m e := by
  intro n m e hle hn
  exact no_nontrivial_oneCircuit_of_ruledOut
    (allOneCircuitsRuledOut_sound K hcheck (m + 1) (Nat.succ_pos m) hle) hn

/-- **Exact Bounded 1-Circuit Elimination (`1 ≤ k ≤ 20`, kernel-verified, zero `native_decide`):**
there is no non-trivial positive 1-circuit Syracuse cycle with `1 ≤ m + 1 ≤ 20`. -/
theorem no_nontrivial_oneCircuit_le_20 :
    ∀ n m e : Nat, m + 1 ≤ 20 → 1 < n → ¬ IsOneCircuitCycle n m e :=
  no_nontrivial_oneCircuit_of_allRuledOut 20 (by decide)

/-- **Conditional Steiner Reduction (Steiner 1977, Theorem 1):**
combining a Baker/Rhin-type Diophantine lower bound
`2 ^ S ≤ 2 ^ k * (2 ^ S - 3 ^ k)` for all `k > K₀` (with `3 ^ k < 2 ^ S`) and finite elimination
for `k ≤ K₀` rules out ALL non-trivial positive 1-circuit Collatz cycles. -/
theorem no_nontrivial_oneCircuit_of_diophantine_bound (K₀ : Nat)
    (hBaker : ∀ k S : Nat, K₀ < k → 3 ^ k < 2 ^ S → 2 ^ S ≤ 2 ^ k * (2 ^ S - 3 ^ k))
    (hFin : ∀ n m e : Nat, m + 1 ≤ K₀ → 1 < n → ¬ IsOneCircuitCycle n m e) :
    ∀ n m e : Nat, 1 < n → ¬ IsOneCircuitCycle n m e := by
  intro n m e hn hcyc
  by_cases hle : m + 1 ≤ K₀
  · exact hFin n m e hle hn hcyc
  · have hgt : K₀ < m + 1 := Nat.lt_of_not_ge hle
    have hlow := hBaker (m + 1) (m + e) hgt hcyc.pow_lt
    have hup := steiner_exp_gap_bound hcyc
    omega

/-- **Specialized Conditional Steiner Reduction above `k = 20`:**
given only the remaining open Baker/Rhin Diophantine lower bound for `k > 20`, there are no
non-trivial positive 1-circuit Collatz cycles (discharging `1 ≤ k ≤ 20` via
`no_nontrivial_oneCircuit_le_20`). -/
theorem no_nontrivial_oneCircuit_of_diophantine_bound_gt_20
    (hBaker : ∀ k S : Nat, 20 < k → 3 ^ k < 2 ^ S → 2 ^ S ≤ 2 ^ k * (2 ^ S - 3 ^ k)) :
    ∀ n m e : Nat, 1 < n → ¬ IsOneCircuitCycle n m e :=
  no_nontrivial_oneCircuit_of_diophantine_bound 20 hBaker no_nontrivial_oneCircuit_le_20

end SolveCollatz
