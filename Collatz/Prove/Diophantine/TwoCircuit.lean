/-
Copyright (c) 2026 The solve-collatz contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Collatz.Known.SteinerCircuit
public import Collatz.Core.TwoAdic

/-!
# Simons (2005) 2-Circuit Diophantine Equation & Bounded Elimination (`PROVE-B1`)

Formalization of the exact 2-circuit Diophantine theory for the Collatz (`3n + 1`) conjecture,
advancing Track A node `PROVE-B1`:
1. Canonical 2-circuit parity vectors `twoCircuitVec k₁ e₁ k₂ e₂` (`search/cycle_hunter.py`),
   `IsTwoCircuitCycle`, and clean bridge to `HasNontrivialCycle` in frozen `Challenge.lean`.
2. Exact 2-circuit closed-form numerator identity (Simons 2005):
   `parityOffset (twoCircuitVec k₁ e₁ k₂ e₂) =`
   `3^k₂ * (3^k₁ - 2^k₁) + 2^(k₁ + e₁ - 1) * (3^k₂ - 2^k₂)`
   and exact cycle equation `(2^S - 3^k) * n = C₂(k₁, e₁, k₂, e₂)`, certifying
   `search/cycle_hunter.py`'s divisibility filter `(2^S - 3^k) ∣ C₂`.
3. Coupled circuit equations and archimedean Simons bounds: `3^k < 2^S`, `9 * 2^S < 16 * 3^k`
   (hence `2^S < 2 * 3^k` and `S = minHalvings k`), `2^k₁ ∣ n + 1`, `2^k₂ ∣ m + 1`,
   and the unconditional exponential gap bound `4^k * (2^S - 3^k)^2 < 16 * 3^(3*k)`.
4. Kernel-verified elimination (`decide`, zero `native_decide`) of ALL non-trivial positive
   2-circuit cycles for `k₁ + k₂ ≤ 29`, plus a non-vacuous conditional Simons-Baker reduction
   for `k > 29` (closing the gap cleanly: `16 * 3^(3*k) ≤ 4^k * (2^S - 3^k)^2` fails at
   `k ∈ {13, 15, 17, 22, 29}` and holds for all verified `k > 29`).
5. Explicit separation from Barriers 1 (`3n - 1` at `5` and `17`), 2 (`5n + 1` on `ℕ⁺`, where
   `n = 17` forms a 2-circuit and `9 * 2^S < 16 * 3^k` relies on `3n + 1`'s `log₂(3/4) < 0`),
   3 (`ℤ_{<0}` at `-5` and `-17`), 4 (`ℤ₂` rational 2-circuit periodic point `23 / 5`), and
   5 (Conway undecidability, bypassed by restricting to fixed `m = 2` circuits on `3n + 1`).
-/

@[expose] public section

namespace SolveCollatz

/-! ### 1. Elementary Multiplication Helpers -/

private theorem mul_four_rearrange (a b c d : Nat) :
    (a * b) * (c * d) = (a * c) * (b * d) := by
  rw [Nat.mul_assoc, Nat.mul_left_comm b c d, ← Nat.mul_assoc]

private theorem nat_mul_lt_mul {a b c d : Nat} (h1 : a < b) (h2 : c < d) :
    a * c < b * d :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul_right c (Nat.le_of_lt h1))
    ((Nat.mul_lt_mul_left (by omega : 0 < b)).mpr h2)

private theorem nat_sq_lt_sq {a b : Nat} (h : a < b) : a ^ 2 < b ^ 2 := by
  simpa [Nat.pow_two] using nat_mul_lt_mul h h

private theorem nat_sq_le_sq {a b : Nat} (h : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  simpa [Nat.pow_two] using Nat.mul_le_mul h h

/-! ### 2. Canonical 2-Circuit Parity Vectors & Closed-Form Numerator -/

/-- Canonical Simons 2-circuit parity vector with first circuit `(1^{k₁-1}, e₁)` followed by
second circuit `(1^{k₂-1}, e₂)`, matching `search/cycle_hunter.py`. -/
def twoCircuitVec (k₁ e₁ k₂ e₂ : Nat) : List Nat :=
  oneCircuitVec (k₁ - 1) e₁ ++ oneCircuitVec (k₂ - 1) e₂

/-- Closed-form Simons 2-circuit cycle numerator
`C₂(k₁, e₁, k₂, e₂) = 3^k₂ * (3^k₁ - 2^k₁) + 2^(k₁ + e₁ - 1) * (3^k₂ - 2^k₂)`.
Note that `C₂` is independent of `_e₂` (`e₂` enters the cycle equation only through the total
halving count `S = k₁ + k₂ + e₁ + e₂ - 2`); the 4-argument signature mirrors `twoCircuitVec`. -/
def twoCircuitOffset (k₁ e₁ k₂ _e₂ : Nat) : Nat :=
  3 ^ k₂ * (3 ^ k₁ - 2 ^ k₁) + 2 ^ (k₁ + e₁ - 1) * (3 ^ k₂ - 2 ^ k₂)

/-- Total length of `twoCircuitVec k₁ e₁ k₂ e₂` is `k₁ + k₂` when `1 ≤ k₁` and `1 ≤ k₂`. -/
theorem twoCircuitVec_length {k₁ e₁ k₂ e₂ : Nat} (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) :
    (twoCircuitVec k₁ e₁ k₂ e₂).length = k₁ + k₂ := by
  simp only [twoCircuitVec, List.length_append, oneCircuitVec_length]
  omega

/-- Total halving count of `twoCircuitVec k₁ e₁ k₂ e₂` is `k₁ + k₂ + e₁ + e₂ - 2`. -/
theorem paritySum_twoCircuitVec {k₁ e₁ k₂ e₂ : Nat} (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) :
    paritySum (twoCircuitVec k₁ e₁ k₂ e₂) = k₁ + k₂ + e₁ + e₂ - 2 := by
  simp only [twoCircuitVec, paritySum_append, paritySum_oneCircuitVec]
  omega

/-- **Exact 2-Circuit Closed-Form Numerator Identity (Simons 2005):**
`parityOffset (twoCircuitVec k₁ e₁ k₂ e₂) = 3^k₂ * (3^k₁ - 2^k₁) + 2^(k₁ + e₁ - 1) * (3^k₂ - 2^k₂)`
for all `1 ≤ k₁` and `1 ≤ k₂`. -/
theorem parityOffset_twoCircuitVec {k₁ e₁ k₂ e₂ : Nat} (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) :
    parityOffset (twoCircuitVec k₁ e₁ k₂ e₂) =
      3 ^ k₂ * (3 ^ k₁ - 2 ^ k₁) + 2 ^ (k₁ + e₁ - 1) * (3 ^ k₂ - 2 ^ k₂) := by
  have h1 : k₁ - 1 + 1 = k₁ := by omega
  have h2 : k₂ - 1 + 1 = k₂ := by omega
  have hsum : k₁ - 1 + e₁ = k₁ + e₁ - 1 := by omega
  rw [twoCircuitVec, parityOffset_append, oneCircuitVec_length, h2,
    parityOffset_oneCircuitVec, parityOffset_oneCircuitVec, paritySum_oneCircuitVec,
    h1, h2, hsum]

/-- `parityOffset (twoCircuitVec k₁ e₁ k₂ e₂)` equals `twoCircuitOffset k₁ e₁ k₂ e₂`. -/
theorem parityOffset_twoCircuitVec_eq {k₁ e₁ k₂ e₂ : Nat} (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) :
    parityOffset (twoCircuitVec k₁ e₁ k₂ e₂) = twoCircuitOffset k₁ e₁ k₂ e₂ :=
  parityOffset_twoCircuitVec hk₁ hk₂

/-- Every canonical 2-circuit parity vector with positive exponents is a valid parity vector. -/
theorem twoCircuitVec_valid {k₁ e₁ k₂ e₂ : Nat}
    (hk₁ : 1 ≤ k₁) (he₁ : 1 ≤ e₁) (hk₂ : 1 ≤ k₂) (he₂ : 1 ≤ e₂) :
    IsValidParityVec (twoCircuitVec k₁ e₁ k₂ e₂) := by
  refine ⟨?_, ?_⟩
  · intro hnil
    have hlen := twoCircuitVec_length (e₁ := e₁) (e₂ := e₂) hk₁ hk₂
    rw [hnil] at hlen
    simp at hlen
    omega
  · intro a ha
    simp only [twoCircuitVec, oneCircuitVec, List.mem_append, List.mem_replicate,
      List.mem_singleton] at ha
    rcases ha with (⟨_, rfl⟩ | rfl) | (⟨_, rfl⟩ | rfl) <;> omega

/-! ### 3. `IsTwoCircuitCycle`, Bridge to `Challenge.lean`, and Exact Cycle Equation -/

/-- A non-trivial positive 2-circuit Syracuse cycle starting at `n > 1` with circuit lengths
`k₁, k₂ ≥ 1` and terminal halving drops `e₁, e₂ ≥ 2`. -/
structure IsTwoCircuitCycle (n k₁ e₁ k₂ e₂ : Nat) : Prop where
  /-- Non-triviality (`n > 1`, excluding the `{1, 4, 2}` fixed cycle). -/
  one_lt_n : 1 < n
  /-- First circuit has at least one odd step (`k₁ ≥ 1`). -/
  k₁_pos : 1 ≤ k₁
  /-- First circuit terminates in a drop of at least `2` halvings (`e₁ ≥ 2`). -/
  two_le_e₁ : 2 ≤ e₁
  /-- Second circuit has at least one odd step (`k₂ ≥ 1`). -/
  k₂_pos : 1 ≤ k₂
  /-- Second circuit terminates in a drop of at least `2` halvings (`e₂ ≥ 2`). -/
  two_le_e₂ : 2 ≤ e₂
  /-- Periodicity under `k₁ + k₂` accelerated Syracuse steps. -/
  period_eq : syracuseIter (k₁ + k₂) n = n
  /-- Exact 2-circuit halving-exponent vector along the period. -/
  valVec_eq : syracuseValVec (k₁ + k₂) n = twoCircuitVec k₁ e₁ k₂ e₂

/-- Every 2-circuit cycle starting point `n` is odd. -/
theorem IsTwoCircuitCycle.odd {n k₁ e₁ k₂ e₂ : Nat} (h : IsTwoCircuitCycle n k₁ e₁ k₂ e₂) :
    n % 2 = 1 := by
  rw [← h.period_eq]
  have hk : 0 < k₁ + k₂ := by have := h.k₁_pos; omega
  exact syracuseIter_odd hk n

/-- Every non-trivial 2-circuit cycle starting point satisfies `3 ≤ n`. -/
theorem IsTwoCircuitCycle.three_le_n {n k₁ e₁ k₂ e₂ : Nat}
    (h : IsTwoCircuitCycle n k₁ e₁ k₂ e₂) : 3 ≤ n := by
  have hodd := h.odd
  have hgt := h.one_lt_n
  omega

/-- Along a 2-circuit cycle, total halving count equals `k₁ + k₂ + e₁ + e₂ - 2`. -/
theorem IsTwoCircuitCycle.totalVal_eq {n k₁ e₁ k₂ e₂ : Nat}
    (h : IsTwoCircuitCycle n k₁ e₁ k₂ e₂) :
    syracuseTotalVal (k₁ + k₂) n = k₁ + k₂ + e₁ + e₂ - 2 := by
  rw [← paritySum_syracuseValVec, h.valVec_eq, paritySum_twoCircuitVec h.k₁_pos h.k₂_pos]

/-- Along a 2-circuit cycle, the affine numerator equals `twoCircuitOffset k₁ e₁ k₂ e₂`. -/
theorem IsTwoCircuitCycle.offset_eq {n k₁ e₁ k₂ e₂ : Nat}
    (h : IsTwoCircuitCycle n k₁ e₁ k₂ e₂) :
    syracuseOffset (k₁ + k₂) n = twoCircuitOffset k₁ e₁ k₂ e₂ := by
  rw [← parityOffset_syracuseValVec, h.valVec_eq, parityOffset_twoCircuitVec_eq h.k₁_pos h.k₂_pos]

/-- Archimedean positivity inequality for 2-circuits: `3 ^ (k₁ + k₂) < 2 ^ S`. -/
theorem IsTwoCircuitCycle.pow_lt {n k₁ e₁ k₂ e₂ : Nat}
    (h : IsTwoCircuitCycle n k₁ e₁ k₂ e₂) :
    3 ^ (k₁ + k₂) < 2 ^ (k₁ + k₂ + e₁ + e₂ - 2) := by
  have hk : 0 < k₁ + k₂ := by have := h.k₁_pos; omega
  have hlt := syracuse_cycle_pow_lt hk h.period_eq
  rwa [h.totalVal_eq] at hlt

/-- **Bridge to Frozen `Challenge.lean`:** any `IsTwoCircuitCycle` witness yields
`HasNontrivialCycle` (and hence `CollatzDisproof`). -/
theorem IsTwoCircuitCycle.hasNontrivialCycle {n k₁ e₁ k₂ e₂ : Nat}
    (h : IsTwoCircuitCycle n k₁ e₁ k₂ e₂) : HasNontrivialCycle := by
  have hk : 0 < k₁ + k₂ := by have := h.k₁_pos; omega
  refine hasNontrivialCycle_of_syracuse_cycle hk h.period_eq ?_
  intro i hi h1
  have hreach : syracuseIter (k₁ + k₂) n = 1 := by
    calc syracuseIter (k₁ + k₂) n
        = syracuseIter (i + (k₁ + k₂ - i)) n := by rw [Nat.add_sub_of_le (Nat.le_of_lt hi)]
      _ = syracuseIter (k₁ + k₂ - i) (syracuseIter i n) := (syracuseIter_add i _ n).symm
      _ = syracuseIter (k₁ + k₂ - i) 1 := by rw [h1]
      _ = 1 := syracuseIter_one _
  rw [h.period_eq] at hreach
  have hgt := h.one_lt_n
  omega

/-- **Exact 2-Circuit Diophantine Cycle Equation (Simons 2005):**
`(2 ^ S - 3 ^ k) * n = 3 ^ k₂ * (3 ^ k₁ - 2 ^ k₁) + 2 ^ (k₁ + e₁ - 1) * (3 ^ k₂ - 2 ^ k₂)`
where `k = k₁ + k₂` and `S = k₁ + k₂ + e₁ + e₂ - 2`. -/
theorem twoCircuit_cycle_equation {n k₁ e₁ k₂ e₂ : Nat}
    (h : IsTwoCircuitCycle n k₁ e₁ k₂ e₂) :
    (2 ^ (k₁ + k₂ + e₁ + e₂ - 2) - 3 ^ (k₁ + k₂)) * n =
      3 ^ k₂ * (3 ^ k₁ - 2 ^ k₁) + 2 ^ (k₁ + e₁ - 1) * (3 ^ k₂ - 2 ^ k₂) := by
  have heq := syracuse_cycle_equation h.period_eq
  rw [h.totalVal_eq, h.offset_eq] at heq
  exact heq

/-- **Divisibility Condition (certifying `search/cycle_hunter.py`):**
every 2-circuit cycle satisfies `(2 ^ S - 3 ^ (k₁ + k₂)) ∣ twoCircuitOffset k₁ e₁ k₂ e₂`. -/
theorem twoCircuit_cycle_dvd {n k₁ e₁ k₂ e₂ : Nat}
    (h : IsTwoCircuitCycle n k₁ e₁ k₂ e₂) :
    (2 ^ (k₁ + k₂ + e₁ + e₂ - 2) - 3 ^ (k₁ + k₂)) ∣ twoCircuitOffset k₁ e₁ k₂ e₂ :=
  ⟨n, (twoCircuit_cycle_equation h).symm⟩

/-! ### 4. Coupled Circuit Equations & Simons Archimedean Bounds -/

/-- Splitting the 2-circuit orbit at step `k₁` separates the two coupled 1-circuits at midpoint
`m = syracuseIter k₁ n`. -/
theorem syracuseValVec_split_twoCircuit {n k₁ e₁ k₂ e₂ : Nat}
    (h : IsTwoCircuitCycle n k₁ e₁ k₂ e₂) :
    syracuseValVec k₁ n = oneCircuitVec (k₁ - 1) e₁ ∧
      syracuseValVec k₂ (syracuseIter k₁ n) = oneCircuitVec (k₂ - 1) e₂ ∧
      syracuseIter k₂ (syracuseIter k₁ n) = n := by
  have happ :
      syracuseValVec k₁ n ++ syracuseValVec k₂ (syracuseIter k₁ n) =
        oneCircuitVec (k₁ - 1) e₁ ++ oneCircuitVec (k₂ - 1) e₂ := by
    rw [← syracuseValVec_add, h.valVec_eq, twoCircuitVec]
  have hlen : (syracuseValVec k₁ n).length = (oneCircuitVec (k₁ - 1) e₁).length := by
    rw [syracuseValVec_length, oneCircuitVec_length]
    have := h.k₁_pos
    omega
  rcases List.append_inj happ hlen with ⟨h1, h2⟩
  have hret : syracuseIter k₂ (syracuseIter k₁ n) = n := by
    rw [syracuseIter_add, h.period_eq]
  exact ⟨h1, h2, hret⟩

/-- The second-circuit starting point `m = syracuseIter k₁ n` is odd and satisfies `3 ≤ m`. -/
theorem twoCircuit_midpoint_odd_and_three_le {n k₁ e₁ k₂ e₂ : Nat}
    (h : IsTwoCircuitCycle n k₁ e₁ k₂ e₂) :
    syracuseIter k₁ n % 2 = 1 ∧ 3 ≤ syracuseIter k₁ n := by
  have hk₁ : 0 < k₁ := h.k₁_pos
  have hodd : syracuseIter k₁ n % 2 = 1 := syracuseIter_odd hk₁ n
  have hne1 : syracuseIter k₁ n ≠ 1 := by
    intro hm1
    have hret := (syracuseValVec_split_twoCircuit h).2.2
    rw [hm1, syracuseIter_one] at hret
    have hgt := h.one_lt_n
    omega
  exact ⟨hodd, by omega⟩

/-- Subtraction-free first-circuit equation `2^(k₁ + e₁ - 1) * m + 2^k₁ = 3^k₁ * (n + 1)`
for `m = syracuseIter k₁ n`. -/
theorem twoCircuit_circuit1_add_eq {n k₁ e₁ k₂ e₂ : Nat}
    (h : IsTwoCircuitCycle n k₁ e₁ k₂ e₂) :
    2 ^ (k₁ + e₁ - 1) * syracuseIter k₁ n + 2 ^ k₁ = 3 ^ k₁ * (n + 1) := by
  have hvec := (syracuseValVec_split_twoCircuit h).1
  have hk₁ := h.k₁_pos
  have haff := syracuse_affine_vec_eq k₁ n
  rw [hvec, paritySum_oneCircuitVec, parityOffset_oneCircuitVec] at haff
  have hsub : k₁ - 1 + e₁ = k₁ + e₁ - 1 := by omega
  have hinc : k₁ - 1 + 1 = k₁ := by omega
  rw [hsub, hinc] at haff
  have h23 : 2 ^ k₁ < 3 ^ k₁ := two_pow_lt_three_pow hk₁
  rw [haff, Nat.mul_add, Nat.mul_one]
  omega

/-- Subtraction-free second-circuit equation `2^(k₂ + e₂ - 1) * n + 2^k₂ = 3^k₂ * (m + 1)`
for `m = syracuseIter k₁ n`. -/
theorem twoCircuit_circuit2_add_eq {n k₁ e₁ k₂ e₂ : Nat}
    (h : IsTwoCircuitCycle n k₁ e₁ k₂ e₂) :
    2 ^ (k₂ + e₂ - 1) * n + 2 ^ k₂ = 3 ^ k₂ * (syracuseIter k₁ n + 1) := by
  have hsplit := syracuseValVec_split_twoCircuit h
  have hk₂ := h.k₂_pos
  have haff := syracuse_affine_vec_eq k₂ (syracuseIter k₁ n)
  rw [hsplit.2.2, hsplit.2.1, paritySum_oneCircuitVec, parityOffset_oneCircuitVec] at haff
  have hsub : k₂ - 1 + e₂ = k₂ + e₂ - 1 := by omega
  have hinc : k₂ - 1 + 1 = k₂ := by omega
  rw [hsub, hinc] at haff
  have h23 : 2 ^ k₂ < 3 ^ k₂ := two_pow_lt_three_pow hk₂
  rw [haff, Nat.mul_add, Nat.mul_one]
  omega

/-- `2`-adic divisibility constraints at both circuit transitions:
`2^k₁ ∣ n + 1` and `2^k₂ ∣ syracuseIter k₁ n + 1`. -/
theorem twoCircuit_two_pow_dvd_succ {n k₁ e₁ k₂ e₂ : Nat}
    (h : IsTwoCircuitCycle n k₁ e₁ k₂ e₂) :
    2 ^ k₁ ∣ n + 1 ∧ 2 ^ k₂ ∣ syracuseIter k₁ n + 1 := by
  have hk₁ := h.k₁_pos
  have he₁ := h.two_le_e₁
  have hk₂ := h.k₂_pos
  have he₂ := h.two_le_e₂
  have h1 : 2 ^ k₁ ∣ 3 ^ k₁ * (n + 1) := by
    refine ⟨2 ^ (e₁ - 1) * syracuseIter k₁ n + 1, ?_⟩
    have hsplit : k₁ + e₁ - 1 = k₁ + (e₁ - 1) := by omega
    rw [← twoCircuit_circuit1_add_eq h, hsplit, Nat.pow_add, Nat.mul_add, Nat.mul_assoc,
      Nat.mul_one]
  have h2 : 2 ^ k₂ ∣ 3 ^ k₂ * (syracuseIter k₁ n + 1) := by
    refine ⟨2 ^ (e₂ - 1) * n + 1, ?_⟩
    have hsplit : k₂ + e₂ - 1 = k₂ + (e₂ - 1) := by omega
    rw [← twoCircuit_circuit2_add_eq h, hsplit, Nat.pow_add, Nat.mul_add, Nat.mul_assoc,
      Nat.mul_one]
  exact ⟨two_pow_dvd_of_dvd_odd_mul (three_pow_odd k₁) k₁ (n + 1) h1,
    two_pow_dvd_of_dvd_odd_mul (three_pow_odd k₂) k₂ (syracuseIter k₁ n + 1) h2⟩

/-- Product of the two coupled strict circuit inequalities:
`2^S * (m * n) < 3^(k₁ + k₂) * ((n + 1) * (m + 1))`. -/
theorem twoCircuit_mul_ineq {n k₁ e₁ k₂ e₂ : Nat}
    (h : IsTwoCircuitCycle n k₁ e₁ k₂ e₂) :
    let m := syracuseIter k₁ n
    2 ^ (k₁ + k₂ + e₁ + e₂ - 2) * (m * n) <
      3 ^ (k₁ + k₂) * ((n + 1) * (m + 1)) := by
  intro m
  have h1 : 2 ^ (k₁ + e₁ - 1) * m < 3 ^ k₁ * (n + 1) := by
    have hc1 : 2 ^ (k₁ + e₁ - 1) * m + 2 ^ k₁ = 3 ^ k₁ * (n + 1) := twoCircuit_circuit1_add_eq h
    have hpos : 0 < 2 ^ k₁ := Nat.two_pow_pos k₁
    omega
  have h2 : 2 ^ (k₂ + e₂ - 1) * n < 3 ^ k₂ * (m + 1) := by
    have hc2 : 2 ^ (k₂ + e₂ - 1) * n + 2 ^ k₂ = 3 ^ k₂ * (m + 1) := twoCircuit_circuit2_add_eq h
    have hpos : 0 < 2 ^ k₂ := Nat.two_pow_pos k₂
    omega
  have hS : (k₁ + e₁ - 1) + (k₂ + e₂ - 1) = k₁ + k₂ + e₁ + e₂ - 2 := by
    have := h.k₁_pos; have := h.k₂_pos; have := h.two_le_e₁; have := h.two_le_e₂; omega
  calc 2 ^ (k₁ + k₂ + e₁ + e₂ - 2) * (m * n)
      = (2 ^ (k₁ + e₁ - 1) * m) * (2 ^ (k₂ + e₂ - 1) * n) := by
          rw [← hS, Nat.pow_add, mul_four_rearrange]
    _ < (3 ^ k₁ * (n + 1)) * (3 ^ k₂ * (m + 1)) := nat_mul_lt_mul h1 h2
    _ = 3 ^ (k₁ + k₂) * ((n + 1) * (m + 1)) := by
          rw [Nat.pow_add, mul_four_rearrange]

/-- **Sharp Simons Archimedean Upper Bound:** every non-trivial 2-circuit satisfies
`9 * 2 ^ S < 16 * 3 ^ (k₁ + k₂)` where `S = k₁ + k₂ + e₁ + e₂ - 2`. -/
theorem twoCircuit_simons_pow_bound {n k₁ e₁ k₂ e₂ : Nat}
    (h : IsTwoCircuitCycle n k₁ e₁ k₂ e₂) :
    9 * 2 ^ (k₁ + k₂ + e₁ + e₂ - 2) < 16 * 3 ^ (k₁ + k₂) := by
  let m := syracuseIter k₁ n
  have hn3 : 3 ≤ n := h.three_le_n
  have hm3 : 3 ≤ m := (twoCircuit_midpoint_odd_and_three_le h).2
  have hmn_pos : 0 < m * n := Nat.mul_pos (by omega) (by omega)
  have hmul : 2 ^ (k₁ + k₂ + e₁ + e₂ - 2) * (m * n) <
      3 ^ (k₁ + k₂) * ((n + 1) * (m + 1)) := twoCircuit_mul_ineq h
  have h9 : 9 * ((n + 1) * (m + 1)) ≤ 16 * (m * n) := by
    have h3n : 3 * (n + 1) ≤ 4 * n := by omega
    have h3m : 3 * (m + 1) ≤ 4 * m := by omega
    calc 9 * ((n + 1) * (m + 1))
        = (3 * (n + 1)) * (3 * (m + 1)) := by rw [← mul_four_rearrange]
      _ ≤ (4 * n) * (4 * m) := Nat.mul_le_mul h3n h3m
      _ = 16 * (m * n) := by rw [mul_four_rearrange, Nat.mul_comm n m]
  have hcomb : (9 * 2 ^ (k₁ + k₂ + e₁ + e₂ - 2)) * (m * n) <
      (16 * 3 ^ (k₁ + k₂)) * (m * n) := by
    calc (9 * 2 ^ (k₁ + k₂ + e₁ + e₂ - 2)) * (m * n)
        = 9 * (2 ^ (k₁ + k₂ + e₁ + e₂ - 2) * (m * n)) := by rw [Nat.mul_assoc]
      _ < 9 * (3 ^ (k₁ + k₂) * ((n + 1) * (m + 1))) :=
          (Nat.mul_lt_mul_left (by decide : 0 < 9)).mpr hmul
      _ = 3 ^ (k₁ + k₂) * (9 * ((n + 1) * (m + 1))) := by rw [Nat.mul_left_comm]
      _ ≤ 3 ^ (k₁ + k₂) * (16 * (m * n)) := Nat.mul_le_mul_left _ h9
      _ = (16 * 3 ^ (k₁ + k₂)) * (m * n) := by
          rw [← Nat.mul_assoc, Nat.mul_comm (3 ^ (k₁ + k₂)) 16]
  exact Nat.lt_of_mul_lt_mul_right hcomb

/-- **Band Upper Bound (`2^S < 2 * 3^k`):** every non-trivial 2-circuit satisfies
`2 ^ (k₁ + k₂ + e₁ + e₂ - 2) < 2 * 3 ^ (k₁ + k₂)` (and hence `< 4 * 3 ^ (k₁ + k₂)`). -/
theorem twoCircuit_two_pow_lt_two_mul_three_pow {n k₁ e₁ k₂ e₂ : Nat}
    (h : IsTwoCircuitCycle n k₁ e₁ k₂ e₂) :
    2 ^ (k₁ + k₂ + e₁ + e₂ - 2) < 2 * 3 ^ (k₁ + k₂) := by
  have h9 := twoCircuit_simons_pow_bound h
  omega

/-- **Uniqueness of `S = minHalvings k` (certifying `search/cycle_hunter.py`):**
for any non-trivial 2-circuit cycle, `S` is uniquely forced to equal `minHalvings (k₁ + k₂)`. -/
theorem twoCircuit_totalVal_eq_minHalvings {n k₁ e₁ k₂ e₂ : Nat}
    (h : IsTwoCircuitCycle n k₁ e₁ k₂ e₂) :
    k₁ + k₂ + e₁ + e₂ - 2 = minHalvings (k₁ + k₂) := by
  have hk : 0 < k₁ + k₂ := by have := h.k₁_pos; omega
  exact steiner_band_unique h.pow_lt (twoCircuit_two_pow_lt_two_mul_three_pow h)
    (lt_two_pow_minHalvings (k₁ + k₂)) (two_pow_minHalvings_lt_two_mul hk)

/-- For any non-trivial 2-circuit cycle (`3 ≤ n`), `3 * (2^S - 3^k) ≤ C₂(k₁, e₁, k₂, e₂)`
with `S = minHalvings (k₁ + k₂)`. -/
theorem twoCircuit_three_mul_denom_le {n k₁ e₁ k₂ e₂ : Nat}
    (h : IsTwoCircuitCycle n k₁ e₁ k₂ e₂) :
    3 * (2 ^ minHalvings (k₁ + k₂) - 3 ^ (k₁ + k₂)) ≤ twoCircuitOffset k₁ e₁ k₂ e₂ := by
  have hs := twoCircuit_totalVal_eq_minHalvings h
  have heq := twoCircuit_cycle_equation h
  have hn3 := h.three_le_n
  rw [hs] at heq
  have hmul : 3 * (2 ^ minHalvings (k₁ + k₂) - 3 ^ (k₁ + k₂)) ≤
      (2 ^ minHalvings (k₁ + k₂) - 3 ^ (k₁ + k₂)) * n := by
    rw [Nat.mul_comm 3]
    exact Nat.mul_le_mul_left _ hn3
  exact Nat.le_trans hmul (Nat.le_of_eq heq)

/-- **Simons Midpoint Gap Bound:** `min m n * (2 ^ S - 3 ^ k) < 3 * 3 ^ k`. -/
theorem twoCircuit_simons_gap_le {n k₁ e₁ k₂ e₂ : Nat}
    (h : IsTwoCircuitCycle n k₁ e₁ k₂ e₂) :
    min (syracuseIter k₁ n) n * (2 ^ (k₁ + k₂ + e₁ + e₂ - 2) - 3 ^ (k₁ + k₂)) <
      3 * 3 ^ (k₁ + k₂) := by
  let m := syracuseIter k₁ n
  let x := min m n
  have hn3 : 3 ≤ n := h.three_le_n
  have hm3 : 3 ≤ m := (twoCircuit_midpoint_odd_and_three_le h).2
  have hx_pos : 0 < x := by simp only [x]; omega
  have hxm : x ≤ m := Nat.min_le_left m n
  have hxn : x ≤ n := Nat.min_le_right m n
  have hmn_pos : 0 < m * n := Nat.mul_pos (by omega) (by omega)
  have hmul := twoCircuit_mul_ineq h
  have hpow := h.pow_lt
  have hdiff : (2 ^ (k₁ + k₂ + e₁ + e₂ - 2) - 3 ^ (k₁ + k₂)) * (m * n) <
      3 ^ (k₁ + k₂) * (m + n + 1) := by
    dsimp only at hmul
    rw [Nat.sub_mul]
    have h3le : 3 ^ (k₁ + k₂) * (m * n) ≤ 2 ^ (k₁ + k₂ + e₁ + e₂ - 2) * (m * n) :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt hpow)
    have hadd : (n + 1) * (m + 1) = m * n + (m + n + 1) := by
      rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, Nat.one_mul, Nat.mul_one, Nat.mul_comm n m]
      omega
    rw [hadd, Nat.mul_add] at hmul
    dsimp only [m] at h3le hmul ⊢
    omega
  have hx_bound : x * (m + n + 1) ≤ 3 * (m * n) := by
    have h1 : x * m ≤ m * n := by rw [Nat.mul_comm m n]; exact Nat.mul_le_mul_right m hxn
    have h2 : x * n ≤ m * n := Nat.mul_le_mul_right n hxm
    have h3 : x ≤ m * n := Nat.le_trans hxm (Nat.le_mul_of_pos_right m (by omega))
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
    omega
  have hcomb : (x * (2 ^ (k₁ + k₂ + e₁ + e₂ - 2) - 3 ^ (k₁ + k₂))) * (m * n) <
      (3 * 3 ^ (k₁ + k₂)) * (m * n) := by
    calc (x * (2 ^ (k₁ + k₂ + e₁ + e₂ - 2) - 3 ^ (k₁ + k₂))) * (m * n)
        = x * ((2 ^ (k₁ + k₂ + e₁ + e₂ - 2) - 3 ^ (k₁ + k₂)) * (m * n)) := by
            rw [Nat.mul_assoc]
      _ < x * (3 ^ (k₁ + k₂) * (m + n + 1)) := (Nat.mul_lt_mul_left hx_pos).mpr hdiff
      _ = 3 ^ (k₁ + k₂) * (x * (m + n + 1)) := by rw [Nat.mul_left_comm]
      _ ≤ 3 ^ (k₁ + k₂) * (3 * (m * n)) := Nat.mul_le_mul_left _ hx_bound
      _ = (3 * 3 ^ (k₁ + k₂)) * (m * n) := by
          rw [← Nat.mul_assoc, Nat.mul_comm (3 ^ (k₁ + k₂)) 3]
  exact Nat.lt_of_mul_lt_mul_right hcomb

private theorem circuit_sq_lower_of_le {k₁ k₂ a b : Nat}
    (hk : k₁ ≤ k₂) (hk₁ : 1 ≤ k₁) (ha : 3 ≤ a) (hb : 3 ≤ b)
    (hdvd : 2 ^ k₂ ≤ a + 1) (hstep : 2 ^ (k₁ + k₂) < 3 ^ k₁ * (b + 1)) :
    9 * 4 ^ (k₁ + k₂) < 16 * 3 ^ (k₁ + k₂) * (min a b) ^ 2 := by
  have h4a : 4 ^ (k₁ + k₂) < 3 ^ (k₁ + k₂) * (a + 1) ^ 2 := by
    have hk_le : k₁ + k₂ ≤ 2 * k₂ := by omega
    have h2k : 2 ^ (k₁ + k₂) ≤ (a + 1) ^ 2 := by
      calc 2 ^ (k₁ + k₂) ≤ 2 ^ (2 * k₂) := Nat.pow_le_pow_right (by decide) hk_le
        _ = (2 ^ k₂) ^ 2 := by rw [Nat.mul_comm 2 k₂, Nat.pow_mul]
        _ ≤ (a + 1) ^ 2 := nat_sq_le_sq hdvd
    have h23 : 2 ^ (k₁ + k₂) < 3 ^ (k₁ + k₂) := two_pow_lt_three_pow (by omega)
    calc 4 ^ (k₁ + k₂) = 2 ^ (k₁ + k₂) * 2 ^ (k₁ + k₂) := by
            rw [show (4 : Nat) = 2 * 2 by rfl, Nat.mul_pow]
      _ < 3 ^ (k₁ + k₂) * 2 ^ (k₁ + k₂) :=
            (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr h23
      _ ≤ 3 ^ (k₁ + k₂) * (a + 1) ^ 2 := Nat.mul_le_mul_left _ h2k
  have h4b : 4 ^ (k₁ + k₂) < 3 ^ (k₁ + k₂) * (b + 1) ^ 2 := by
    have hk_le : 2 * k₁ ≤ k₁ + k₂ := by omega
    calc 4 ^ (k₁ + k₂) = (2 ^ (k₁ + k₂)) ^ 2 := by
            rw [show (4 : Nat) = 2 ^ 2 by rfl, ← Nat.pow_mul, Nat.mul_comm 2, Nat.pow_mul]
      _ < (3 ^ k₁ * (b + 1)) ^ 2 := nat_sq_lt_sq hstep
      _ = 3 ^ (2 * k₁) * (b + 1) ^ 2 := by rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm k₁ 2]
      _ ≤ 3 ^ (k₁ + k₂) * (b + 1) ^ 2 :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hk_le)
  have finish : ∀ {c : Nat}, 3 ≤ c → 4 ^ (k₁ + k₂) < 3 ^ (k₁ + k₂) * (c + 1) ^ 2 →
      9 * 4 ^ (k₁ + k₂) < 16 * 3 ^ (k₁ + k₂) * c ^ 2 := by
    intro c hc hlt
    have h3c : 9 * (c + 1) ^ 2 ≤ 16 * c ^ 2 := by
      have h1 : 3 * (c + 1) ≤ 4 * c := by omega
      simpa [Nat.mul_pow] using nat_sq_le_sq h1
    calc 9 * 4 ^ (k₁ + k₂)
        < 9 * (3 ^ (k₁ + k₂) * (c + 1) ^ 2) := (Nat.mul_lt_mul_left (by decide)).mpr hlt
      _ = 3 ^ (k₁ + k₂) * (9 * (c + 1) ^ 2) := by rw [Nat.mul_left_comm]
      _ ≤ 3 ^ (k₁ + k₂) * (16 * c ^ 2) := Nat.mul_le_mul_left _ h3c
      _ = 16 * 3 ^ (k₁ + k₂) * c ^ 2 := by
          rw [← Nat.mul_assoc, Nat.mul_comm (3 ^ (k₁ + k₂)) 16]
  by_cases hmin : a ≤ b
  · rw [Nat.min_eq_left hmin]; exact finish ha h4a
  · rw [Nat.min_eq_right (Nat.le_of_not_ge hmin)]; exact finish hb h4b

/-- Exponential lower bound on the circuit minimum:
`9 * 4^(k₁ + k₂) < 16 * 3^(k₁ + k₂) * (min (syracuseIter k₁ n) n)^2`. -/
theorem twoCircuit_midpoint_lower_sq {n k₁ e₁ k₂ e₂ : Nat}
    (h : IsTwoCircuitCycle n k₁ e₁ k₂ e₂) :
    9 * 4 ^ (k₁ + k₂) < 16 * 3 ^ (k₁ + k₂) * (min (syracuseIter k₁ n) n) ^ 2 := by
  let m := syracuseIter k₁ n
  have hn3 : 3 ≤ n := h.three_le_n
  have hm3 : 3 ≤ m := (twoCircuit_midpoint_odd_and_three_le h).2
  have hk₁ := h.k₁_pos; have he₁ := h.two_le_e₁
  have hk₂ := h.k₂_pos; have he₂ := h.two_le_e₂
  have hdvd := twoCircuit_two_pow_dvd_succ h
  have h1le : 2 ^ k₁ ≤ n + 1 := Nat.le_of_dvd (by omega) hdvd.1
  have h2le : 2 ^ k₂ ≤ m + 1 := Nat.le_of_dvd (by omega) hdvd.2
  have hstep1 : 2 ^ (k₁ + k₂) < 3 ^ k₁ * (n + 1) := by
    have h2m : 2 ^ k₂ ≤ 2 * m := Nat.le_trans h2le (by omega)
    have hc1 : 2 ^ (k₁ + e₁ - 1) * m + 2 ^ k₁ = 3 ^ k₁ * (n + 1) := twoCircuit_circuit1_add_eq h
    have hpow : k₁ + e₁ - 1 ≥ k₁ + 1 := by omega
    have hpow2 : 2 ^ (k₁ + 1) ≤ 2 ^ (k₁ + e₁ - 1) := Nat.pow_le_pow_right (by decide) hpow
    calc 2 ^ (k₁ + k₂) = 2 ^ k₁ * 2 ^ k₂ := Nat.pow_add 2 k₁ k₂
      _ ≤ 2 ^ k₁ * (2 * m) := Nat.mul_le_mul_left _ h2m
      _ = 2 ^ (k₁ + 1) * m := by rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2 m]
      _ ≤ 2 ^ (k₁ + e₁ - 1) * m := Nat.mul_le_mul_right m hpow2
      _ < 3 ^ k₁ * (n + 1) := by have := Nat.two_pow_pos k₁; omega
  have hstep2 : 2 ^ (k₂ + k₁) < 3 ^ k₂ * (m + 1) := by
    have h2n : 2 ^ k₁ ≤ 2 * n := Nat.le_trans h1le (by omega)
    have hc2 : 2 ^ (k₂ + e₂ - 1) * n + 2 ^ k₂ = 3 ^ k₂ * (m + 1) := twoCircuit_circuit2_add_eq h
    have hpow : k₂ + e₂ - 1 ≥ k₂ + 1 := by omega
    have hpow2 : 2 ^ (k₂ + 1) ≤ 2 ^ (k₂ + e₂ - 1) := Nat.pow_le_pow_right (by decide) hpow
    calc 2 ^ (k₂ + k₁) = 2 ^ k₂ * 2 ^ k₁ := Nat.pow_add 2 k₂ k₁
      _ ≤ 2 ^ k₂ * (2 * n) := Nat.mul_le_mul_left _ h2n
      _ = 2 ^ (k₂ + 1) * n := by rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2 n]
      _ ≤ 2 ^ (k₂ + e₂ - 1) * n := Nat.mul_le_mul_right n hpow2
      _ < 3 ^ k₂ * (m + 1) := by have := Nat.two_pow_pos k₂; omega
  by_cases hle : k₁ ≤ k₂
  · exact circuit_sq_lower_of_le hle hk₁ hm3 hn3 h2le hstep1
  · have hlt : k₂ ≤ k₁ := Nat.le_of_not_ge hle
    simpa [Nat.add_comm k₂ k₁, Nat.min_comm] using
      circuit_sq_lower_of_le hlt hk₂ hn3 hm3 h1le hstep2

/-- **Simons Exponential Diophantine Gap Bound:** every non-trivial 2-circuit cycle satisfies
`4 ^ (k₁ + k₂) * (2 ^ S - 3 ^ (k₁ + k₂)) ^ 2 < 16 * 3 ^ (3 * (k₁ + k₂))`
(in real terms, `(2^S - 3^k) / 3^k < 4 * (√3 / 2)^k`), requiring zero external computation. -/
theorem twoCircuit_exp_gap_bound {n k₁ e₁ k₂ e₂ : Nat}
    (h : IsTwoCircuitCycle n k₁ e₁ k₂ e₂) :
    4 ^ (k₁ + k₂) * (2 ^ (k₁ + k₂ + e₁ + e₂ - 2) - 3 ^ (k₁ + k₂)) ^ 2 <
      16 * 3 ^ (3 * (k₁ + k₂)) := by
  let k := k₁ + k₂
  let d := 2 ^ (k₁ + k₂ + e₁ + e₂ - 2) - 3 ^ k
  let x := min (syracuseIter k₁ n) n
  have hd_pos : 0 < d := by dsimp only [d, k]; have := h.pow_lt; omega
  have hgap : x * d < 3 * 3 ^ k := twoCircuit_simons_gap_le h
  have hsq : x ^ 2 * d ^ 2 < 9 * 3 ^ (2 * k) := by
    have h1 := nat_sq_lt_sq hgap
    rw [Nat.mul_pow, Nat.mul_pow, show (3 : Nat) ^ 2 = 9 by decide, ← Nat.pow_mul,
      Nat.mul_comm k 2] at h1
    exact h1
  have hlow : 9 * 4 ^ k < 16 * 3 ^ k * x ^ 2 := twoCircuit_midpoint_lower_sq h
  have hcomb : 9 * (4 ^ k * d ^ 2) < 9 * (16 * 3 ^ (3 * k)) := by
    calc 9 * (4 ^ k * d ^ 2)
        = (9 * 4 ^ k) * d ^ 2 := by rw [Nat.mul_assoc]
      _ < (16 * 3 ^ k * x ^ 2) * d ^ 2 := (Nat.mul_lt_mul_right (Nat.pow_pos hd_pos)).mpr hlow
      _ = 16 * 3 ^ k * (x ^ 2 * d ^ 2) := by rw [Nat.mul_assoc]
      _ < 16 * 3 ^ k * (9 * 3 ^ (2 * k)) :=
          (Nat.mul_lt_mul_left (Nat.mul_pos (by decide) (Nat.pow_pos (by decide)))).mpr hsq
      _ = 9 * (16 * 3 ^ (3 * k)) := by
          rw [Nat.mul_left_comm (16 * 3 ^ k) 9, Nat.mul_assoc 16, ← Nat.pow_add,
            show k + 2 * k = 3 * k by omega]
  exact (Nat.mul_lt_mul_left (by decide : 0 < 9)).mp hcomb

/-! ### 5. Kernel-Verified Elimination (`k₁ + k₂ ≤ 29`) & Conditional Simons-Baker Reduction -/

/-- Kernel-computable test ruling out a 2-circuit tuple `(k₁, e₁, k - k₁, S + 2 - k - e₁)` at
the unique forced exponent `S = minHalvings k`: either `C₂ < 3 * (2^S - 3^k)` or
`(2^S - 3^k) ∤ C₂`. -/
def twoCircuitPairRuledOut (k k₁ e₁ : Nat) : Bool :=
  let k₂ := k - k₁
  let s := minHalvings k
  let e₂ := s + 2 - k - e₁
  let d := 2 ^ s - 3 ^ k
  let c := twoCircuitOffset k₁ e₁ k₂ e₂
  decide (c < 3 * d ∨ c % d ≠ 0)

/-- Check all `e₁` with `2 ≤ e₁ ≤ bound` for fixed `(k, k₁)`. -/
def checkTwoCircuitE₁ (k k₁ : Nat) : Nat → Bool
  | 0 => true
  | e₁ + 1 =>
    (e₁ + 1 < 2 || twoCircuitPairRuledOut k k₁ (e₁ + 1)) && checkTwoCircuitE₁ k k₁ e₁

/-- Check all `k₁` with `1 ≤ k₁ ≤ bound` for fixed `k`. -/
def checkTwoCircuitK₁ (k : Nat) : Nat → Bool
  | 0 => true
  | k₁ + 1 => checkTwoCircuitE₁ k (k₁ + 1) (minHalvings k - k) && checkTwoCircuitK₁ k k₁

/-- Kernel-computable test certifying that no non-trivial 2-circuit cycle of odd length `k`
exists. -/
def twoCircuitKRuledOut (k : Nat) : Bool :=
  checkTwoCircuitK₁ k (k - 1)

/-- Kernel-computable test certifying that no non-trivial 2-circuit cycle exists for any
`2 ≤ k ≤ K`. -/
def allTwoCircuitsRuledOut : Nat → Bool
  | 0 => true
  | 1 => true
  | k + 1 => twoCircuitKRuledOut (k + 1) && allTwoCircuitsRuledOut k

/-- Soundness of `checkTwoCircuitE₁` for all `2 ≤ e₁ ≤ bound`. -/
theorem checkTwoCircuitE₁_sound (k k₁ bound : Nat)
    (h : checkTwoCircuitE₁ k k₁ bound = true) :
    ∀ e₁ : Nat, 2 ≤ e₁ → e₁ ≤ bound → twoCircuitPairRuledOut k k₁ e₁ = true := by
  induction bound with
  | zero => intro e₁ he₁ hle; omega
  | succ b ih =>
    simp only [checkTwoCircuitE₁, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    intro e₁ he₁ hle
    by_cases heq : e₁ = b + 1
    · subst heq
      rcases h.1 with hlt | hok
      · omega
      · exact hok
    · exact ih h.2 e₁ he₁ (by omega)

/-- Soundness of `checkTwoCircuitK₁` for all `1 ≤ k₁ ≤ bound`. -/
theorem checkTwoCircuitK₁_sound (k bound : Nat)
    (h : checkTwoCircuitK₁ k bound = true) :
    ∀ k₁ e₁ : Nat, 1 ≤ k₁ → k₁ ≤ bound → 2 ≤ e₁ → e₁ ≤ minHalvings k - k →
      twoCircuitPairRuledOut k k₁ e₁ = true := by
  induction bound with
  | zero => intro k₁ _ hk₁ hle; omega
  | succ b ih =>
    simp only [checkTwoCircuitK₁, Bool.and_eq_true] at h
    intro k₁ e₁ hk₁ hle he₁ he₁le
    by_cases heq : k₁ = b + 1
    · subst heq
      exact checkTwoCircuitE₁_sound k (b + 1) (minHalvings k - k) h.1 e₁ he₁ he₁le
    · exact ih h.2 k₁ e₁ hk₁ (by omega) he₁ he₁le

/-- Soundness of `allTwoCircuitsRuledOut` for all `2 ≤ k ≤ K`. -/
theorem allTwoCircuitsRuledOut_sound (K : Nat) (h : allTwoCircuitsRuledOut K = true) :
    ∀ k : Nat, 2 ≤ k → k ≤ K → twoCircuitKRuledOut k = true := by
  induction K with
  | zero => intro k hk hle; omega
  | succ K ih =>
    cases K with
    | zero => intro k hk hle; omega
    | succ K =>
      simp only [allTwoCircuitsRuledOut, Bool.and_eq_true] at h
      intro k hk hle
      by_cases heq : k = K + 2
      · subst heq; exact h.1
      · exact ih h.2 k hk (by omega)

/-- Soundness of `twoCircuitKRuledOut` against `IsTwoCircuitCycle`. -/
theorem no_nontrivial_twoCircuit_of_ruledOut {n k₁ e₁ k₂ e₂ : Nat}
    (hcheck : twoCircuitKRuledOut (k₁ + k₂) = true) :
    ¬ IsTwoCircuitCycle n k₁ e₁ k₂ e₂ := by
  intro hcyc
  have hk₁ := hcyc.k₁_pos; have hk₂ := hcyc.k₂_pos
  have he₁ := hcyc.two_le_e₁; have he₂ := hcyc.two_le_e₂
  have hs := twoCircuit_totalVal_eq_minHalvings hcyc
  have he₁_le : e₁ ≤ minHalvings (k₁ + k₂) - (k₁ + k₂) := by omega
  have hpair : twoCircuitPairRuledOut (k₁ + k₂) k₁ e₁ = true :=
    checkTwoCircuitK₁_sound (k₁ + k₂) (k₁ + k₂ - 1) hcheck k₁ e₁ hk₁ (by omega) he₁ he₁_le
  have hk₂eq : k₁ + k₂ - k₁ = k₂ := by omega
  have he₂eq : minHalvings (k₁ + k₂) + 2 - (k₁ + k₂) - e₁ = e₂ := by omega
  have hprop :
      twoCircuitOffset k₁ e₁ k₂ e₂ < 3 * (2 ^ minHalvings (k₁ + k₂) - 3 ^ (k₁ + k₂)) ∨
        twoCircuitOffset k₁ e₁ k₂ e₂ % (2 ^ minHalvings (k₁ + k₂) - 3 ^ (k₁ + k₂)) ≠ 0 := by
    simpa [twoCircuitPairRuledOut, hk₂eq, he₂eq] using hpair
  have h3d := twoCircuit_three_mul_denom_le hcyc
  have hdvd := twoCircuit_cycle_dvd hcyc
  rw [hs] at hdvd
  have hmod := Nat.mod_eq_zero_of_dvd hdvd
  rcases hprop with hlt | hne
  · omega
  · exact hne hmod

/-- General bounded 2-circuit elimination driven by `allTwoCircuitsRuledOut`. -/
theorem no_nontrivial_twoCircuit_of_allRuledOut (K : Nat)
    (hcheck : allTwoCircuitsRuledOut K = true) :
    ∀ n k₁ e₁ k₂ e₂ : Nat, k₁ + k₂ ≤ K → ¬ IsTwoCircuitCycle n k₁ e₁ k₂ e₂ := by
  intro n k₁ e₁ k₂ e₂ hle hcyc
  have hk2 : 2 ≤ k₁ + k₂ := by have := hcyc.k₁_pos; have := hcyc.k₂_pos; omega
  exact no_nontrivial_twoCircuit_of_ruledOut
    (allTwoCircuitsRuledOut_sound K hcheck (k₁ + k₂) hk2 hle) hcyc

/-- **Exact Bounded 2-Circuit Elimination (`k₁ + k₂ ≤ 29`, kernel-verified, zero
`native_decide`):** there is no non-trivial positive 2-circuit Collatz cycle with
`k₁ + k₂ ≤ 29`. Covering up to `29` closes all small-`k` exceptions (`k ∈ {13, 15, 17, 22, 29}`)
where `4^k * (2^S - 3^k)^2 < 16 * 3^(3*k)` still holds for `S = minHalvings k`. -/
theorem no_nontrivial_twoCircuit_le_29 :
    ∀ n k₁ e₁ k₂ e₂ : Nat, k₁ + k₂ ≤ 29 → ¬ IsTwoCircuitCycle n k₁ e₁ k₂ e₂ :=
  no_nontrivial_twoCircuit_of_allRuledOut 29 (by decide)

/-- **Conditional Simons-Baker 2-Circuit Reduction:**
combining a Baker/Rhin-type Diophantine lower bound
`16 * 3 ^ (3 * k) ≤ 4 ^ k * (2 ^ S - 3 ^ k) ^ 2` for all `k > K₀` (with `3 ^ k < 2 ^ S`,
non-vacuous for `K₀ ≥ 29`) and finite elimination for `k ≤ K₀` rules out ALL non-trivial
positive 2-circuit Collatz cycles. -/
theorem no_nontrivial_twoCircuit_of_diophantine_bound (K₀ : Nat)
    (hBaker : ∀ k S : Nat, K₀ < k → 3 ^ k < 2 ^ S →
      16 * 3 ^ (3 * k) ≤ 4 ^ k * (2 ^ S - 3 ^ k) ^ 2)
    (hFin : ∀ n k₁ e₁ k₂ e₂ : Nat, k₁ + k₂ ≤ K₀ → ¬ IsTwoCircuitCycle n k₁ e₁ k₂ e₂) :
    ∀ n k₁ e₁ k₂ e₂ : Nat, ¬ IsTwoCircuitCycle n k₁ e₁ k₂ e₂ := by
  intro n k₁ e₁ k₂ e₂ hcyc
  by_cases hle : k₁ + k₂ ≤ K₀
  · exact hFin n k₁ e₁ k₂ e₂ hle hcyc
  · have hgt : K₀ < k₁ + k₂ := Nat.lt_of_not_ge hle
    have hlow := hBaker (k₁ + k₂) (k₁ + k₂ + e₁ + e₂ - 2) hgt hcyc.pow_lt
    have hup := twoCircuit_exp_gap_bound hcyc
    omega

/-- **Specialized Conditional Simons-Baker Reduction above `k = 29`:**
discharging `k₁ + k₂ ≤ 29` via `no_nontrivial_twoCircuit_le_29`. Every small-`k` counterexample
to `16 * 3^(3*k) ≤ 4^k * (2^S - 3^k)^2` (`k ∈ {13, 15, 17, 22, 29}`) lies in `k ≤ 29`, so the
remaining hypothesis `hBaker` for `k > 29` is genuinely non-vacuous and implied by Baker/Rhin
linear forms in logarithms for large `k`. -/
theorem no_nontrivial_twoCircuit_of_diophantine_bound_gt_29
    (hBaker : ∀ k S : Nat, 29 < k → 3 ^ k < 2 ^ S →
      16 * 3 ^ (3 * k) ≤ 4 ^ k * (2 ^ S - 3 ^ k) ^ 2) :
    ∀ n k₁ e₁ k₂ e₂ : Nat, ¬ IsTwoCircuitCycle n k₁ e₁ k₂ e₂ :=
  no_nontrivial_twoCircuit_of_diophantine_bound 29 hBaker no_nontrivial_twoCircuit_le_29

/-! ### 6. Explicit Barrier Separation (`Barriers 1, 3, and 4`) -/

/-- **Barrier 1 Separation (`3n - 1` on `ℕ⁺`):**
Both `n = 5` (`5 → 7 → 5`, `k = 2, S = 3`) and the genuine 2-circuit `n = 17`
(`twoCircuitVec 4 2 3 4 = [1, 1, 1, 2, 1, 1, 4]`, `k = 7, S = 11`) satisfy the `3n - 1`
cycle equation yet violate `3^k < 2^S` (`2^3 = 8 < 9 = 3^2` and `2^11 = 2048 < 2187 = 3^7`). -/
theorem barrier1_three_n_minus_one_separation :
    (Barriers.genIter 3 (-1) 5 5 = 5 ∧ ¬ (3 ^ 2 < 2 ^ 3)) ∧
    (Barriers.genIter 3 (-1) 18 17 = 17 ∧
      (3 ^ 7 - 2 ^ 11) * 17 = twoCircuitOffset 4 2 3 4 ∧
      ¬ (3 ^ 7 < 2 ^ 11)) := by
  exact ⟨⟨Barriers.three_n_minus_one_cycle_5.1, by decide⟩,
    ⟨by decide, by decide, by decide⟩⟩

/-- **Barrier 3 Separation (`3n + 1` on `ℤ_{<0}`):**
Both `n = -5` (`k = 2, S = 3`) and the genuine negative 2-circuit `n = -17`
(`twoCircuitVec 4 2 3 4`, `k = 7, S = 11`) satisfy the signed cycle equation
`((2 : Int)^S - 3^k) * n = C` yet violate positivity (`0 < n`) and `3^k < 2^S`. -/
theorem barrier3_neg_int_separation :
    (Barriers.genIter 3 1 5 (-5) = -5 ∧ ¬ (3 ^ 2 < 2 ^ 3)) ∧
    (Barriers.genIter 3 1 18 (-17) = -17 ∧
      ((2 : Int) ^ 11 - (3 : Int) ^ 7) * (-17) = (twoCircuitOffset 4 2 3 4 : Int) ∧
      ¬ (3 ^ 7 < 2 ^ 11)) := by
  exact ⟨⟨Barriers.neg_int_cycle_neg5.1, by decide⟩,
    ⟨by decide, by decide, by decide⟩⟩

/-- **Barrier 4 Separation (`ℤ₂` rational 2-circuit periodic points):**
Every canonical 2-circuit parity vector admits a periodic point in `ℤ_(2) ⊂ ℤ₂`; for
`(2, 2, 1, 2)` (`k = 3, S = 5`), `x = 23 / 5` satisfies BOTH `3^3 < 2^5` and `9 * 2^5 < 16 * 3^3`
yet fails global integrality in `ℕ⁺` (`¬ ∃ m : Int, x.Equiv (OddDenomRat.ofInt m)`). -/
theorem barrier4_twoAdic_twoCircuit_separation :
    let v := twoCircuitVec 2 2 1 2
    let x := periodicPoint v (by decide)
    3 ^ 3 < 2 ^ 5 ∧
    9 * 2 ^ 5 < 16 * 3 ^ 3 ∧
    x = ⟨23, 5, by decide⟩ ∧
    OddDenomRat.syracuseIter 3 x = x ∧
    OddDenomRat.syracuseValVec 3 x = v ∧
    (¬ ∃ m : Int, x.Equiv (OddDenomRat.ofInt m)) := by
  have hv : IsValidParityVec (twoCircuitVec 2 2 1 2) :=
    twoCircuitVec_valid (by decide) (by decide) (by decide) (by decide)
  rcases universal_twoAdic_periodicPoint hv with ⟨_, _, hcyc, hvec, _, _⟩
  have hx : periodicPoint (twoCircuitVec 2 2 1 2) (by decide) = ⟨23, 5, by decide⟩ := by decide
  have hnotInt :
      ¬ ∃ m : Int, (periodicPoint (twoCircuitVec 2 2 1 2) (by decide)).Equiv
        (OddDenomRat.ofInt m) := by
    rintro ⟨m, hm⟩
    rw [hx] at hm
    unfold OddDenomRat.Equiv OddDenomRat.ofInt at hm
    simp only at hm
    omega
  exact ⟨by decide, by decide, hx, hcyc, hvec, hnotInt⟩

end SolveCollatz
