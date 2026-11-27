/-
Copyright (c) 2026 The solve-collatz contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Collatz.Prove.Diophantine.TwoCircuit

/-!
# Simons–de Weger (2005) 3-Circuit Theory & Kernel Elimination (`PROVE-B1`)

Formalization of the exact 3-circuit Diophantine theory for the Collatz (`3n + 1`) conjecture,
advancing Track A node `PROVE-B1` (Phase 2):
1. Canonical 3-circuit parity vectors `threeCircuitVec k₁ e₁ k₂ e₂ k₃ e₃` (`mcircuit_hunter.c`),
   closed-form numerator `threeCircuitOffset`, and exact identity
   `parityOffset (threeCircuitVec k₁ e₁ k₂ e₂ k₃ e₃) = threeCircuitOffset k₁ e₁ k₂ e₂ k₃ e₃`.
2. `IsThreeCircuitCycle`, automatic positivity/nontriviality of the two intermediate valleys
   `3 ≤ syracuseIter k₁ n` and `3 ≤ syracuseIter (k₁ + k₂) n`, bridge to `HasNontrivialCycle`
   in frozen `Challenge.lean`, and exact cycle equation `(2 ^ S - 3 ^ K) * n = C₃`.
3. Exact Simons–de Weger 3-circuit band bound `27 * 2 ^ S < 64 * 3 ^ K`, yielding
   `2 ^ S < 4 * 3 ^ K` and the sharp two-value band `S = minHalvings K ∨ S = minHalvings K + 1`
   (ruling out `minHalvings K + 1` whenever `64 * 3 ^ K ≤ 27 * 2 ^ (minHalvings K + 1)`).
4. Kernel-verified bounded elimination (`decide`, zero `native_decide`) of ALL non-trivial
   positive 3-circuit cycles for `k₁ + k₂ + k₃ ≤ 12`.
5. Explicit barrier separations: Barrier 1 (`3n - 1` at `5`, `17`), Barrier 2 (`5n + 1` at `13`,
   where `5^3 < 2^7` holds yet `27 * 2^7 < 64 * 3^3` fails), Barrier 3 (`ℤ_{<0}` at `-5`, `-17`),
   Barrier 4 (`ℤ₂` rational 3-circuit periodic point `143 / 47` for `threeCircuitVec 1 2 1 2 2 2`
   satisfying both `3^4 < 2^7` and `27 * 2^7 < 64 * 3^4`), and Barrier 5 (fixed `m = 3` canonical
   circuits on `3n + 1`).
-/

@[expose] public section

namespace SolveCollatz

/-! ### 1. Elementary Multiplication Helpers -/

private theorem mul_four_rearrange3 (a b c d : Nat) :
    (a * b) * (c * d) = (a * c) * (b * d) := by
  rw [Nat.mul_assoc, Nat.mul_left_comm b c d, ← Nat.mul_assoc]

private theorem nat_mul_lt_mul3 {a b c d : Nat} (h1 : a < b) (h2 : c < d) :
    a * c < b * d :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul_right c (Nat.le_of_lt h1))
    ((Nat.mul_lt_mul_left (by omega : 0 < b)).mpr h2)

private theorem mul_six_rearrange (a b c d e f : Nat) :
    (a * b * c) * (d * e * f) = ((a * d) * (b * e)) * (c * f) := by
  rw [mul_four_rearrange3 (a * b) c (d * e) f, mul_four_rearrange3 a b d e]

/-! ### 2. Canonical 3-Circuit Parity Vectors & Closed-Form Numerator -/

/-- Canonical Simons–de Weger 3-circuit parity vector concatenating three 1-circuits
`(1^{k₁-1}, e₁)`, `(1^{k₂-1}, e₂)`, and `(1^{k₃-1}, e₃)`, matching `mcircuit_hunter.c`. -/
def threeCircuitVec (k₁ e₁ k₂ e₂ k₃ e₃ : Nat) : List Nat :=
  oneCircuitVec (k₁ - 1) e₁ ++ oneCircuitVec (k₂ - 1) e₂ ++ oneCircuitVec (k₃ - 1) e₃

/-- Closed-form Simons–de Weger 3-circuit cycle numerator
`C₃(k₁, e₁, k₂, e₂, k₃, _e₃) = 3^(k₂+k₃)*(3^k₁ - 2^k₁) + 2^(k₁+e₁-1)*(3^k₃*(3^k₂ - 2^k₂)) +`
`2^(k₁+k₂+e₁+e₂-2)*(3^k₃ - 2^k₃)`.
Note that `_e₃` only enters the cycle equation through the total halving count
`S = k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3`, mirroring `twoCircuitOffset`. -/
def threeCircuitOffset (k₁ e₁ k₂ e₂ k₃ _e₃ : Nat) : Nat :=
  3 ^ (k₂ + k₃) * (3 ^ k₁ - 2 ^ k₁) +
    2 ^ (k₁ + e₁ - 1) * (3 ^ k₃ * (3 ^ k₂ - 2 ^ k₂)) +
    2 ^ (k₁ + k₂ + e₁ + e₂ - 2) * (3 ^ k₃ - 2 ^ k₃)

/-- Total length of `threeCircuitVec k₁ e₁ k₂ e₂ k₃ e₃` is `k₁ + k₂ + k₃` for `1 ≤ k₁, k₂, k₃`. -/
theorem threeCircuitVec_length {k₁ e₁ k₂ e₂ k₃ e₃ : Nat}
    (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) (hk₃ : 1 ≤ k₃) :
    (threeCircuitVec k₁ e₁ k₂ e₂ k₃ e₃).length = k₁ + k₂ + k₃ := by
  simp only [threeCircuitVec, List.length_append, oneCircuitVec_length]
  omega

/-- Total halving count of `threeCircuitVec k₁ e₁ k₂ e₂ k₃ e₃` is
`k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3`. -/
theorem paritySum_threeCircuitVec {k₁ e₁ k₂ e₂ k₃ e₃ : Nat}
    (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) (hk₃ : 1 ≤ k₃) :
    paritySum (threeCircuitVec k₁ e₁ k₂ e₂ k₃ e₃) = k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3 := by
  simp only [threeCircuitVec, paritySum_append, paritySum_oneCircuitVec]
  omega

/-- Every canonical 3-circuit parity vector with positive exponents is a valid parity vector. -/
theorem threeCircuitVec_valid {k₁ e₁ k₂ e₂ k₃ e₃ : Nat}
    (hk₁ : 1 ≤ k₁) (he₁ : 1 ≤ e₁) (hk₂ : 1 ≤ k₂) (he₂ : 1 ≤ e₂)
    (hk₃ : 1 ≤ k₃) (he₃ : 1 ≤ e₃) :
    IsValidParityVec (threeCircuitVec k₁ e₁ k₂ e₂ k₃ e₃) := by
  refine ⟨?_, ?_⟩
  · intro hnil
    have hlen := threeCircuitVec_length (e₁ := e₁) (e₂ := e₂) (e₃ := e₃) hk₁ hk₂ hk₃
    rw [hnil] at hlen
    simp at hlen
    omega
  · intro a ha
    simp only [threeCircuitVec, oneCircuitVec, List.mem_append, List.mem_replicate,
      List.mem_singleton] at ha
    rcases ha with ((⟨_, rfl⟩ | rfl) | (⟨_, rfl⟩ | rfl)) | (⟨_, rfl⟩ | rfl) <;> omega

/-- **Exact 3-Circuit Closed-Form Numerator Identity (Simons–de Weger 2005):**
`parityOffset (threeCircuitVec k₁ e₁ k₂ e₂ k₃ e₃) = threeCircuitOffset k₁ e₁ k₂ e₂ k₃ e₃`
for all `1 ≤ k₁, k₂, k₃`. -/
theorem parityOffset_threeCircuitVec {k₁ e₁ k₂ e₂ k₃ e₃ : Nat}
    (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) (hk₃ : 1 ≤ k₃) :
    parityOffset (threeCircuitVec k₁ e₁ k₂ e₂ k₃ e₃) =
      threeCircuitOffset k₁ e₁ k₂ e₂ k₃ e₃ := by
  have hk₃' : k₃ - 1 + 1 = k₃ := by omega
  have hvec : threeCircuitVec k₁ e₁ k₂ e₂ k₃ e₃ =
      twoCircuitVec k₁ e₁ k₂ e₂ ++ oneCircuitVec (k₃ - 1) e₃ := rfl
  rw [hvec, parityOffset_append, oneCircuitVec_length, hk₃',
    parityOffset_twoCircuitVec hk₁ hk₂, paritySum_twoCircuitVec hk₁ hk₂,
    parityOffset_oneCircuitVec, hk₃']
  rw [threeCircuitOffset, Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_add,
    Nat.add_comm k₃ k₂, Nat.mul_left_comm (3 ^ k₃)]

/-! ### 3. `IsThreeCircuitCycle`, Bridge to `Challenge.lean`, and Cycle Equations -/

/-- A non-trivial positive 3-circuit Syracuse cycle starting at `n > 1` with circuit lengths
`k₁, k₂, k₃ ≥ 1` and terminal halving drops `e₁, e₂, e₃ ≥ 2`. -/
structure IsThreeCircuitCycle (n k₁ e₁ k₂ e₂ k₃ e₃ : Nat) : Prop where
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
  /-- Third circuit has at least one odd step (`k₃ ≥ 1`). -/
  k₃_pos : 1 ≤ k₃
  /-- Third circuit terminates in a drop of at least `2` halvings (`e₃ ≥ 2`). -/
  two_le_e₃ : 2 ≤ e₃
  /-- Periodicity under `k₁ + k₂ + k₃` accelerated Syracuse steps. -/
  period_eq : syracuseIter (k₁ + k₂ + k₃) n = n
  /-- Exact 3-circuit halving-exponent vector along the period. -/
  valVec_eq : syracuseValVec (k₁ + k₂ + k₃) n = threeCircuitVec k₁ e₁ k₂ e₂ k₃ e₃

/-- Every 3-circuit cycle starting point `n` is odd. -/
theorem IsThreeCircuitCycle.odd {n k₁ e₁ k₂ e₂ k₃ e₃ : Nat}
    (h : IsThreeCircuitCycle n k₁ e₁ k₂ e₂ k₃ e₃) : n % 2 = 1 := by
  rw [← h.period_eq]
  have hk : 0 < k₁ + k₂ + k₃ := by have := h.k₁_pos; omega
  exact syracuseIter_odd hk n

/-- Every non-trivial 3-circuit cycle starting point satisfies `3 ≤ n`. -/
theorem IsThreeCircuitCycle.three_le_n {n k₁ e₁ k₂ e₂ k₃ e₃ : Nat}
    (h : IsThreeCircuitCycle n k₁ e₁ k₂ e₂ k₃ e₃) : 3 ≤ n := by
  have hodd := h.odd
  have hgt := h.one_lt_n
  omega

/-- Along a 3-circuit cycle, total halving count equals `k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3`. -/
theorem IsThreeCircuitCycle.totalVal_eq {n k₁ e₁ k₂ e₂ k₃ e₃ : Nat}
    (h : IsThreeCircuitCycle n k₁ e₁ k₂ e₂ k₃ e₃) :
    syracuseTotalVal (k₁ + k₂ + k₃) n = k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3 := by
  rw [← paritySum_syracuseValVec, h.valVec_eq,
    paritySum_threeCircuitVec h.k₁_pos h.k₂_pos h.k₃_pos]

/-- Along a 3-circuit cycle, the affine numerator equals `threeCircuitOffset`. -/
theorem IsThreeCircuitCycle.offset_eq {n k₁ e₁ k₂ e₂ k₃ e₃ : Nat}
    (h : IsThreeCircuitCycle n k₁ e₁ k₂ e₂ k₃ e₃) :
    syracuseOffset (k₁ + k₂ + k₃) n = threeCircuitOffset k₁ e₁ k₂ e₂ k₃ e₃ := by
  rw [← parityOffset_syracuseValVec, h.valVec_eq,
    parityOffset_threeCircuitVec h.k₁_pos h.k₂_pos h.k₃_pos]

/-- Archimedean positivity inequality for 3-circuits: `3 ^ (k₁ + k₂ + k₃) < 2 ^ S`. -/
theorem threeCircuit_pow_lt {n k₁ e₁ k₂ e₂ k₃ e₃ : Nat}
    (h : IsThreeCircuitCycle n k₁ e₁ k₂ e₂ k₃ e₃) :
    3 ^ (k₁ + k₂ + k₃) < 2 ^ (k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3) := by
  have hk : 0 < k₁ + k₂ + k₃ := by have := h.k₁_pos; omega
  have hlt := syracuse_cycle_pow_lt hk h.period_eq
  rwa [h.totalVal_eq] at hlt

/-- **Bridge to Frozen `Challenge.lean`:** any `IsThreeCircuitCycle` witness yields
`HasNontrivialCycle` (and hence `CollatzDisproof`). -/
theorem IsThreeCircuitCycle.hasNontrivialCycle {n k₁ e₁ k₂ e₂ k₃ e₃ : Nat}
    (h : IsThreeCircuitCycle n k₁ e₁ k₂ e₂ k₃ e₃) : HasNontrivialCycle := by
  have hk : 0 < k₁ + k₂ + k₃ := by have := h.k₁_pos; omega
  refine hasNontrivialCycle_of_syracuse_cycle hk h.period_eq ?_
  intro i hi h1
  have hreach : syracuseIter (k₁ + k₂ + k₃) n = 1 := by
    calc syracuseIter (k₁ + k₂ + k₃) n
        = syracuseIter (i + (k₁ + k₂ + k₃ - i)) n := by
            rw [Nat.add_sub_of_le (Nat.le_of_lt hi)]
      _ = syracuseIter (k₁ + k₂ + k₃ - i) (syracuseIter i n) := (syracuseIter_add i _ n).symm
      _ = syracuseIter (k₁ + k₂ + k₃ - i) 1 := by rw [h1]
      _ = 1 := syracuseIter_one _
  rw [h.period_eq] at hreach
  have hgt := h.one_lt_n
  omega

/-- **Exact 3-Circuit Diophantine Cycle Equation (Simons–de Weger 2005):**
`(2 ^ S - 3 ^ K) * n = threeCircuitOffset k₁ e₁ k₂ e₂ k₃ e₃`. -/
theorem threeCircuit_cycle_eq {n k₁ e₁ k₂ e₂ k₃ e₃ : Nat}
    (h : IsThreeCircuitCycle n k₁ e₁ k₂ e₂ k₃ e₃) :
    (2 ^ (k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3) - 3 ^ (k₁ + k₂ + k₃)) * n =
      threeCircuitOffset k₁ e₁ k₂ e₂ k₃ e₃ := by
  have heq := syracuse_cycle_equation h.period_eq
  rw [h.totalVal_eq, h.offset_eq] at heq
  exact heq

/-- **Divisibility Condition (certifying `mcircuit_hunter.c`):**
every 3-circuit cycle satisfies `(2 ^ S - 3 ^ K) ∣ threeCircuitOffset k₁ e₁ k₂ e₂ k₃ e₃`. -/
theorem threeCircuit_cycle_dvd {n k₁ e₁ k₂ e₂ k₃ e₃ : Nat}
    (h : IsThreeCircuitCycle n k₁ e₁ k₂ e₂ k₃ e₃) :
    (2 ^ (k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3) - 3 ^ (k₁ + k₂ + k₃)) ∣
      threeCircuitOffset k₁ e₁ k₂ e₂ k₃ e₃ :=
  ⟨n, (threeCircuit_cycle_eq h).symm⟩

/-- For any non-trivial 3-circuit cycle (`3 ≤ n`), `3 * (2 ^ S - 3 ^ K) ≤ C₃`. -/
theorem threeCircuit_three_mul_denom_le {n k₁ e₁ k₂ e₂ k₃ e₃ : Nat}
    (h : IsThreeCircuitCycle n k₁ e₁ k₂ e₂ k₃ e₃) :
    3 * (2 ^ (k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3) - 3 ^ (k₁ + k₂ + k₃)) ≤
      threeCircuitOffset k₁ e₁ k₂ e₂ k₃ e₃ := by
  have heq := threeCircuit_cycle_eq h
  have hn3 := h.three_le_n
  have hmul : 3 * (2 ^ (k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3) - 3 ^ (k₁ + k₂ + k₃)) ≤
      (2 ^ (k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3) - 3 ^ (k₁ + k₂ + k₃)) * n := by
    rw [Nat.mul_comm 3]
    exact Nat.mul_le_mul_left _ hn3
  exact Nat.le_trans hmul (Nat.le_of_eq heq)

/-! ### 4. Block Splitting, Valley Nontriviality, & Simons–de Weger Band Bound -/

/-- Splitting the 3-circuit orbit at steps `k₁` and `k₁ + k₂` isolates all three 1-circuits at
the intermediate valleys `m₁ = syracuseIter k₁ n` and `m₂ = syracuseIter (k₁ + k₂) n`. -/
theorem syracuseValVec_split_threeCircuit {n k₁ e₁ k₂ e₂ k₃ e₃ : Nat}
    (h : IsThreeCircuitCycle n k₁ e₁ k₂ e₂ k₃ e₃) :
    let m₁ := syracuseIter k₁ n
    let m₂ := syracuseIter (k₁ + k₂) n
    syracuseValVec k₁ n = oneCircuitVec (k₁ - 1) e₁ ∧
      syracuseValVec k₂ m₁ = oneCircuitVec (k₂ - 1) e₂ ∧
      syracuseValVec k₃ m₂ = oneCircuitVec (k₃ - 1) e₃ ∧
      syracuseIter k₂ m₁ = m₂ ∧
      syracuseIter k₃ m₂ = n := by
  intro m₁ m₂
  have happ12 :
      syracuseValVec (k₁ + k₂) n ++ syracuseValVec k₃ m₂ =
        (oneCircuitVec (k₁ - 1) e₁ ++ oneCircuitVec (k₂ - 1) e₂) ++
          oneCircuitVec (k₃ - 1) e₃ := by
    rw [← syracuseValVec_add, h.valVec_eq, threeCircuitVec]
  have hlen12 : (syracuseValVec (k₁ + k₂) n).length =
      (oneCircuitVec (k₁ - 1) e₁ ++ oneCircuitVec (k₂ - 1) e₂).length := by
    rw [syracuseValVec_length, List.length_append, oneCircuitVec_length, oneCircuitVec_length]
    have := h.k₁_pos; have := h.k₂_pos; omega
  rcases List.append_inj happ12 hlen12 with ⟨h12, h3⟩
  have happ1 :
      syracuseValVec k₁ n ++ syracuseValVec k₂ m₁ =
        oneCircuitVec (k₁ - 1) e₁ ++ oneCircuitVec (k₂ - 1) e₂ := by
    rw [← syracuseValVec_add, h12]
  have hlen1 : (syracuseValVec k₁ n).length = (oneCircuitVec (k₁ - 1) e₁).length := by
    rw [syracuseValVec_length, oneCircuitVec_length]
    have := h.k₁_pos; omega
  rcases List.append_inj happ1 hlen1 with ⟨h1, h2⟩
  exact ⟨h1, h2, h3, syracuseIter_add k₁ k₂ n, by rw [syracuseIter_add, h.period_eq]⟩

private theorem valley_odd_and_three_le {j rest n : Nat}
    (hj : 0 < j) (hn : 1 < n) (hper : syracuseIter (j + rest) n = n) :
    syracuseIter j n % 2 = 1 ∧ 3 ≤ syracuseIter j n := by
  have hodd : syracuseIter j n % 2 = 1 := syracuseIter_odd hj n
  have hne1 : syracuseIter j n ≠ 1 := by
    intro h1
    have hret : syracuseIter rest (syracuseIter j n) = n := by
      rw [syracuseIter_add, hper]
    rw [h1, syracuseIter_one] at hret
    omega
  exact ⟨hodd, by omega⟩

/-- The first intermediate valley `m₁ = syracuseIter k₁ n` is automatically odd with `3 ≤ m₁`. -/
theorem threeCircuit_valley1_odd_and_three_le {n k₁ e₁ k₂ e₂ k₃ e₃ : Nat}
    (h : IsThreeCircuitCycle n k₁ e₁ k₂ e₂ k₃ e₃) :
    syracuseIter k₁ n % 2 = 1 ∧ 3 ≤ syracuseIter k₁ n :=
  valley_odd_and_three_le h.k₁_pos h.one_lt_n (by simpa [Nat.add_assoc] using h.period_eq)

/-- The second intermediate valley `m₂ = syracuseIter (k₁ + k₂) n` is automatically odd with
`3 ≤ m₂`. -/
theorem threeCircuit_valley2_odd_and_three_le {n k₁ e₁ k₂ e₂ k₃ e₃ : Nat}
    (h : IsThreeCircuitCycle n k₁ e₁ k₂ e₂ k₃ e₃) :
    syracuseIter (k₁ + k₂) n % 2 = 1 ∧ 3 ≤ syracuseIter (k₁ + k₂) n :=
  valley_odd_and_three_le (by have := h.k₁_pos; omega) h.one_lt_n h.period_eq

private theorem oneCircuit_block_ineq {k e a b : Nat} (hk : 1 ≤ k)
    (hvec : syracuseValVec k a = oneCircuitVec (k - 1) e)
    (hstep : syracuseIter k a = b) :
    2 ^ (k + e - 1) * b < 3 ^ k * (a + 1) := by
  have haff := syracuse_affine_vec_eq k a
  rw [hvec, hstep, paritySum_oneCircuitVec, parityOffset_oneCircuitVec] at haff
  have hsub : k - 1 + e = k + e - 1 := by omega
  have hinc : k - 1 + 1 = k := by omega
  rw [hsub, hinc] at haff
  have h23 : 2 ^ k < 3 ^ k := two_pow_lt_three_pow hk
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  rw [haff, Nat.mul_add, Nat.mul_one]
  omega

/-- Product of the three coupled strict circuit inequalities:
`2^S * (m₁ * m₂ * n) < 3^(k₁+k₂+k₃) * ((n + 1) * (m₁ + 1) * (m₂ + 1))`. -/
theorem threeCircuit_mul_ineq {n k₁ e₁ k₂ e₂ k₃ e₃ : Nat}
    (h : IsThreeCircuitCycle n k₁ e₁ k₂ e₂ k₃ e₃) :
    let m₁ := syracuseIter k₁ n
    let m₂ := syracuseIter (k₁ + k₂) n
    2 ^ (k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3) * (m₁ * m₂ * n) <
      3 ^ (k₁ + k₂ + k₃) * ((n + 1) * (m₁ + 1) * (m₂ + 1)) := by
  intro m₁ m₂
  rcases syracuseValVec_split_threeCircuit h with ⟨hv1, hv2, hv3, hs2, hs3⟩
  have h1 := oneCircuit_block_ineq h.k₁_pos hv1 rfl
  have h2 := oneCircuit_block_ineq h.k₂_pos hv2 hs2
  have h3 := oneCircuit_block_ineq h.k₃_pos hv3 hs3
  have hS : (k₁ + e₁ - 1) + (k₂ + e₂ - 1) + (k₃ + e₃ - 1) =
      k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3 := by
    have := h.k₁_pos; have := h.k₂_pos; have := h.k₃_pos
    have := h.two_le_e₁; have := h.two_le_e₂; have := h.two_le_e₃; omega
  have h12 := nat_mul_lt_mul3 h1 h2
  have h123 := nat_mul_lt_mul3 h12 h3
  calc 2 ^ (k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3) * (m₁ * m₂ * n)
      = (2 ^ (k₁ + e₁ - 1) * m₁ * (2 ^ (k₂ + e₂ - 1) * m₂)) * (2 ^ (k₃ + e₃ - 1) * n) := by
          rw [← hS, Nat.pow_add, Nat.pow_add, mul_six_rearrange]
    _ < (3 ^ k₁ * (n + 1) * (3 ^ k₂ * (m₁ + 1))) * (3 ^ k₃ * (m₂ + 1)) := h123
    _ = 3 ^ (k₁ + k₂ + k₃) * ((n + 1) * (m₁ + 1) * (m₂ + 1)) := by
          rw [Nat.pow_add, Nat.pow_add, mul_six_rearrange]

/-- **Exact Simons–de Weger 3-Circuit Band Bound (certifying `mcircuit_hunter.c`):**
every non-trivial 3-circuit satisfies `27 * 2 ^ S < 64 * 3 ^ (k₁ + k₂ + k₃)`. -/
theorem threeCircuit_simons_pow_bound {n k₁ e₁ k₂ e₂ k₃ e₃ : Nat}
    (h : IsThreeCircuitCycle n k₁ e₁ k₂ e₂ k₃ e₃) :
    27 * 2 ^ (k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3) < 64 * 3 ^ (k₁ + k₂ + k₃) := by
  let m₁ := syracuseIter k₁ n
  let m₂ := syracuseIter (k₁ + k₂) n
  have hn3 : 3 ≤ n := h.three_le_n
  have hm1_3 : 3 ≤ m₁ := (threeCircuit_valley1_odd_and_three_le h).2
  have hm2_3 : 3 ≤ m₂ := (threeCircuit_valley2_odd_and_three_le h).2
  have hpos : 0 < m₁ * m₂ * n := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have hmul := threeCircuit_mul_ineq h
  have h27 : 27 * ((n + 1) * (m₁ + 1) * (m₂ + 1)) ≤ 64 * (m₁ * m₂ * n) := by
    have h12 : 9 * ((n + 1) * (m₁ + 1)) ≤ 16 * (n * m₁) := by
      have h3n : 3 * (n + 1) ≤ 4 * n := by omega
      have h3m : 3 * (m₁ + 1) ≤ 4 * m₁ := by omega
      calc 9 * ((n + 1) * (m₁ + 1))
          = (3 * (n + 1)) * (3 * (m₁ + 1)) := by rw [← mul_four_rearrange3]
        _ ≤ (4 * n) * (4 * m₁) := Nat.mul_le_mul h3n h3m
        _ = 16 * (n * m₁) := by rw [mul_four_rearrange3]
    have h3m2 : 3 * (m₂ + 1) ≤ 4 * m₂ := by omega
    calc 27 * ((n + 1) * (m₁ + 1) * (m₂ + 1))
        = (9 * ((n + 1) * (m₁ + 1))) * (3 * (m₂ + 1)) := by
            rw [show (27 : Nat) = 9 * 3 by rfl, mul_four_rearrange3]
      _ ≤ (16 * (n * m₁)) * (4 * m₂) := Nat.mul_le_mul h12 h3m2
      _ = 64 * (m₁ * m₂ * n) := by
            rw [mul_four_rearrange3, show 16 * 4 = 64 by rfl, Nat.mul_comm n m₁,
              Nat.mul_assoc, Nat.mul_comm n m₂, ← Nat.mul_assoc, Nat.mul_assoc 64,
              ← Nat.mul_assoc m₁ m₂ n]
  have hcomb : (27 * 2 ^ (k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3)) * (m₁ * m₂ * n) <
      (64 * 3 ^ (k₁ + k₂ + k₃)) * (m₁ * m₂ * n) := by
    calc (27 * 2 ^ (k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3)) * (m₁ * m₂ * n)
        = 27 * (2 ^ (k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3) * (m₁ * m₂ * n)) := by rw [Nat.mul_assoc]
      _ < 27 * (3 ^ (k₁ + k₂ + k₃) * ((n + 1) * (m₁ + 1) * (m₂ + 1))) :=
          (Nat.mul_lt_mul_left (by decide : 0 < 27)).mpr hmul
      _ = 3 ^ (k₁ + k₂ + k₃) * (27 * ((n + 1) * (m₁ + 1) * (m₂ + 1))) := by
          rw [Nat.mul_left_comm]
      _ ≤ 3 ^ (k₁ + k₂ + k₃) * (64 * (m₁ * m₂ * n)) := Nat.mul_le_mul_left _ h27
      _ = (64 * 3 ^ (k₁ + k₂ + k₃)) * (m₁ * m₂ * n) := by
          rw [← Nat.mul_assoc, Nat.mul_comm (3 ^ (k₁ + k₂ + k₃)) 64]
  exact Nat.lt_of_mul_lt_mul_right hcomb

/-- **Band Upper Bound (`2^S < 4 * 3^K`):** every non-trivial 3-circuit satisfies
`2 ^ (k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3) < 4 * 3 ^ (k₁ + k₂ + k₃)`. -/
theorem threeCircuit_two_pow_lt_four_mul {n k₁ e₁ k₂ e₂ k₃ e₃ : Nat}
    (h : IsThreeCircuitCycle n k₁ e₁ k₂ e₂ k₃ e₃) :
    2 ^ (k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3) < 4 * 3 ^ (k₁ + k₂ + k₃) := by
  have h27 := threeCircuit_simons_pow_bound h
  omega

private theorem two_pow_minHalvings_pred_le {k : Nat} (hk : 0 < k) :
    1 ≤ minHalvings k ∧ 2 ^ (minHalvings k - 1) ≤ 3 ^ k := by
  have hspec :=
    findTwoExpAux_spec (2 * k + 1) (3 ^ k) 0 (Or.inl rfl)
      (by simpa [Nat.zero_add] using three_pow_lt_two_pow_double_succ k)
  have hgt : 3 ^ k < 2 ^ minHalvings k := by simpa [minHalvings] using hspec.1
  have hlo : minHalvings k = 0 ∨ 2 ^ (minHalvings k - 1) ≤ 3 ^ k := by
    simpa [minHalvings] using hspec.2
  have h3ge : 3 ≤ 3 ^ k := by
    simpa using Nat.pow_le_pow_right (by decide) hk
  have hne0 : minHalvings k ≠ 0 := by
    intro h0
    rw [h0] at hgt
    omega
  rcases hlo with h0 | hle
  · exact absurd h0 hne0
  · exact ⟨Nat.pos_of_ne_zero hne0, hle⟩

/-- **Sharp Two-Value Band Theorem (certifying `mcircuit_hunter.c`):**
for every non-trivial 3-circuit cycle, `S` is forced into `{minHalvings K, minHalvings K + 1}`. -/
theorem threeCircuit_totalVal_eq_minHalvings_or_succ {n k₁ e₁ k₂ e₂ k₃ e₃ : Nat}
    (h : IsThreeCircuitCycle n k₁ e₁ k₂ e₂ k₃ e₃) :
    k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3 = minHalvings (k₁ + k₂ + k₃) ∨
      k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3 = minHalvings (k₁ + k₂ + k₃) + 1 := by
  let k := k₁ + k₂ + k₃
  let s := k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3
  have hk : 0 < k := by have := h.k₁_pos; omega
  have hlow : 3 ^ k < 2 ^ s := threeCircuit_pow_lt h
  have hhi : 2 ^ s < 4 * 3 ^ k := threeCircuit_two_pow_lt_four_mul h
  obtain ⟨hmpos, hpred⟩ := two_pow_minHalvings_pred_le hk
  have hm_lt : 3 ^ k < 2 ^ minHalvings k := lt_two_pow_minHalvings k
  have hge_min : minHalvings k ≤ s := by
    by_cases hle : minHalvings k ≤ s
    · exact hle
    · have hle' : s ≤ minHalvings k - 1 := by omega
      have hpow : 2 ^ s ≤ 2 ^ (minHalvings k - 1) := Nat.pow_le_pow_right (by decide) hle'
      omega
  have hle_succ : s ≤ minHalvings k + 1 := by
    by_cases hle : s ≤ minHalvings k + 1
    · exact hle
    · have hge2 : minHalvings k + 2 ≤ s := by omega
      have hpow : 2 ^ (minHalvings k + 2) ≤ 2 ^ s := Nat.pow_le_pow_right (by decide) hge2
      rw [Nat.pow_add] at hpow
      omega
  dsimp only [k, s] at hge_min hle_succ
  omega

/-! ### 5. Kernel-Verified Bounded 3-Circuit Elimination (`k₁ + k₂ + k₃ ≤ 12`) -/

/-- Kernel-computable test ruling out a 3-circuit tuple `(k₁, e₁, k₂, e₂, k₃, e₃)` at `(k, s)`
with `k₃ = k - k₁ - k₂` and `e₃ = s + 3 - k - e₁ - e₂`: either `C₃ < 3 * (2^s - 3^k)` or
`(2^s - 3^k) ∤ C₃`. -/
def threeCircuitTupleRuledOut (k s k₁ k₂ e₁ e₂ : Nat) : Bool :=
  let k₃ := k - k₁ - k₂
  let e₃ := s + 3 - k - e₁ - e₂
  let d := 2 ^ s - 3 ^ k
  let c := threeCircuitOffset k₁ e₁ k₂ e₂ k₃ e₃
  decide (c < 3 * d ∨ c % d ≠ 0)

/-- Check all `e₂` with `2 ≤ e₂ ≤ bound` for fixed `(k, s, k₁, k₂, e₁)`. -/
def checkThreeCircuitE₂ (k s k₁ k₂ e₁ : Nat) : Nat → Bool
  | 0 => true
  | e₂ + 1 =>
    (e₂ + 1 < 2 || threeCircuitTupleRuledOut k s k₁ k₂ e₁ (e₂ + 1)) &&
      checkThreeCircuitE₂ k s k₁ k₂ e₁ e₂

/-- Check all `e₁` with `2 ≤ e₁ ≤ bound` for fixed `(k, s, k₁, k₂)`. -/
def checkThreeCircuitE₁ (k s k₁ k₂ : Nat) : Nat → Bool
  | 0 => true
  | e₁ + 1 =>
    (e₁ + 1 < 2 || checkThreeCircuitE₂ k s k₁ k₂ (e₁ + 1) (s + 1 - k - (e₁ + 1))) &&
      checkThreeCircuitE₁ k s k₁ k₂ e₁

/-- Check all `k₂` with `1 ≤ k₂ ≤ bound` for fixed `(k, s, k₁)`. -/
def checkThreeCircuitK₂ (k s k₁ : Nat) : Nat → Bool
  | 0 => true
  | k₂ + 1 =>
    checkThreeCircuitE₁ k s k₁ (k₂ + 1) (s - k - 1) && checkThreeCircuitK₂ k s k₁ k₂

/-- Check all `k₁` with `1 ≤ k₁ ≤ bound` for fixed `(k, s)`. -/
def checkThreeCircuitK₁ (k s : Nat) : Nat → Bool
  | 0 => true
  | k₁ + 1 =>
    checkThreeCircuitK₂ k s (k₁ + 1) (k - (k₁ + 1) - 1) && checkThreeCircuitK₁ k s k₁

/-- Kernel-computable check at `(k, s)`: either `27 * 2^s ≥ 64 * 3^k` (band exclusion) or every
valid 3-circuit tuple `(k₁, e₁, k₂, e₂, k₃, e₃)` fails `3 * D ≤ C₃ ∧ D ∣ C₃`. -/
def threeCircuitKSRuledOut (k s : Nat) : Bool :=
  decide (64 * 3 ^ k ≤ 27 * 2 ^ s) || checkThreeCircuitK₁ k s (k - 2)

/-- Kernel-computable test certifying that no non-trivial 3-circuit cycle of odd length `k`
exists, checking both `s = minHalvings k` and `s = minHalvings k + 1`. -/
def threeCircuitKRuledOut (k : Nat) : Bool :=
  let s := minHalvings k
  threeCircuitKSRuledOut k s && threeCircuitKSRuledOut k (s + 1)

/-- Kernel-computable test certifying that no non-trivial 3-circuit cycle exists for any
`3 ≤ k ≤ K`. -/
def allThreeCircuitsRuledOut : Nat → Bool
  | 0 => true
  | 1 => true
  | 2 => true
  | k + 1 => threeCircuitKRuledOut (k + 1) && allThreeCircuitsRuledOut k

private theorem checkThreeCircuitE₂_sound (k s k₁ k₂ e₁ bound : Nat)
    (h : checkThreeCircuitE₂ k s k₁ k₂ e₁ bound = true) :
    ∀ e₂ : Nat, 2 ≤ e₂ → e₂ ≤ bound → threeCircuitTupleRuledOut k s k₁ k₂ e₁ e₂ = true := by
  induction bound with
  | zero => intro e₂ he₂ hle; omega
  | succ b ih =>
    simp only [checkThreeCircuitE₂, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    intro e₂ he₂ hle
    by_cases heq : e₂ = b + 1
    · subst heq
      rcases h.1 with hlt | hok
      · omega
      · exact hok
    · exact ih h.2 e₂ he₂ (by omega)

private theorem checkThreeCircuitE₁_sound (k s k₁ k₂ bound : Nat)
    (h : checkThreeCircuitE₁ k s k₁ k₂ bound = true) :
    ∀ e₁ e₂ : Nat, 2 ≤ e₁ → e₁ ≤ bound → 2 ≤ e₂ → e₂ ≤ s + 1 - k - e₁ →
      threeCircuitTupleRuledOut k s k₁ k₂ e₁ e₂ = true := by
  induction bound with
  | zero => intro e₁ _ he₁ hle; omega
  | succ b ih =>
    simp only [checkThreeCircuitE₁, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    intro e₁ e₂ he₁ hle he₂ he₂le
    by_cases heq : e₁ = b + 1
    · subst heq
      rcases h.1 with hlt | hok
      · omega
      · exact checkThreeCircuitE₂_sound k s k₁ k₂ (b + 1) (s + 1 - k - (b + 1)) hok e₂ he₂ he₂le
    · exact ih h.2 e₁ e₂ he₁ (by omega) he₂ he₂le

private theorem checkThreeCircuitK₂_sound (k s k₁ bound : Nat)
    (h : checkThreeCircuitK₂ k s k₁ bound = true) :
    ∀ k₂ e₁ e₂ : Nat, 1 ≤ k₂ → k₂ ≤ bound → 2 ≤ e₁ → e₁ ≤ s - k - 1 →
      2 ≤ e₂ → e₂ ≤ s + 1 - k - e₁ →
      threeCircuitTupleRuledOut k s k₁ k₂ e₁ e₂ = true := by
  induction bound with
  | zero => intro k₂ _ _ hk₂ hle; omega
  | succ b ih =>
    simp only [checkThreeCircuitK₂, Bool.and_eq_true] at h
    intro k₂ e₁ e₂ hk₂ hle he₁ he₁le he₂ he₂le
    by_cases heq : k₂ = b + 1
    · subst heq
      exact checkThreeCircuitE₁_sound k s k₁ (b + 1) (s - k - 1) h.1 e₁ e₂ he₁ he₁le he₂ he₂le
    · exact ih h.2 k₂ e₁ e₂ hk₂ (by omega) he₁ he₁le he₂ he₂le

private theorem checkThreeCircuitK₁_sound (k s bound : Nat)
    (h : checkThreeCircuitK₁ k s bound = true) :
    ∀ k₁ k₂ e₁ e₂ : Nat, 1 ≤ k₁ → k₁ ≤ bound → 1 ≤ k₂ → k₂ ≤ k - k₁ - 1 →
      2 ≤ e₁ → e₁ ≤ s - k - 1 → 2 ≤ e₂ → e₂ ≤ s + 1 - k - e₁ →
      threeCircuitTupleRuledOut k s k₁ k₂ e₁ e₂ = true := by
  induction bound with
  | zero => intro k₁ _ _ _ hk₁ hle; omega
  | succ b ih =>
    simp only [checkThreeCircuitK₁, Bool.and_eq_true] at h
    intro k₁ k₂ e₁ e₂ hk₁ hle hk₂ hk₂le he₁ he₁le he₂ he₂le
    by_cases heq : k₁ = b + 1
    · subst heq
      exact checkThreeCircuitK₂_sound k s (b + 1) (k - (b + 1) - 1) h.1 k₂ e₁ e₂
        hk₂ hk₂le he₁ he₁le he₂ he₂le
    · exact ih h.2 k₁ k₂ e₁ e₂ hk₁ (by omega) hk₂ hk₂le he₁ he₁le he₂ he₂le

/-- Soundness of `allThreeCircuitsRuledOut` for all `3 ≤ k ≤ K`. -/
theorem allThreeCircuitsRuledOut_sound (K : Nat) (h : allThreeCircuitsRuledOut K = true) :
    ∀ k : Nat, 3 ≤ k → k ≤ K → threeCircuitKRuledOut k = true := by
  induction K with
  | zero => intro k hk hle; omega
  | succ K ih =>
    cases K with
    | zero => intro k hk hle; omega
    | succ K =>
      cases K with
      | zero => intro k hk hle; omega
      | succ K =>
        simp only [allThreeCircuitsRuledOut, Bool.and_eq_true] at h
        intro k hk hle
        by_cases heq : k = K + 3
        · subst heq; exact h.1
        · exact ih h.2 k hk (by omega)

/-- Soundness of `threeCircuitKRuledOut` against `IsThreeCircuitCycle`. -/
theorem no_nontrivial_threeCircuit_of_ruledOut {n k₁ e₁ k₂ e₂ k₃ e₃ : Nat}
    (hcheck : threeCircuitKRuledOut (k₁ + k₂ + k₃) = true) :
    ¬ IsThreeCircuitCycle n k₁ e₁ k₂ e₂ k₃ e₃ := by
  intro hcyc
  let k := k₁ + k₂ + k₃
  let s := k + e₁ + e₂ + e₃ - 3
  have hk₁ := hcyc.k₁_pos; have hk₂ := hcyc.k₂_pos; have hk₃ := hcyc.k₃_pos
  have he₁ := hcyc.two_le_e₁; have he₂ := hcyc.two_le_e₂; have he₃ := hcyc.two_le_e₃
  have hs_band := threeCircuit_totalVal_eq_minHalvings_or_succ hcyc
  have hks : threeCircuitKSRuledOut k s = true := by
    simp only [threeCircuitKRuledOut, Bool.and_eq_true] at hcheck
    rcases hs_band with hs0 | hs1
    · rw [show s = minHalvings k from hs0]; exact hcheck.1
    · rw [show s = minHalvings k + 1 from hs1]; exact hcheck.2
  have hsim : 27 * 2 ^ s < 64 * 3 ^ k := threeCircuit_simons_pow_bound hcyc
  simp only [threeCircuitKSRuledOut, Bool.or_eq_true, decide_eq_true_eq] at hks
  have hchk1 : checkThreeCircuitK₁ k s (k - 2) = true := by
    rcases hks with hge | hok
    · omega
    · exact hok
  have hk₂₃ : 2 ^ k < 3 ^ k := two_pow_lt_three_pow (by omega)
  have hpow : 3 ^ k < 2 ^ s := threeCircuit_pow_lt hcyc
  have hk_lt_s : k < s := by
    by_cases hlt : k < s
    · exact hlt
    · have h2 : 2 ^ s ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
      omega
  have htup : threeCircuitTupleRuledOut k s k₁ k₂ e₁ e₂ = true :=
    checkThreeCircuitK₁_sound k s (k - 2) hchk1 k₁ k₂ e₁ e₂
      hk₁ (by omega) hk₂ (by omega) he₁ (by omega) he₂ (by omega)
  have hk₃eq : k - k₁ - k₂ = k₃ := by omega
  have he₃eq : s + 3 - k - e₁ - e₂ = e₃ := by omega
  have hprop :
      threeCircuitOffset k₁ e₁ k₂ e₂ k₃ e₃ < 3 * (2 ^ s - 3 ^ k) ∨
        threeCircuitOffset k₁ e₁ k₂ e₂ k₃ e₃ % (2 ^ s - 3 ^ k) ≠ 0 := by
    simpa [threeCircuitTupleRuledOut, hk₃eq, he₃eq] using htup
  have h3d : 3 * (2 ^ s - 3 ^ k) ≤ threeCircuitOffset k₁ e₁ k₂ e₂ k₃ e₃ :=
    threeCircuit_three_mul_denom_le hcyc
  have hmod : threeCircuitOffset k₁ e₁ k₂ e₂ k₃ e₃ % (2 ^ s - 3 ^ k) = 0 :=
    Nat.mod_eq_zero_of_dvd (threeCircuit_cycle_dvd hcyc)
  rcases hprop with hlt | hne
  · omega
  · exact hne hmod

/-- General bounded 3-circuit elimination driven by `allThreeCircuitsRuledOut`. -/
theorem no_nontrivial_threeCircuit_of_allRuledOut (K : Nat)
    (hcheck : allThreeCircuitsRuledOut K = true) :
    ∀ n k₁ e₁ k₂ e₂ k₃ e₃ : Nat, k₁ + k₂ + k₃ ≤ K →
      ¬ IsThreeCircuitCycle n k₁ e₁ k₂ e₂ k₃ e₃ := by
  intro n k₁ e₁ k₂ e₂ k₃ e₃ hle hcyc
  have hk3 : 3 ≤ k₁ + k₂ + k₃ := by
    have := hcyc.k₁_pos; have := hcyc.k₂_pos; have := hcyc.k₃_pos; omega
  exact no_nontrivial_threeCircuit_of_ruledOut
    (allThreeCircuitsRuledOut_sound K hcheck (k₁ + k₂ + k₃) hk3 hle) hcyc

/-- **Exact Bounded 3-Circuit Elimination (`k₁ + k₂ + k₃ ≤ 12`, kernel-verified, zero
`native_decide`):** there is no non-trivial positive 3-circuit Collatz cycle with
`k₁ + k₂ + k₃ ≤ 12`. -/
theorem no_nontrivial_threeCircuit_le_12 :
    ∀ n k₁ e₁ k₂ e₂ k₃ e₃ : Nat, k₁ + k₂ + k₃ ≤ 12 →
      ¬ IsThreeCircuitCycle n k₁ e₁ k₂ e₂ k₃ e₃ :=
  no_nontrivial_threeCircuit_of_allRuledOut 12 (by decide)

/-! ### 6. Explicit Barrier Separations (`Barriers 1–5`) -/

/-- **Barrier 1, 2, 3 & 5 Separation (`3n - 1`, `5n + 1`, `ℤ_{<0}`, and Conway undecidability):**
1. Barrier 1 (`3n - 1` on `ℕ⁺`): `n = 5` and the 2-circuit `n = 17` satisfy the `3n - 1` cycle
   equation yet violate `3^K < 2^S` (`2^3 < 3^2`, `2^11 < 3^7`).
2. Barrier 2 (`5n + 1` on `ℕ⁺`): `n = 13` (`k = 3, S = 7`) satisfies `5^3 < 2^7` yet violates
   `27 * 2^7 < 64 * 3^3` (`3456 < 1728` is false), showing `threeCircuit_simons_pow_bound` relies
   on `3n + 1`'s negative average drift `log₂(3/4) < 0`.
3. Barrier 3 (`3n + 1` on `ℤ_{<0}`): `-5` and `-17` violate positivity `3 ≤ n` and `3^K < 2^S`.
4. Barrier 5 (Conway 1972): all theorems here fix `3n + 1` on canonical `m = 3` circuits. -/
theorem barrier123_threeCircuit_separation :
    (Barriers.genIter 3 (-1) 5 5 = 5 ∧ ¬ (3 ^ 2 < 2 ^ 3)) ∧
    (Barriers.genIter 5 1 10 13 = 13 ∧ 5 ^ 3 < 2 ^ 7 ∧ ¬ (27 * 2 ^ 7 < 64 * 3 ^ 3)) ∧
    (Barriers.genIter 3 1 5 (-5) = -5 ∧ ¬ (3 ^ 2 < 2 ^ 3)) := by
  exact ⟨⟨Barriers.three_n_minus_one_cycle_5.1, by decide⟩,
    ⟨Barriers.five_n_plus_one_cycle_13.1, by decide, by decide⟩,
    ⟨Barriers.neg_int_cycle_neg5.1, by decide⟩⟩

/-- **Barrier 4 Separation (`ℤ₂` rational 3-circuit periodic points):**
For `(k₁, e₁, k₂, e₂, k₃, e₃) = (1, 2, 1, 2, 2, 2)` (`K = 4, S = 7`, `v = [2, 2, 1, 2]`),
`x = 143 / 47 ∈ ℤ_(2) ⊂ ℤ₂` satisfies BOTH `3^4 < 2^7` AND the Simons–de Weger 3-circuit band
bound `27 * 2^7 < 64 * 3^4`, is strictly positive (`3 < 143/47`), has exact Syracuse period `4`
with halving vector `v`, yet fails global integrality (`¬ ∃ m : Int, x.Equiv (ofInt m)`). -/
theorem barrier4_twoAdic_threeCircuit_separation :
    let v := threeCircuitVec 1 2 1 2 2 2
    let x := periodicPoint v (by decide)
    3 ^ 4 < 2 ^ 7 ∧
    27 * 2 ^ 7 < 64 * 3 ^ 4 ∧
    x = ⟨143, 47, by decide⟩ ∧
    OddDenomRat.syracuseIter 4 x = x ∧
    OddDenomRat.syracuseValVec 4 x = v ∧
    (¬ ∃ m : Int, x.Equiv (OddDenomRat.ofInt m)) := by
  have hv : IsValidParityVec (threeCircuitVec 1 2 1 2 2 2) :=
    threeCircuitVec_valid (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rcases universal_twoAdic_periodicPoint hv with ⟨_, _, hcyc, hvec, _, _⟩
  have hx : periodicPoint (threeCircuitVec 1 2 1 2 2 2) (by decide) = ⟨143, 47, by decide⟩ := by
    decide
  have hnotInt :
      ¬ ∃ m : Int, (periodicPoint (threeCircuitVec 1 2 1 2 2 2) (by decide)).Equiv
        (OddDenomRat.ofInt m) := by
    rintro ⟨m, hm⟩
    rw [hx] at hm
    unfold OddDenomRat.Equiv OddDenomRat.ofInt at hm
    simp only at hm
    omega
  exact ⟨by decide, by decide, hx, hcyc, hvec, hnotInt⟩

end SolveCollatz
