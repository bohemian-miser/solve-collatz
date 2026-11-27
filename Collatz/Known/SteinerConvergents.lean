/-
Copyright (c) 2026 The solve-collatz contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Collatz.Known.EliahouConvergents

/-!
# Unconditional 1-Circuit Elimination via Continued Fractions (`KNOWN-002` Phase 2)

Formalization in pure Lean 4 core (zero Mathlib, zero `sorry`, zero `native_decide`):
1. Pure-`Nat` difference-of-powers, reverse-Bernoulli upper bound `(N + 1) ^ Q ≤ 2 * N ^ Q` for
   `2 * Q ≤ N`, and Farey-determinant divisibility helpers.
2. **Steiner-Legendre Convergent Exclusion Lemma** (`steiner_legendre_convergent_exclusion`):
   given Farey neighbors `pL / qL < log₂(3) < pU / qU` (`2 ^ pL < 3 ^ qL`, `3 ^ qU < 2 ^ pU`,
   `pU * qL = pL * qU + 1`) with `3 ^ qU ≤ 2 ^ c * (2 ^ pU - 3 ^ qU)` (`c + 1 ≤ qU`), every
   parameter pair `(k, S)` satisfying `3 ^ k < 2 ^ S`, `2 ^ (k - 1) * (2 ^ S - 3 ^ k) < 3 ^ k`,
   `2 * qU ≤ 2 ^ (k - 1)`, and `k < qU + qL` is impossible.
3. Extended `log₂(3)` continued-fraction convergent `(p₁₄, q₁₄) = (16785921, 10590737)` paired with
   upper convergent `(p₁₃, q₁₃) = (301994, 190537)`, eliminating ALL non-trivial positive Steiner
   1-circuits for `1 ≤ k ≤ 10781273` (a `539,063x` leap over `1 ≤ k ≤ 20`, including
   `k ≤ 15600`, `k ≤ 31866`, and `k ≤ 10^7`), yielding unconditional bounds `10781274 ≤ k`,
   `17087915 ≤ S`, and total Collatz cycle length `27869189 ≤ k + S`, bridged directly to frozen
   `Challenge.lean` and sharpening `no_nontrivial_oneCircuit_of_diophantine_bound_gt_20`.
4. Explicit **Barrier 1–5 separations** (`3n - 1` at `n = 5`, `5n + 1` at `n = 1, 13`, `ℤ_{<0}`
   at `n = -5`, `ℤ₂` rational 1-circuit `211 / 13`, and Conway finite-horizon obstruction).
-/

@[expose] public section

namespace SolveCollatz

/-! ### 1. Pure-`Nat` Power, Reverse-Bernoulli, and Farey Divisibility Helpers -/

/-- Lower difference-of-powers bound: for `b ≤ a` and `1 ≤ d`,
`(a - b) * b ^ (d - 1) ≤ a ^ d - b ^ d`. -/
theorem pow_sub_pow_ge_mul_sub {a b d : Nat} (hba : b ≤ a) (hd : 1 ≤ d) :
    (a - b) * b ^ (d - 1) ≤ a ^ d - b ^ d := by
  cases d with
  | zero => omega
  | succ k =>
    cases k with
    | zero => simp
    | succ k =>
      have heq := pow_succ_sub_pow_succ b a (k + 1) hba
      have hpow : b ^ (k + 1) ≤ a ^ (k + 1) := Nat.pow_le_pow_left hba (k + 1)
      have hmul : (a - b) * b ^ (k + 1) ≤ a ^ (k + 1) * (a - b) := by
        rw [Nat.mul_comm]
        exact Nat.mul_le_mul_right (a - b) hpow
      simp only [Nat.add_sub_cancel]
      omega

/-- Reverse-Bernoulli factor-of-two bound: whenever `0 < N` and `2 * Q ≤ N`,
`(N + 1) ^ Q ≤ 2 * N ^ Q`. -/
theorem succ_pow_le_two_mul_pow {N Q : Nat} (hN : 0 < N) (hNQ : 2 * Q ≤ N) :
    (N + 1) ^ Q ≤ 2 * N ^ Q := by
  have hbern : (N + 1) ^ Q * (N - Q) ≤ N ^ (Q + 1) := succ_pow_mul_sub_le N Q (by omega)
  have h2 : N ≤ 2 * (N - Q) := by omega
  have hmul : (N + 1) ^ Q * N ≤ (2 * N ^ Q) * N := by
    calc (N + 1) ^ Q * N
        ≤ (N + 1) ^ Q * (2 * (N - Q)) := Nat.mul_le_mul_left _ h2
      _ = 2 * ((N + 1) ^ Q * (N - Q)) := by ac_rfl
      _ ≤ 2 * N ^ (Q + 1) := Nat.mul_le_mul_left 2 hbern
      _ = (2 * N ^ Q) * N := by rw [Nat.pow_succ]; ac_rfl
  exact Nat.le_of_mul_le_mul_right hmul hN

/-- Farey-determinant divisibility: if `pU * qL = pL * qU + 1`, `0 < qU`, `0 < k`, and
`pU * k = qU * S`, then `(k, S) = d * (qU, pU)` for some `1 ≤ d`. -/
theorem farey_eq_mul_imp_dvd {pL qL pU qU k S : Nat}
    (hqU : 0 < qU) (hk : 0 < k) (hdet : pU * qL = pL * qU + 1) (heq : pU * k = qU * S) :
    ∃ d : Nat, 1 ≤ d ∧ k = d * qU ∧ S = d * pU := by
  have h1 : qU * (S * qL) = qU * (pL * k) + k := by
    calc qU * (S * qL) = (qU * S) * qL := by ac_rfl
      _ = (pU * k) * qL := by rw [heq]
      _ = (pU * qL) * k := by ac_rfl
      _ = (pL * qU + 1) * k := by rw [hdet]
      _ = qU * (pL * k) + k := by rw [Nat.add_mul, Nat.one_mul]; ac_rfl
  let d := S * qL - pL * k
  have hk_eq : k = d * qU := by
    have hmul : qU * d = k := by rw [Nat.mul_sub]; omega
    rw [Nat.mul_comm] at hmul
    exact hmul.symm
  have hd_pos : 1 ≤ d := by
    by_cases hd0 : d = 0
    · rw [hd0, Nat.zero_mul] at hk_eq; omega
    · omega
  have hS_eq : S = d * pU := by
    have hqS : qU * S = qU * (d * pU) := by
      calc qU * S = pU * k := heq.symm
        _ = pU * (d * qU) := by rw [hk_eq]
        _ = qU * (d * pU) := by ac_rfl
    exact Nat.eq_of_mul_eq_mul_left hqU hqS
  exact ⟨d, hd_pos, hk_eq, hS_eq⟩

/-! ### 2. Pure-`Nat` Steiner-Legendre Convergent Exclusion Lemma -/

/-- Exact-multiple branch of the Steiner-Legendre convergent exclusion: if `(k, S) = d * (qU, pU)`
with `1 ≤ d` and `3 ^ qU ≤ 2 ^ c * (2 ^ pU - 3 ^ qU)` (`c + 1 ≤ qU`), then
`3 ^ k ≤ 2 ^ (k - 1) * (2 ^ S - 3 ^ k)`. -/
private theorem steiner_convergent_eq_case {pU qU c k S d : Nat}
    (hU : 3 ^ qU < 2 ^ pU) (hc : c + 1 ≤ qU) (hself : 3 ^ qU ≤ 2 ^ c * (2 ^ pU - 3 ^ qU))
    (hd : 1 ≤ d) (hk_eq : k = d * qU) (hS_eq : S = d * pU) :
    3 ^ k ≤ 2 ^ (k - 1) * (2 ^ S - 3 ^ k) := by
  have hk_ge : qU ≤ k := by
    rw [hk_eq]
    simpa using Nat.mul_le_mul_right qU hd
  have h2c : 2 ^ c ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hdiff := pow_sub_pow_ge_mul_sub (Nat.le_of_lt hU) hd
  have hS_pow : (2 ^ pU) ^ d = 2 ^ S := by rw [← Nat.pow_mul, Nat.mul_comm pU d, ← hS_eq]
  have hk_pow : (3 ^ qU) ^ d = 3 ^ k := by rw [← Nat.pow_mul, Nat.mul_comm qU d, ← hk_eq]
  rw [hS_pow, hk_pow] at hdiff
  have h3pow : 3 ^ k = 3 ^ qU * (3 ^ qU) ^ (d - 1) := by
    have hd1 : (d - 1) + 1 = d := by omega
    calc 3 ^ k = (3 ^ qU) ^ d := hk_pow.symm
      _ = (3 ^ qU) ^ ((d - 1) + 1) := by rw [hd1]
      _ = 3 ^ qU * (3 ^ qU) ^ (d - 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  calc 3 ^ k = 3 ^ qU * (3 ^ qU) ^ (d - 1) := h3pow
    _ ≤ (2 ^ c * (2 ^ pU - 3 ^ qU)) * (3 ^ qU) ^ (d - 1) := Nat.mul_le_mul_right _ hself
    _ = 2 ^ c * ((2 ^ pU - 3 ^ qU) * (3 ^ qU) ^ (d - 1)) := by rw [Nat.mul_assoc]
    _ ≤ 2 ^ (k - 1) * (2 ^ S - 3 ^ k) := Nat.mul_le_mul h2c hdiff

/-- Strict-ratio branch of the Steiner-Legendre convergent exclusion: `pU * k < qU * S` with
`3 ^ qU < 2 ^ pU` and `2 * qU ≤ 2 ^ (k - 1)` contradicts `2 ^ (k - 1) * (2 ^ S - 3 ^ k) < 3 ^ k`. -/
private theorem steiner_convergent_lt_case {pU qU k S : Nat}
    (hqU : 0 < qU) (hkpos : 1 ≤ k) (hU : 3 ^ qU < 2 ^ pU) (hlt : pU * k < qU * S)
    (hk_lo : 2 * qU ≤ 2 ^ (k - 1)) (hpow : 3 ^ k < 2 ^ S)
    (hgap : 2 ^ (k - 1) * (2 ^ S - 3 ^ k) < 3 ^ k) : False := by
  have h2low : 2 * (3 ^ qU) ^ k < (2 ^ S) ^ qU := by
    have h32 : (3 ^ qU) ^ k < (2 ^ pU) ^ k := Nat.pow_lt_pow_left hU (by omega)
    calc 2 * (3 ^ qU) ^ k < 2 * (2 ^ pU) ^ k := Nat.mul_lt_mul_of_pos_left h32 (by decide)
      _ = 2 ^ (pU * k + 1) := by rw [← Nat.pow_mul, Nat.pow_succ, Nat.mul_comm]
      _ ≤ 2 ^ (qU * S) := Nat.pow_le_pow_right (by decide) hlt
      _ = (2 ^ S) ^ qU := by rw [Nat.mul_comm qU S, Nat.pow_mul]
  have hstep : 2 ^ (k - 1) * 2 ^ S < (2 ^ (k - 1) + 1) * 3 ^ k := by
    rw [Nat.mul_sub] at hgap
    have h3le : 2 ^ (k - 1) * 3 ^ k ≤ 2 ^ (k - 1) * 2 ^ S :=
      Nat.mul_le_mul_left _ (Nat.le_of_lt hpow)
    rw [Nat.add_mul, Nat.one_mul]; omega
  have hq_lt : (2 ^ (k - 1)) ^ qU * (2 ^ S) ^ qU < (2 ^ (k - 1) + 1) ^ qU * (3 ^ qU) ^ k := by
    have hp := Nat.pow_lt_pow_left hstep (Nat.pos_iff_ne_zero.mp hqU)
    have h3eq : (3 ^ k) ^ qU = (3 ^ qU) ^ k := by
      rw [← Nat.pow_mul, Nat.mul_comm k qU, Nat.pow_mul]
    rw [Nat.mul_pow, Nat.mul_pow, h3eq] at hp
    exact hp
  have hcomb :
      2 * (2 ^ (k - 1)) ^ qU * (3 ^ qU) ^ k < (2 ^ (k - 1) + 1) ^ qU * (3 ^ qU) ^ k := by
    have hpos : 0 < (2 ^ (k - 1)) ^ qU := Nat.pow_pos (Nat.two_pow_pos (k - 1))
    have hmul := Nat.mul_lt_mul_of_pos_left h2low hpos
    rw [← Nat.mul_assoc, Nat.mul_comm ((2 ^ (k - 1)) ^ qU) 2] at hmul
    exact Nat.lt_trans hmul hq_lt
  have hcancel : 2 * (2 ^ (k - 1)) ^ qU < (2 ^ (k - 1) + 1) ^ qU :=
    Nat.lt_of_mul_lt_mul_right hcomb
  have hbern := succ_pow_le_two_mul_pow (Nat.two_pow_pos (k - 1)) hk_lo
  omega

/-- **Pure-Nat Steiner-Legendre Convergent Exclusion Lemma:**
given Farey neighbors `pL / qL < log₂(3) < pU / qU` (`2 ^ pL < 3 ^ qL`, `3 ^ qU < 2 ^ pU`,
`pU * qL = pL * qU + 1`) with `3 ^ qU ≤ 2 ^ c * (2 ^ pU - 3 ^ qU)` (`c + 1 ≤ qU`), no pair
`(k, S)` with `1 ≤ k`, `2 * qU ≤ 2 ^ (k - 1)`, and `k < qU + qL` can satisfy both `3 ^ k < 2 ^ S`
and Steiner's exponential gap bound `2 ^ (k - 1) * (2 ^ S - 3 ^ k) < 3 ^ k`. -/
theorem steiner_legendre_convergent_exclusion
    {pL qL pU qU c k S : Nat} (hqU : 0 < qU) (hkpos : 1 ≤ k)
    (hL : 2 ^ pL < 3 ^ qL) (hU : 3 ^ qU < 2 ^ pU) (hdet : pU * qL = pL * qU + 1)
    (hc : c + 1 ≤ qU) (hself : 3 ^ qU ≤ 2 ^ c * (2 ^ pU - 3 ^ qU))
    (hk_lo : 2 * qU ≤ 2 ^ (k - 1)) (hk_hi : k < qU + qL)
    (hpow : 3 ^ k < 2 ^ S) (hgap : 2 ^ (k - 1) * (2 ^ S - 3 ^ k) < 3 ^ k) : False := by
  have hle : pU * k ≤ qU * S := farey_upper_semiconvergent_bound hL hdet hk_hi hpow
  by_cases heq : pU * k = qU * S
  · rcases farey_eq_mul_imp_dvd hqU hkpos hdet heq with ⟨d, hd, hk_eq, hS_eq⟩
    have hcontra := steiner_convergent_eq_case hU hc hself hd hk_eq hS_eq
    omega
  · exact steiner_convergent_lt_case hqU hkpos hU (by omega) hk_lo hpow hgap

/-- Parametric Steiner 1-circuit elimination over `[k₀, qU + qL)` driven by Farey neighbors
`(pL, qL)` and `(pU, qU)`. -/
theorem no_nontrivial_oneCircuit_of_farey_window
    {pL qL pU qU c k₀ : Nat} (hqU : 0 < qU) (hk₀ : 1 ≤ k₀)
    (hL : 2 ^ pL < 3 ^ qL) (hU : 3 ^ qU < 2 ^ pU) (hdet : pU * qL = pL * qU + 1)
    (hc : c + 1 ≤ qU) (hself : 3 ^ qU ≤ 2 ^ c * (2 ^ pU - 3 ^ qU))
    (h2k₀ : 2 * qU ≤ 2 ^ (k₀ - 1))
    {n m e : Nat} (hlo : k₀ ≤ m + 1) (hhi : m + 1 < qU + qL) (hn : 1 < n) :
    ¬ IsOneCircuitCycle n m e := by
  intro hcyc
  have hk_lo : 2 * qU ≤ 2 ^ ((m + 1) - 1) :=
    Nat.le_trans h2k₀ (Nat.pow_le_pow_right (by decide) (by omega))
  exact steiner_legendre_convergent_exclusion hqU (Nat.succ_pos m) hL hU hdet hc hself
    hk_lo hhi hcyc.pow_lt (steiner_three_pow_gap_bound hcyc hn)

/-! ### 3. Extended `log₂(3)` Continued Fraction & `1 ≤ k ≤ 10781273` Elimination -/

/-- Extended partial quotients of `log₂(3)` up to index `14`
(`[1, 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, 1, 55]`). -/
def log2ThreeCFExt : List Nat :=
  log2ThreeCF ++ [2, 2, 1, 1, 55]

/-- Exact convergent pair `((176251, 111202), (301994, 190537))` and `(16785921, 10590737)` from
`log2ThreeCFExt`. -/
theorem log2ThreeCFExt_convergents :
    cfConvergentPair (log2ThreeCFExt.take 14) = ((176251, 111202), (301994, 190537)) ∧
    cfConvergentPair (log2ThreeCFExt.take 15) = ((301994, 190537), (16785921, 10590737)) := by
  decide

/-- Farey determinant `301994 * 10590737 = 16785921 * 190537 + 1` derived from
`cfConvergentPair_det`. -/
theorem log2ThreeCFExt_det_14_15 :
    301994 * 10590737 = 16785921 * 190537 + 1 := by
  have hdet := cfConvergentPair_det (log2ThreeCFExt.take 15)
  have hlen : (log2ThreeCFExt.take 15).length % 2 = 1 := by decide
  rw [log2ThreeCFExt_convergents.2, hlen] at hdet

/-- Kernel-verified `fastPow` witness certifying `(p₁₃, q₁₃) = (301994, 190537)`,
`(p₁₄, q₁₄) = (16785921, 10590737)`, the `2 ^ 24` gap witness, and `2 ^ 17087914 < 3 ^ 10781274`. -/
private theorem cf_witness_steiner_10m :
    2 ^ 16785921 < 3 ^ 10590737 ∧
    3 ^ 190537 < 2 ^ 301994 ∧
    3 ^ 190537 ≤ 2 ^ 24 * (2 ^ 301994 - 3 ^ 190537) ∧
    2 ^ 17087914 < 3 ^ 10781274 := by
  have h :
      fastPow 2 16785921 < fastPow 3 10590737 ∧
      fastPow 3 190537 < fastPow 2 301994 ∧
      fastPow 3 190537 ≤ 2 ^ 24 * (fastPow 2 301994 - fastPow 3 190537) ∧
      fastPow 2 17087914 < fastPow 3 10781274 := by
    decide
  rwa [fastPow_eq 2 16785921 (by decide), fastPow_eq 3 10590737 (by decide),
    fastPow_eq 3 190537 (by decide), fastPow_eq 2 301994 (by decide),
    fastPow_eq 2 17087914 (by decide), fastPow_eq 3 10781274 (by decide)] at h

/-- **Flagship Unconditional 1-Circuit Elimination (`1 ≤ k ≤ 10781273`, zero `native_decide`):**
there is no non-trivial positive Steiner 1-circuit Syracuse cycle with `m + 1 ≤ 10781273`. -/
theorem no_nontrivial_oneCircuit_le_10781273 :
    ∀ n m e : Nat, m + 1 ≤ 10781273 → 1 < n → ¬ IsOneCircuitCycle n m e := by
  intro n m e hle hn
  by_cases h20 : m + 1 ≤ 20
  · exact no_nontrivial_oneCircuit_le_20 n m e h20 hn
  · exact no_nontrivial_oneCircuit_of_farey_window (pL := 16785921) (qL := 10590737)
      (pU := 301994) (qU := 190537) (c := 24) (k₀ := 21) (by decide) (by decide)
      cf_witness_steiner_10m.1 cf_witness_steiner_10m.2.1 log2ThreeCFExt_det_14_15
      (by decide) cf_witness_steiner_10m.2.2.1 (by decide) (by omega) (by omega) hn

/-- **Unconditional 1-Circuit Elimination (`1 ≤ k ≤ 15600`):** corollary of
`no_nontrivial_oneCircuit_le_10781273` (`780x` beyond `SteinerCircuit.lean`). -/
theorem no_nontrivial_oneCircuit_le_15600 :
    ∀ n m e : Nat, m + 1 ≤ 15600 → 1 < n → ¬ IsOneCircuitCycle n m e :=
  fun n m e hle hn => no_nontrivial_oneCircuit_le_10781273 n m e (by omega) hn

/-- **Unconditional 1-Circuit Elimination (`1 ≤ k ≤ 31866`):** corollary of
`no_nontrivial_oneCircuit_le_10781273`. -/
theorem no_nontrivial_oneCircuit_le_31866 :
    ∀ n m e : Nat, m + 1 ≤ 31866 → 1 < n → ¬ IsOneCircuitCycle n m e :=
  fun n m e hle hn => no_nontrivial_oneCircuit_le_10781273 n m e (by omega) hn

/-- **Unconditional 1-Circuit Elimination (`1 ≤ k ≤ 10^7`):** corollary of
`no_nontrivial_oneCircuit_le_10781273`. -/
theorem no_nontrivial_oneCircuit_le_10000000 :
    ∀ n m e : Nat, m + 1 ≤ 10000000 → 1 < n → ¬ IsOneCircuitCycle n m e :=
  fun n m e hle hn => no_nontrivial_oneCircuit_le_10781273 n m e (by omega) hn

/-- **Unconditional 1-Circuit Odd-Length Lower Bound:** every non-trivial positive 1-circuit
has odd step count `10781274 ≤ m + 1` (equivalently `10781273 < m + 1`). -/
theorem steiner_oneCircuit_k_ge_10781274 {n m e : Nat}
    (h : IsOneCircuitCycle n m e) (hn : 1 < n) : 10781274 ≤ m + 1 := by
  by_cases hk : 10781274 ≤ m + 1
  · exact hk
  · exact absurd h (no_nontrivial_oneCircuit_le_10781273 n m e (Nat.le_of_not_lt hk) hn)

/-- Parametric halving lower bound from `k₀ ≤ m + 1` and `2 ^ s₀ < 3 ^ k₀`. -/
private theorem steiner_halvings_ge_of_k_ge {n m e k₀ s₀ : Nat}
    (h : IsOneCircuitCycle n m e) (hk : k₀ ≤ m + 1) (hpow : 2 ^ s₀ < 3 ^ k₀) :
    s₀ + 1 ≤ m + e := by
  have h3 : 3 ^ k₀ ≤ 3 ^ (m + 1) := Nat.pow_le_pow_right (by decide) hk
  have h2 : 2 ^ s₀ < 2 ^ (m + e) := Nat.lt_trans (Nat.lt_of_lt_of_le hpow h3) h.pow_lt
  by_cases hs : s₀ + 1 ≤ m + e
  · exact hs
  · have hle : 2 ^ (m + e) ≤ 2 ^ s₀ :=
      Nat.pow_le_pow_right (by decide) (Nat.le_of_lt_succ (Nat.lt_of_not_ge hs))
    exact absurd h2 (Nat.not_lt_of_ge hle)

/-- **Unconditional 1-Circuit Halving Lower Bound:** every non-trivial positive 1-circuit
accumulates at least `17087915` halvings (`17087915 ≤ m + e`). -/
theorem steiner_oneCircuit_halvings_ge_17087915 {n m e : Nat}
    (h : IsOneCircuitCycle n m e) (hn : 1 < n) : 17087915 ≤ m + e :=
  steiner_halvings_ge_of_k_ge h (steiner_oneCircuit_k_ge_10781274 h hn)
    cf_witness_steiner_10m.2.2.2

/-- **Unconditional 1-Circuit Total Collatz-Length Lower Bound:** every non-trivial positive
1-circuit has total Collatz period `27869189 ≤ (m + 1) + (m + e)`. -/
theorem steiner_oneCircuit_collatzLen_ge_27869189 {n m e : Nat}
    (h : IsOneCircuitCycle n m e) (hn : 1 < n) : 27869189 ≤ (m + 1) + (m + e) := by
  have hk := steiner_oneCircuit_k_ge_10781274 h hn
  have hs := steiner_oneCircuit_halvings_ge_17087915 h hn
  omega

/-- **Bridge to Frozen `Challenge.lean`:** every non-trivial 1-circuit yields a `HasNontrivialCycle`
witness in `Challenge.lean` AND an explicit `collatzIter` period `L = (m + 1) + (m + e)` avoiding
`1` with `10781274 ≤ m + 1`, `17087915 ≤ m + e`, and `27869189 ≤ L`. -/
theorem steiner_oneCircuit_challenge_bounds {n m e : Nat}
    (h : IsOneCircuitCycle n m e) (hn : 1 < n) :
    HasNontrivialCycle ∧
    collatzIter ((m + 1) + (m + e)) n = n ∧
    (∀ j : Nat, j < (m + 1) + (m + e) → collatzIter j n ≠ 1) ∧
    10781274 ≤ m + 1 ∧ 17087915 ≤ m + e ∧ 27869189 ≤ (m + 1) + (m + e) := by
  have hodd : n % 2 = 1 := h.odd
  have htot : syracuseTotalVal (m + 1) n = m + e := h.totalVal_eq
  have hne_syr : ∀ i : Nat, i < m + 1 → syracuseIter i n ≠ 1 := by
    intro i hi h1
    have hreach : syracuseIter (m + 1) n = 1 := by
      calc syracuseIter (m + 1) n
          = syracuseIter (i + (m + 1 - i)) n := by rw [Nat.add_sub_of_le (Nat.le_of_lt hi)]
        _ = syracuseIter (m + 1 - i) (syracuseIter i n) := (syracuseIter_add i _ n).symm
        _ = syracuseIter (m + 1 - i) 1 := by rw [h1]
        _ = 1 := syracuseIter_one _
    rw [h.1] at hreach
    omega
  have hcol : collatzIter ((m + 1) + (m + e)) n = n := by
    rw [Nat.add_comm, ← htot, collatzIter_eq_syracuseIter (m + 1) hodd, h.1]
  have havoid : ∀ j : Nat, j < (m + 1) + (m + e) → collatzIter j n ≠ 1 := by
    intro j hj
    rw [Nat.add_comm, ← htot] at hj
    exact collatzIter_ne_one_of_syracuseIter (m + 1) hodd hne_syr j hj
  exact ⟨h.hasNontrivialCycle hn, hcol, havoid,
    steiner_oneCircuit_k_ge_10781274 h hn,
    steiner_oneCircuit_halvings_ge_17087915 h hn,
    steiner_oneCircuit_collatzLen_ge_27869189 h hn⟩

/-- **Sharpened Conditional Steiner Reduction above `k = 10781273`:**
any Baker/Rhin lower bound `2 ^ S ≤ 2 ^ k * (2 ^ S - 3 ^ k)` for `10781273 < k` (with
`3 ^ k < 2 ^ S`) rules out ALL non-trivial positive 1-circuit Collatz cycles. -/
theorem no_nontrivial_oneCircuit_of_diophantine_bound_gt_10781273
    (hBaker : ∀ k S : Nat, 10781273 < k → 3 ^ k < 2 ^ S → 2 ^ S ≤ 2 ^ k * (2 ^ S - 3 ^ k)) :
    ∀ n m e : Nat, 1 < n → ¬ IsOneCircuitCycle n m e :=
  no_nontrivial_oneCircuit_of_diophantine_bound 10781273 hBaker
    no_nontrivial_oneCircuit_le_10781273

/-! ### 4. Explicit Barrier 1–5 Separations -/

/-- **Barrier 1 Separation (`3n - 1` on `ℕ⁺`):** `n = 5` forms a non-trivial positive `3n - 1`
1-circuit (`5 → 14 → 7 → 20 → 10 → 5`) with `k = 2 ≤ 10781273` and `S = 3`, escaping the
convergent exclusion by violating `3 ^ k < 2 ^ S` (`¬ (3 ^ 2 < 2 ^ 3)`). -/
theorem barrier1_steiner_three_n_minus_one :
    Barriers.genIter 3 (-1) 5 5 = 5 ∧
    (∀ j : Nat, j < 5 → Barriers.genIter 3 (-1) j 5 ≠ 1) ∧
    2 ≤ 10781273 ∧ ¬ (3 ^ 2 < 2 ^ 3) :=
  ⟨Barriers.three_n_minus_one_cycle_5.1, Barriers.three_n_minus_one_cycle_5.2,
    by decide, by decide⟩

/-- **Barrier 2 Separation (`5n + 1` on `ℕ⁺`):** `n = 1` (`1 → 6 → 3 → 16 → 8 → 4 → 2 → 1`,
`k = 2, S = 5`) and non-trivial `n = 13` (`k = 3, S = 7`) satisfy `5 ^ k < 2 ^ S` and
`3 ^ k < 2 ^ S` with `k ≤ 10781273`, yet escape `steiner_three_pow_gap_bound`
(`¬ (2 ^ (k - 1) * (2 ^ S - 3 ^ k) < 3 ^ k)`) because `5n + 1` replaces `3 ^ k` drift by
`5 ^ k`. -/
theorem barrier2_steiner_five_n_plus_one :
    (Barriers.genIter 5 1 7 1 = 1 ∧ 2 ≤ 10781273 ∧
      5 ^ 2 < 2 ^ 5 ∧ 3 ^ 2 < 2 ^ 5 ∧ ¬ (2 ^ 1 * (2 ^ 5 - 3 ^ 2) < 3 ^ 2)) ∧
    (Barriers.genIter 5 1 10 13 = 13 ∧
      (∀ j : Nat, j < 10 → Barriers.genIter 5 1 j 13 ≠ 1) ∧
      3 ≤ 10781273 ∧ 5 ^ 3 < 2 ^ 7 ∧ 3 ^ 3 < 2 ^ 7 ∧
      ¬ (2 ^ 2 * (2 ^ 7 - 3 ^ 3) < 3 ^ 3)) :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide⟩,
    ⟨Barriers.five_n_plus_one_cycle_13.1, Barriers.five_n_plus_one_cycle_13.2,
      by decide, by decide, by decide, by decide⟩⟩

/-- **Barrier 3 Separation (`3n + 1` on `ℤ_{<0}`):** `n = -5` forms a non-trivial negative
1-circuit (`-5 → -14 → -7 → -20 → -10 → -5`) with `k = 2 ≤ 10781273` and `S = 3`, escaping
archimedean positivity `1 < n` and `3 ^ 2 < 2 ^ 3`. -/
theorem barrier3_steiner_neg_int :
    Barriers.genIter 3 1 5 (-5) = -5 ∧
    (∀ j : Nat, j < 5 → Barriers.genIter 3 1 j (-5) ≠ 1) ∧
    2 ≤ 10781273 ∧ ¬ (3 ^ 2 < 2 ^ 3) :=
  ⟨Barriers.neg_int_cycle_neg5.1, Barriers.neg_int_cycle_neg5.2, by decide, by decide⟩

/-- **Barrier 4 Separation (`ℤ₂` rational 1-circuits):** `oneCircuitVec 4 4 = [1, 1, 1, 1, 4]`
(`k = 5 ≤ 10781273`, `S = 8`) realizes the genuine positive periodic point
`211 / 13 ∈ ℤ_(2) \ ℤ` satisfying BOTH `3 ^ 5 < 2 ^ 8` and Steiner's exponential gap bound
`2 ^ 4 * (2 ^ 8 - 3 ^ 5) < 3 ^ 5`, escaping `no_nontrivial_oneCircuit_le_10781273` solely by
violating global integrality in `ℕ⁺` (`13 ∤ 211`). -/
theorem barrier4_steiner_twoAdic :
    let v := oneCircuitVec 4 4
    let x := periodicPoint v (by decide)
    v = [1, 1, 1, 1, 4] ∧
    x = ⟨211, 13, by decide⟩ ∧
    0 < x.num ∧
    OddDenomRat.syracuseIter 5 x = x ∧
    5 ≤ 10781273 ∧
    3 ^ 5 < 2 ^ 8 ∧
    2 ^ 4 * (2 ^ 8 - 3 ^ 5) < 3 ^ 5 ∧
    (¬ ∃ m : Int, x.Equiv (OddDenomRat.ofInt m)) :=
  ⟨rfl, twoAdic_cycle_211_over_13.1, twoAdic_cycle_211_over_13.2.1,
    twoAdic_cycle_211_over_13.2.2.1, by decide, by decide, by decide,
    twoAdic_cycle_211_over_13.2.2.2.2.2.1⟩

/-- **Barrier 5 Separation (Conway 1972 / Finite Verification Horizon):** continued-fraction
convergent windows rule out finite prefixes (`1 ≤ k ≤ 20`, `1 ≤ k ≤ 10781273`), leaving all
`k > 10781273` dependent on global Baker/Rhin linear forms in logarithms. -/
theorem barrier5_steiner_conway_finite_horizon :
    (∀ n m e : Nat, m + 1 ≤ 10781273 → 1 < n → ¬ IsOneCircuitCycle n m e) ∧
    ((∀ k S : Nat, 10781273 < k → 3 ^ k < 2 ^ S → 2 ^ S ≤ 2 ^ k * (2 ^ S - 3 ^ k)) →
      ∀ n m e : Nat, 1 < n → ¬ IsOneCircuitCycle n m e) :=
  ⟨no_nontrivial_oneCircuit_le_10781273, no_nontrivial_oneCircuit_of_diophantine_bound_gt_10781273⟩

end SolveCollatz
