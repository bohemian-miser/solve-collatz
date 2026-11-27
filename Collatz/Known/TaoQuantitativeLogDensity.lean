/-
Copyright (c) 2026 The solve-collatz contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Collatz.Prove.Ergodic.SharperChernoff
public import Collatz.Core.TwoAdic

/-!
# Quantitative Logarithmic Density & Multi-Scale Tao (2022) Interface (`KNOWN-004`, Phase 2)

Pure Lean 4 core formalization (zero Mathlib, zero reals) bridging `PROVE-A1` (`SharperChernoff`)
into `KNOWN-004` (`TaoBridge`): dyadic harmonic bounds, `O(1 / log N)` logarithmic density
(`HasQuantitativeLogDensityOne ↔ HasConvergentReciprocalExceptions`), quantitative Abel transfer
from `HasPowerSavingDensityOne`, multi-scale iterated descent, and explicit Barrier 1–5 separations.
-/

@[expose] public section

namespace SolveCollatz

private theorem tq_dec_true {P : Prop} (h : P) : @decide P (Classical.propDecidable P) = true :=
  @decide_eq_true P (Classical.propDecidable P) h
private theorem tq_dec_false {P : Prop} (h : ¬ P) : @decide P (Classical.propDecidable P) = false :=
  @decide_eq_false P (Classical.propDecidable P) h
private noncomputable def failInd (P : Nat → Prop) (i : Nat) : Nat :=
  if @decide (¬ P i) (Classical.propDecidable _) then 1 else 0
private theorem tq_natSum1_mono {a b : Nat} (hab : a ≤ b) (f : Nat → Nat) :
    natSum1 a f ≤ natSum1 b f := by
  induction b with | zero => rw [Nat.eq_zero_of_le_zero hab]; exact Nat.le_refl 0 | succ b ih =>
    by_cases hle : a ≤ b; exact Nat.le_trans (ih hle) (by simp [natSum1])
    rw [show a = b + 1 by omega]; exact Nat.le_refl _
private theorem tq_natSum1_split (a k : Nat) (f : Nat → Nat) :
    natSum1 (a + k) f = natSum1 a f + natSum1 k (fun j => f (a + j)) := by
  induction k with | zero => simp [natSum1] | succ k ih =>
    rw [← Nat.add_assoc, natSum1, ih, natSum1, show a + k + 1 = a + (k + 1) by omega]; omega
private theorem tq_natSum1_mul (c N : Nat) (f : Nat → Nat) :
    natSum1 N (fun i => c * f i) = c * natSum1 N f := by
  induction N with | zero => simp [natSum1] | succ N ih => simp only [natSum1, ih, Nat.mul_add]
private theorem tq_natSum1_add (N : Nat) (f g : Nat → Nat) :
    natSum1 N (fun i => f i + g i) = natSum1 N f + natSum1 N g := by
  induction N with | zero => simp [natSum1] | succ N ih => simp only [natSum1, ih]; omega
private theorem tq_natSum1_congr {N : Nat} {f g : Nat → Nat}
    (h : ∀ i : Nat, 1 ≤ i → i ≤ N → f i = g i) : natSum1 N f = natSum1 N g :=
  Nat.le_antisymm (natSum1_le (fun i h1 h2 => Nat.le_of_eq (h i h1 h2)))
    (natSum1_le (fun i h1 h2 => Nat.le_of_eq (h i h1 h2).symm))
private theorem tq_natSum1_const (N c : Nat) : natSum1 N (fun _ => c) = N * c := by
  induction N with | zero => simp [natSum1] | succ N ih => rw [natSum1, ih, Nat.succ_mul]
private theorem tq_natSum1_const_le {N c : Nat} {f : Nat → Nat}
    (h : ∀ i : Nat, 1 ≤ i → i ≤ N → c ≤ f i) : N * c ≤ natSum1 N f := by
  rw [← tq_natSum1_const N c]; exact natSum1_le h
private theorem tq_lt_two_pow_self : ∀ n : Nat, n < 2 ^ n
  | 0 => by decide | n + 1 => by have := tq_lt_two_pow_self n; rw [Nat.pow_succ]; omega

/-! ### 1. Quantitative Logarithmic Density & Pure-`Nat` Harmonic Bounds -/

/-- Pure-`Nat` convergent exceptional reciprocal sum: `logExceptionalNum P N ≤ M₀ * natFact N`. -/
def HasConvergentReciprocalExceptions (P : Nat → Prop) : Prop :=
  ∃ M₀ : Nat, ∀ N : Nat, logExceptionalNum P N ≤ M₀ * natFact N
/-- Explicit `O(1 / log N)` logarithmic density: `E_log(P, N) * bitLen N ≤ K * H_log(N)`. -/
def HasQuantitativeLogDensityOne (P : Nat → Prop) : Prop :=
  ∃ K : Nat, ∀ N : Nat, 1 ≤ N → logExceptionalNum P N * bitLen N ≤ K * harmonicSumNum N
/-- Exact pure-`Nat` dyadic harmonic lower bound: `H_log(2^m) ≥ (m / 2) * (2^m)!`. -/
theorem harmonicSumNum_two_pow_lower (m : Nat) :
    (m / 2) * natFact (2 ^ m) ≤ harmonicSumNum (2 ^ m) := by
  have hmul := Nat.le_trans
    (Nat.mul_le_mul_right (natFact (2 ^ m)) (by omega : 2 * (m / 2) ≤ m + 2))
    (dyadic_harmonic_lower_bound (Nat.le_refl (2 ^ m)))
  rw [Nat.mul_assoc] at hmul; omega
/-- Pure-`Nat` `bitLen`-scaled harmonic lower bound: `bitLen N * N! ≤ 2 * H_log(N)` for `1 ≤ N`. -/
theorem bitLen_mul_natFact_le_two_harmonicSumNum {N : Nat} (hN : 1 ≤ N) :
    bitLen N * natFact N ≤ 2 * harmonicSumNum N :=
  Nat.le_trans (Nat.mul_le_mul_right _ (by omega : bitLen N ≤ (bitLen N - 1) + 2))
    (dyadic_harmonic_lower_bound (two_pow_pred_bitLen_le hN))

private theorem block_harmonic_sum_le (k N : Nat) :
    natSum1 (2 ^ k) (fun j => harmonicWeight N ((2 ^ k - 1) + j)) ≤ natFact N := by
  have hmul : 2 ^ k * natSum1 (2 ^ k) (fun j => harmonicWeight N ((2 ^ k - 1) + j)) ≤
      2 ^ k * natFact N := by
    rw [← tq_natSum1_mul, ← tq_natSum1_const (2 ^ k) (natFact N)]
    refine natSum1_le (fun j hj1 _ => Nat.le_trans
      (Nat.mul_le_mul_right _ (by omega : 2 ^ k ≤ (2 ^ k - 1) + j))
      (Nat.mul_div_le (natFact N) ((2 ^ k - 1) + j)))
  exact Nat.le_of_mul_le_mul_left hmul (Nat.two_pow_pos k)

/-- Pure-`Nat` harmonic upper bound: `H_log(N) ≤ bitLen N * N!` for all `N`. -/
theorem harmonicSumNum_le_bitLen_mul_natFact (N : Nat) :
    harmonicSumNum N ≤ bitLen N * natFact N := by
  have hpow : ∀ m : Nat, natSum1 (2 ^ m - 1) (harmonicWeight N) ≤ m * natFact N := fun m => by
    induction m with | zero => simp [natSum1] | succ m ih =>
      have h2m : 1 ≤ 2 ^ m := Nat.two_pow_pos m
      rw [show 2 ^ (m + 1) - 1 = (2 ^ m - 1) + 2 ^ m by rw [Nat.pow_succ]; omega,
        tq_natSum1_split, Nat.succ_mul]
      exact Nat.add_le_add ih (block_harmonic_sum_le m N)
  exact Nat.le_trans (tq_natSum1_mono (by have := lt_two_pow_bitLen N; omega) (harmonicWeight N))
    (hpow (bitLen N))

/-- Equivalence: `HasQuantitativeLogDensityOne P ↔ HasConvergentReciprocalExceptions P`. -/
theorem quantitativeLogDensity_iff_convergentReciprocal (P : Nat → Prop) :
    HasQuantitativeLogDensityOne P ↔ HasConvergentReciprocalExceptions P := by
  constructor
  · rintro ⟨K, hK⟩; refine ⟨K, fun N => ?_⟩
    cases N with | zero => simp [logExceptionalNum, natSum1] | succ n =>
      have hmul := Nat.le_trans (hK (n + 1) (Nat.succ_pos n))
        (Nat.mul_le_mul_left K (harmonicSumNum_le_bitLen_mul_natFact (n + 1)))
      rw [Nat.mul_left_comm K (bitLen (n + 1)) (natFact (n + 1)),
        Nat.mul_comm (bitLen (n + 1)) (K * natFact (n + 1))] at hmul
      exact Nat.le_of_mul_le_mul_right hmul (bitLen_pos_succ n)
  · rintro ⟨M₀, hM₀⟩; refine ⟨2 * M₀, fun N hN => ?_⟩
    calc logExceptionalNum P N * bitLen N ≤ (M₀ * natFact N) * bitLen N :=
          Nat.mul_le_mul_right _ (hM₀ N)
      _ = M₀ * (bitLen N * natFact N) := by ac_rfl
      _ ≤ M₀ * (2 * harmonicSumNum N) :=
          Nat.mul_le_mul_left _ (bitLen_mul_natFact_le_two_harmonicSumNum hN)
      _ = (2 * M₀) * harmonicSumNum N := by ac_rfl

/-- Quantitative `O(1 / log N)` logarithmic density implies Tao's `HasLogDensityOne`. -/
theorem hasLogDensityOne_of_quantitativeLogDensity {P : Nat → Prop}
    (h : HasQuantitativeLogDensityOne P) : HasLogDensityOne P := by
  rcases h with ⟨K, hK⟩; intro D hD; refine ⟨2 ^ (K * D), fun N hN => ?_⟩
  have hN1 : 1 ≤ N := Nat.le_trans (Nat.two_pow_pos _) hN
  have hbit : K * D < bitLen N := Nat.lt_of_not_ge (fun hle =>
    absurd (Nat.pow_le_pow_right (by decide : 0 < 2) hle)
      (by have := lt_two_pow_bitLen N; omega))
  have hHpos : 0 < harmonicSumNum N := by
    have h1 := bitLen_mul_natFact_le_two_harmonicSumNum hN1
    have : 0 < bitLen N * natFact N := Nat.mul_pos (by omega) (natFact_pos N); omega
  have hmul : logExceptionalNum P N * D * bitLen N < harmonicSumNum N * bitLen N := by
    calc logExceptionalNum P N * D * bitLen N = (logExceptionalNum P N * bitLen N) * D := by ac_rfl
      _ ≤ (K * harmonicSumNum N) * D := Nat.mul_le_mul_right D (hK N hN1)
      _ = (K * D) * harmonicSumNum N := by ac_rfl
      _ < bitLen N * harmonicSumNum N := Nat.mul_lt_mul_of_pos_right hbit hHpos
      _ = harmonicSumNum N * bitLen N := Nat.mul_comm _ _
  exact Nat.lt_of_mul_lt_mul_right hmul

/-- Convergent exceptional reciprocal sum implies `HasLogDensityOne`. -/
theorem hasLogDensityOne_of_convergentReciprocal {P : Nat → Prop}
    (h : HasConvergentReciprocalExceptions P) : HasLogDensityOne P :=
  hasLogDensityOne_of_quantitativeLogDensity
    ((quantitativeLogDensity_iff_convergentReciprocal P).mpr h)

/-! ### 2. Quantitative Abel Summation Transfer (`powerSaving → O(1 / log N)`) -/

private theorem logExceptionalNum_eq_natSum1 (P : Nat → Prop) (N : Nat) :
    logExceptionalNum P N = natSum1 N (fun i => failInd P i * harmonicWeight N i) :=
  tq_natSum1_congr (fun i _ _ => by dsimp [failInd]; split <;> simp)

private theorem powerSaving_block_count_lt {P : Nat → Prop} {p q N₀ t₀ k : Nat}
    (hN₀ : N₀ ≤ 2 ^ (q * t₀))
    (hpow : ∀ n : Nat, N₀ ≤ n → natExceptionalCount P n ^ q < n ^ p) :
    natExceptionalCount P (2 ^ (q * (t₀ + k + 1))) < 2 ^ p * 2 ^ (p * (t₀ + k)) := by
  have hB_ge : N₀ ≤ 2 ^ (q * (t₀ + k + 1)) := Nat.le_trans hN₀
    (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.mul_le_mul_left q (by omega)))
  have hcnt_pow : natExceptionalCount P (2 ^ (q * (t₀ + k + 1))) ^ q <
      (2 ^ (p * (t₀ + k + 1))) ^ q := by
    calc natExceptionalCount P (2 ^ (q * (t₀ + k + 1))) ^ q
        < (2 ^ (q * (t₀ + k + 1))) ^ p := hpow _ hB_ge
      _ = 2 ^ (q * (t₀ + k + 1) * p) := (Nat.pow_mul _ _ _).symm
      _ = 2 ^ (p * (t₀ + k + 1) * q) := by congr 1; ac_rfl
      _ = (2 ^ (p * (t₀ + k + 1))) ^ q := Nat.pow_mul _ _ _
  have hlt := Nat.lt_of_not_ge (fun hge =>
    Nat.not_lt_of_ge (Nat.pow_le_pow_left hge q) hcnt_pow)
  rwa [show p * (t₀ + k + 1) = p + p * (t₀ + k) by rw [Nat.mul_add, Nat.mul_one]; omega,
    Nat.pow_add] at hlt

private theorem powerSaving_dyadic_tail_step {P : Nat → Prop} {p q N₀ t₀ k N M : Nat}
    (hpq : p < q) (hN₀ : N₀ ≤ 2 ^ (q * t₀))
    (hpow : ∀ n : Nat, N₀ ≤ n → natExceptionalCount P n ^ q < n ^ p)
    (hA : 2 ^ (q * (t₀ + k)) < M) (hM : M ≤ 2 ^ (q * (t₀ + k + 1))) :
    let A := 2 ^ (q * (t₀ + k))
    2 ^ k * natSum1 (M - A) (fun j => failInd P (A + j) * harmonicWeight N (A + j)) ≤
      2 ^ p * natFact N := by
  intro A
  have hcnt_lt := powerSaving_block_count_lt hN₀ hpow (k := k)
  have hsum_f : natSum1 (M - A) (fun j => failInd P (A + j)) ≤
      natExceptionalCount P (2 ^ (q * (t₀ + k + 1))) := by
    rw [natExceptionalCount_eq_natSum1]
    have hsplit := tq_natSum1_split A (M - A) (failInd P)
    rw [Nat.add_sub_of_le (Nat.le_of_lt hA)] at hsplit
    exact Nat.le_trans (by change _ ≤ natSum1 M (failInd P); omega)
      (tq_natSum1_mono hM (failInd P))
  have hA_mul : A * natSum1 (M - A) (fun j => failInd P (A + j) * harmonicWeight N (A + j)) ≤
      natSum1 (M - A) (fun j => failInd P (A + j)) * natFact N := by
    rw [← tq_natSum1_mul, Nat.mul_comm _ (natFact N), ← tq_natSum1_mul]
    refine natSum1_le (fun j _ _ => ?_)
    have hwt := Nat.le_trans (Nat.mul_le_mul_right _ (Nat.le_add_right A j))
      (Nat.mul_div_le (natFact N) (A + j))
    rw [Nat.mul_left_comm A (failInd P (A + j)), Nat.mul_comm (natFact N) (failInd P (A + j))]
    exact Nat.mul_le_mul_left _ hwt
  have hexp : p * (t₀ + k) + k ≤ q * (t₀ + k) := by
    have h1 : (p + 1) * (t₀ + k) ≤ q * (t₀ + k) := Nat.mul_le_mul_right _ hpq
    rw [Nat.add_mul, Nat.one_mul] at h1; omega
  have hfin : 2 ^ (p * (t₀ + k)) *
      (2 ^ k * natSum1 (M - A) (fun j => failInd P (A + j) * harmonicWeight N (A + j))) ≤
      2 ^ (p * (t₀ + k)) * (2 ^ p * natFact N) := by
    calc _ = 2 ^ (p * (t₀ + k) + k) *
            natSum1 (M - A) (fun j => failInd P (A + j) * harmonicWeight N (A + j)) := by
            rw [← Nat.mul_assoc, ← Nat.pow_add]
      _ ≤ A * natSum1 (M - A) (fun j => failInd P (A + j) * harmonicWeight N (A + j)) :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide : 0 < 2) hexp)
      _ ≤ natSum1 (M - A) (fun j => failInd P (A + j)) * natFact N := hA_mul
      _ ≤ (2 ^ p * 2 ^ (p * (t₀ + k))) * natFact N :=
            Nat.mul_le_mul_right _ (Nat.le_trans hsum_f (Nat.le_of_lt hcnt_lt))
      _ = 2 ^ (p * (t₀ + k)) * (2 ^ p * natFact N) := by ac_rfl
  exact Nat.le_of_mul_le_mul_left hfin (Nat.two_pow_pos _)

private theorem powerSaving_dyadic_step_combine {H P_term T_term k S₁ S₂ : Nat}
    (h1 : 2 ^ k * S₁ ≤ 2 ^ k * H + (2 ^ (k + 1) - 2) * P_term)
    (h2 : 2 ^ k * T_term ≤ P_term) (hS : S₂ = S₁ + T_term) :
    2 ^ (k + 1) * S₂ ≤ 2 ^ (k + 1) * H + (2 ^ (k + 1 + 1) - 2) * P_term := by
  have h2k : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
  have hpos : 2 ≤ 2 ^ (k + 1) := by have := Nat.two_pow_pos k; rw [Nat.pow_succ]; omega
  calc 2 ^ (k + 1) * S₂
      = 2 * (2 ^ k * S₁) + 2 * (2 ^ k * T_term) := by
          rw [hS, h2k, Nat.mul_add, Nat.mul_assoc 2 (2 ^ k), Nat.mul_assoc 2 (2 ^ k)]
    _ ≤ 2 * (2 ^ k * H + (2 ^ (k + 1) - 2) * P_term) + 2 * P_term :=
          Nat.add_le_add (Nat.mul_le_mul_left 2 h1) (Nat.mul_le_mul_left 2 h2)
    _ = 2 ^ (k + 1) * H + (2 * (2 ^ (k + 1) - 2) + 2) * P_term := by
          rw [Nat.mul_add, ← Nat.mul_assoc 2 (2 ^ k), ← h2k, ← Nat.mul_assoc 2, Nat.add_assoc,
            ← Nat.add_mul (2 * (2 ^ (k + 1) - 2)) 2 P_term]
    _ ≤ 2 ^ (k + 1) * H + (2 ^ (k + 1 + 1) - 2) * P_term :=
          Nat.add_le_add_left (Nat.mul_le_mul_right _ (by rw [Nat.pow_succ 2 (k + 1)]; omega)) _

private theorem powerSaving_dyadic_prefix_bound {P : Nat → Prop} {p q N₀ t₀ : Nat}
    (hpq : p < q) (hN₀ : N₀ ≤ 2 ^ (q * t₀))
    (hpow : ∀ n : Nat, N₀ ≤ n → natExceptionalCount P n ^ q < n ^ p)
    (N k M : Nat) (hM : M ≤ 2 ^ (q * (t₀ + k))) :
    2 ^ k * natSum1 M (fun i => failInd P i * harmonicWeight N i) ≤
      2 ^ k * (2 ^ (q * t₀) * natFact N) + (2 ^ (k + 1) - 2) * (2 ^ p * natFact N) := by
  induction k generalizing M with
  | zero =>
    simp only [Nat.pow_zero, Nat.one_mul, Nat.add_zero, show 2 ^ 1 - 2 = 0 by decide,
      Nat.zero_mul, Nat.add_zero] at hM ⊢
    have h1 := natSum1_le (N := M) (f := fun i => failInd P i * harmonicWeight N i)
      (g := fun _ => natFact N) (fun i _ _ => Nat.le_trans (Nat.mul_le_mul
        (by dsimp [failInd]; split <;> omega) (Nat.div_le_self _ _))
        (Nat.le_of_eq (Nat.one_mul _)))
    rw [tq_natSum1_const] at h1; exact Nat.le_trans h1 (Nat.mul_le_mul_right _ hM)
  | succ k ih =>
    let A := 2 ^ (q * (t₀ + k))
    by_cases hle : M ≤ A
    · exact powerSaving_dyadic_step_combine (ih M hle) (Nat.zero_le _) (Nat.add_zero _).symm
    · have hA_lt : A < M := Nat.lt_of_not_ge hle
      have hsplit := tq_natSum1_split A (M - A) (fun i => failInd P i * harmonicWeight N i)
      rw [Nat.add_sub_of_le (Nat.le_of_lt hA_lt)] at hsplit
      exact powerSaving_dyadic_step_combine (ih A (Nat.le_refl A))
        (powerSaving_dyadic_tail_step hpq hN₀ hpow hA_lt hM) hsplit

/-- **Explicit-Modulus Quantitative Transfer:** if `natExceptionalCount P n ^ q < n ^ p` for
`n ≥ N₀` (`0 < q`, `p < q`), then `logExceptionalNum P N ≤ (2^(q * bitLen N₀) + 2^(p+1)) * N!`. -/
theorem convergentReciprocal_of_powerSaving_explicit {P : Nat → Prop} {p q N₀ : Nat}
    (hq : 0 < q) (hpq : p < q)
    (hpow : ∀ n : Nat, N₀ ≤ n → natExceptionalCount P n ^ q < n ^ p) :
    ∀ N : Nat, logExceptionalNum P N ≤ (2 ^ (q * bitLen N₀) + 2 ^ (p + 1)) * natFact N := by
  intro N; let t₀ := bitLen N₀
  have hN₀ : N₀ ≤ 2 ^ (q * t₀) := Nat.le_trans (Nat.le_of_lt (lt_two_pow_bitLen N₀))
    (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_mul_of_pos_left t₀ hq))
  have hN_le : N ≤ 2 ^ (q * (t₀ + N)) := Nat.le_trans (Nat.le_of_lt (tq_lt_two_pow_self N))
    (Nat.pow_le_pow_right (by decide : 0 < 2)
      (Nat.le_trans (Nat.le_add_left N t₀) (Nat.le_mul_of_pos_left _ hq)))
  have hbd := powerSaving_dyadic_prefix_bound hpq hN₀ hpow N N N hN_le
  rw [← logExceptionalNum_eq_natSum1 P N] at hbd
  have htail : 2 ^ (N + 1) - 2 ≤ 2 * 2 ^ N := by rw [Nat.pow_succ]; omega
  have hfin : 2 ^ N * logExceptionalNum P N ≤
      2 ^ N * ((2 ^ (q * t₀) + 2 ^ (p + 1)) * natFact N) := by
    calc 2 ^ N * logExceptionalNum P N
        ≤ 2 ^ N * (2 ^ (q * t₀) * natFact N) + (2 ^ (N + 1) - 2) * (2 ^ p * natFact N) := hbd
      _ ≤ 2 ^ N * (2 ^ (q * t₀) * natFact N) + (2 * 2 ^ N) * (2 ^ p * natFact N) :=
          Nat.add_le_add_left (Nat.mul_le_mul_right _ htail) _
      _ = 2 ^ N * (2 ^ (q * t₀) * natFact N) + 2 ^ N * (2 ^ (p + 1) * natFact N) := by
          rw [Nat.pow_succ 2 p]; ac_rfl
      _ = 2 ^ N * ((2 ^ (q * t₀) + 2 ^ (p + 1)) * natFact N) := by
          rw [← Nat.mul_add, ← Nat.add_mul]
  exact Nat.le_of_mul_le_mul_left hfin (Nat.two_pow_pos N)

/-- **General Quantitative Transfer Theorem (`PROVE-A1 → KNOWN-004`):** `HasPowerSavingDensityOne`
(`0 < q`, `p < q`) implies `HasConvergentReciprocalExceptions P`. -/
theorem convergentReciprocal_of_powerSaving {P : Nat → Prop} {p q : Nat}
    (hq : 0 < q) (hpq : p < q) (h : HasPowerSavingDensityOne P p q) :
    HasConvergentReciprocalExceptions P :=
  let ⟨N₀, hN₀⟩ := h
  ⟨2 ^ (q * bitLen N₀) + 2 ^ (p + 1), convergentReciprocal_of_powerSaving_explicit hq hpq hN₀⟩
/-- **General `O(1 / log N)` Transfer:** `HasPowerSavingDensityOne P p q` (`0 < q`, `p < q`)
implies `HasQuantitativeLogDensityOne P`. -/
theorem quantitativeLogDensity_of_powerSaving {P : Nat → Prop} {p q : Nat}
    (hq : 0 < q) (hpq : p < q) (h : HasPowerSavingDensityOne P p q) :
    HasQuantitativeLogDensityOne P :=
  (quantitativeLogDensity_iff_convergentReciprocal P).mpr
    (convergentReciprocal_of_powerSaving hq hpq h)
/-- **Flagship Unconditional Reciprocal Convergence (`SharperChernoff` 19/20 → `TaoBridge`):**
the sum of reciprocals `∑_{¬ HasFiniteStoppingTime n} 1/n` converges unconditionally. -/
theorem hasFiniteStoppingTime_convergent_reciprocal_sum :
    HasConvergentReciprocalExceptions HasFiniteStoppingTime :=
  convergentReciprocal_of_powerSaving (by decide) (by decide) sharper_power_saving_density_19_20
/-- **Flagship Unconditional `O(1 / log N)` Logarithmic Density (`KNOWN-004` Phase 2):**
`HasFiniteStoppingTime` satisfies explicit `O(1 / log N)` quantitative logarithmic density. -/
theorem hasFiniteStoppingTime_quantitative_log_density :
    HasQuantitativeLogDensityOne HasFiniteStoppingTime :=
  (quantitativeLogDensity_iff_convergentReciprocal HasFiniteStoppingTime).mpr
    hasFiniteStoppingTime_convergent_reciprocal_sum
/-- **Constructive Constant Instantiation (`20/21`, `N₀ = 2^2002`):** explicit uniform bound
`logExceptionalNum HasFiniteStoppingTime N ≤ (2 ^ 42063 + 2 ^ 21) * natFact N` for all `N`. -/
theorem hasFiniteStoppingTime_explicit_reciprocal_bound (N : Nat) :
    logExceptionalNum HasFiniteStoppingTime N ≤ (2 ^ 42063 + 2 ^ 21) * natFact N := by
  have hbit : bitLen (2 ^ 2002) = 2003 := by
    have h : ∀ m : Nat, bitLen (2 ^ m) = m + 1 := fun m => by
      induction m with | zero => rw [show (2 ^ 0 : Nat) = 1 by rfl, bitLen, bitLen] | succ m ih =>
        rw [Nat.pow_succ, show 2 ^ m * 2 = (2 ^ m * 2 - 1) + 1 by have := Nat.two_pow_pos m; omega,
          bitLen, show (2 ^ m * 2 - 1 + 1) / 2 = 2 ^ m by omega, ih]
    exact h 2002
  have h := convergentReciprocal_of_powerSaving_explicit (p := 20) (q := 21) (N₀ := 2 ^ 2002)
    (by decide) (by decide) sharper_power_saving_explicit_20_21 N
  rwa [hbit, show 21 * 2003 = 42063 by decide, show 20 + 1 = 21 by decide] at h

/-! ### 3. Iterated Stopping-Time & Multi-Scale Tao (2022) Reductions -/

/-- Monotonicity of `OrbitMinLe` in the bounding function (`f ≤ g`). -/
theorem orbitMinLe_mono_func {f g : Nat → Nat} {n : Nat} (hfg : f n ≤ g n)
    (h : OrbitMinLe n (f n)) : OrbitMinLe n (g n) := orbitMinLe_mono hfg h
/-- Eventual monotonicity of `HasLogDensityOne (OrbitMinLe · (f ·))` under `f n ≤ g n`. -/
theorem hasLogDensityOne_orbitMinLe_mono_func {f g : Nat → Nat} (M : Nat)
    (hfg : ∀ n : Nat, M ≤ n → f n ≤ g n)
    (h : HasLogDensityOne (fun n => OrbitMinLe n (f n))) :
    HasLogDensityOne (fun n => OrbitMinLe n (g n)) :=
  hasLogDensityOne_eventually_mono M (fun n hn => orbitMinLe_mono_func (hfg n hn)) h
/-- `r`-fold iteration of `f : Nat → Nat`. -/
def iterFn (f : Nat → Nat) : Nat → Nat → Nat | 0, x => x | r + 1, x => f (iterFn f r x)

/-- **Iterated Descent Composition:** if `f` is monotone and every `m > B₀` drops to `≤ f m`,
then `r` iterated drops reach `≤ max (iterFn f r n) B₀`. -/
theorem orbitMinLe_iterated_composition {f : Nat → Nat} {B₀ : Nat}
    (hf_mono : ∀ a b : Nat, a ≤ b → f a ≤ f b)
    (hdrop : ∀ m : Nat, B₀ < m → OrbitMinLe m (f m))
    (r : Nat) {n : Nat} (hn : 0 < n) : OrbitMinLe n (max (iterFn f r n) B₀) := by
  induction r with
  | zero => exact orbitMinLe_mono (Nat.le_max_left n B₀) (orbitMinLe_self n)
  | succ r ih =>
    rcases ih with ⟨t, ht⟩; let m := collatzIter t n
    have hmpos : 0 < m := collatzIter_pos t hn
    by_cases hmB : m ≤ B₀
    · exact ⟨t, Nat.le_trans hmB (Nat.le_max_right _ _)⟩
    · have hmle : m ≤ iterFn f r n := by rw [Nat.max_def] at ht; split at ht <;> omega
      exact orbitMinLe_of_iter (orbitMinLe_mono
        (Nat.le_trans (hf_mono m (iterFn f r n) hmle) (Nat.le_max_left _ _))
        (hdrop m (Nat.lt_of_not_ge hmB)))

/-- Monotonicity of `HasConvergentReciprocalExceptions` under eventual implication. -/
theorem hasConvergentReciprocal_eventually_mono {P Q : Nat → Prop} (M : Nat)
    (hPQ : ∀ n : Nat, M ≤ n → P n → Q n) (hP : HasConvergentReciprocalExceptions P) :
    HasConvergentReciprocalExceptions Q := by
  rcases hP with ⟨M₀, hM₀⟩; refine ⟨M + M₀, fun N => ?_⟩
  have hsum : logExceptionalNum Q N ≤ natSum1 N (fun n => if n < M then natFact N else 0) +
      logExceptionalNum P N := by
    unfold logExceptionalNum; rw [← tq_natSum1_add]; refine natSum1_le (fun i _ _ => ?_)
    by_cases hiM : i < M
    · simp only [hiM, ↓reduceIte]; have hw : harmonicWeight N i ≤ natFact N := Nat.div_le_self _ _
      split <;> omega
    · simp only [hiM, ↓reduceIte, Nat.zero_add]; by_cases hQi : Q i
      · rw [tq_dec_false (fun h => h hQi)]; simp
      · rw [tq_dec_true hQi, tq_dec_true (fun hPi => hQi (hPQ i (Nat.le_of_not_lt hiM) hPi))]
        exact Nat.le_refl _
  have haux : ∀ k : Nat, natSum1 k (fun n => if n < M then natFact N else 0) ≤
      min k M * natFact N := fun k => by
    induction k with | zero => simp [natSum1] | succ j ih =>
      rw [natSum1]; by_cases hj : j + 1 < M
      · simp only [hj, ↓reduceIte]; rw [show min j M = j by omega] at ih
        rw [show min (j + 1) M = j + 1 by omega, Nat.succ_mul]; omega
      · simp only [hj, ↓reduceIte, Nat.add_zero]
        exact Nat.le_trans ih (Nat.mul_le_mul_right _ (by omega))
  have := Nat.le_trans (haux N) (Nat.mul_le_mul_right _ (Nat.min_le_right _ _))
  have := hM₀ N; rw [Nat.add_mul]; omega

/-- **Power-Saving → OrbitMinLe Bridge:** `HasPowerSavingDensityOne` (`0 < q`, `p < q`) on
`OrbitMinLe n (f n)` yields convergent exceptional reciprocal sum and quantitative log density. -/
theorem hasLogDensityOne_orbitMinLe_of_powerSaving {f : Nat → Nat} {p q : Nat}
    (hq : 0 < q) (hpq : p < q) (h : HasPowerSavingDensityOne (fun n => OrbitMinLe n (f n)) p q) :
    HasConvergentReciprocalExceptions (fun n => OrbitMinLe n (f n)) ∧
      HasQuantitativeLogDensityOne (fun n => OrbitMinLe n (f n)) ∧
      HasLogDensityOne (fun n => OrbitMinLe n (f n)) :=
  have hc := convergentReciprocal_of_powerSaving hq hpq h
  ⟨hc, (quantitativeLogDensity_iff_convergentReciprocal _).mpr hc,
    hasLogDensityOne_of_convergentReciprocal hc⟩

/-- **Unconditional `OrbitMinLe n (n - 1)` Convergence:** `HasFiniteStoppingTime` gives
`OrbitMinLe n (n - 1)` with convergent reciprocal sum and `O(1 / log N)` log density. -/
theorem hasConvergentReciprocal_orbitMinLe_pred :
    HasConvergentReciprocalExceptions (fun n => OrbitMinLe n (n - 1)) ∧
      HasQuantitativeLogDensityOne (fun n => OrbitMinLe n (n - 1)) :=
  have hc := hasConvergentReciprocal_eventually_mono 2 (fun _ hn ⟨k, _, hlt⟩ => ⟨k, by omega⟩)
    hasFiniteStoppingTime_convergent_reciprocal_sum
  ⟨hc, (quantitativeLogDensity_iff_convergentReciprocal _).mpr hc⟩

private def SparseSqBlocks (n : Nat) : Prop := ∃ k : Nat, 1 ≤ k ∧ bitLen n = k * k + 1

private theorem bitLen_eq_succ_of_dyadic {j n : Nat} (h1 : 2 ^ j ≤ n) (h2 : n < 2 ^ (j + 1)) :
    bitLen n = j + 1 := by
  have := two_pow_pred_bitLen_le (Nat.le_trans (Nat.two_pow_pos j) h1); have := lt_two_pow_bitLen n
  have ha : j < bitLen n := Nat.lt_of_not_ge (fun h =>
    absurd (Nat.pow_le_pow_right (by decide : 0 < 2) h) (by omega))
  have hb : bitLen n - 1 < j + 1 := Nat.lt_of_not_ge (fun h =>
    absurd (Nat.pow_le_pow_right (by decide : 0 < 2) h) (by omega))
  omega

private theorem bitLen_mono {a b : Nat} (hab : a ≤ b) : bitLen a ≤ bitLen b := by
  cases a with | zero => simp [bitLen] | succ a' =>
    have := two_pow_pred_bitLen_le (by omega : 1 ≤ a' + 1); have := lt_two_pow_bitLen b
    have hlt : bitLen (a' + 1) - 1 < bitLen b := Nat.lt_of_not_ge (fun h =>
      absurd (Nat.pow_le_pow_right (by decide : 0 < 2) h) (by omega))
    omega

private noncomputable def sumLog (E : Nat → Prop) (N M : Nat) : Nat :=
  natSum1 M (fun n => if @decide (E n) (Classical.propDecidable _) then harmonicWeight N n else 0)

private theorem sparseSqBlocks_single_block (N j : Nat) :
    sumLog (fun n => bitLen n = j + 1) N N ≤ natFact N := by
  have hle1 : sumLog (fun n => bitLen n = j + 1) N N ≤
      sumLog (fun n => bitLen n = j + 1) N (2 ^ (j + 1) - 1) := by
    by_cases hNj : N ≤ 2 ^ (j + 1) - 1
    · exact tq_natSum1_mono hNj _
    · have hlt : 2 ^ (j + 1) - 1 < N := Nat.lt_of_not_ge hNj
      have hzero : natSum1 (N - (2 ^ (j + 1) - 1)) (fun x =>
          if @decide (bitLen ((2 ^ (j + 1) - 1) + x) = j + 1) (Classical.propDecidable _) then
            harmonicWeight N ((2 ^ (j + 1) - 1) + x) else 0) = 0 := by
        rw [tq_natSum1_congr (g := fun _ => 0) (fun x hx1 _ => ?_), tq_natSum1_const]; simp
        have hbl : j + 2 ≤ bitLen ((2 ^ (j + 1) - 1) + x) := Nat.lt_of_not_ge (fun h =>
          absurd (Nat.pow_le_pow_right (by decide : 0 < 2) h)
            (by have := lt_two_pow_bitLen ((2 ^ (j + 1) - 1) + x); omega))
        rw [tq_dec_false (by omega)]; rfl
      unfold sumLog; conv => lhs; arg 1; rw [← Nat.add_sub_of_le (Nat.le_of_lt hlt)]
      rw [tq_natSum1_split, hzero, Nat.add_zero]; exact Nat.le_refl _
  have h2j : 1 ≤ 2 ^ j := Nat.two_pow_pos j
  have hzero0 : sumLog (fun n => bitLen n = j + 1) N (2 ^ j - 1) = 0 := by
    unfold sumLog; rw [tq_natSum1_congr (g := fun _ => 0) (fun x _ hx2 => ?_), tq_natSum1_const]
    simp; have hbl : bitLen x ≤ j := by
      cases x with | zero => simp [bitLen] | succ x' =>
        have ha := two_pow_pred_bitLen_le (by omega : 1 ≤ x' + 1)
        exact Nat.le_of_not_lt (fun h => absurd (Nat.pow_le_pow_right (by decide : 0 < 2)
          (by omega : j ≤ bitLen (x' + 1) - 1)) (by omega))
    rw [tq_dec_false (by omega)]; rfl
  have htail := natSum1_le (N := 2 ^ j)
    (f := fun x => if @decide (bitLen ((2 ^ j - 1) + x) = j + 1) (Classical.propDecidable _)
      then harmonicWeight N ((2 ^ j - 1) + x) else 0)
    (g := fun x => harmonicWeight N ((2 ^ j - 1) + x)) (fun x _ _ => by split <;> omega)
  unfold sumLog at hle1 hzero0
  rw [show 2 ^ (j + 1) - 1 = (2 ^ j - 1) + 2 ^ j by rw [Nat.pow_succ]; omega,
    tq_natSum1_split, hzero0, Nat.zero_add] at hle1
  exact Nat.le_trans hle1 (Nat.le_trans htail (block_harmonic_sum_le j N))

private theorem sparseSqBlocks_upper (N K : Nat) (hK : bitLen N < (K + 1) * (K + 1) + 1) :
    logExceptionalNum (fun n => ¬ SparseSqBlocks n) N ≤ K * natFact N := by
  have haux : ∀ m : Nat,
      sumLog (fun n => ∃ k : Nat, 1 ≤ k ∧ k ≤ m ∧ bitLen n = k * k + 1) N N ≤ m * natFact N :=
    fun m => by induction m with
    | zero => unfold sumLog; rw [tq_natSum1_congr (g := fun _ => 0) (fun i _ _ => by
        rw [tq_dec_false (fun ⟨k, hk1, hk0, _⟩ => by omega)]; rfl), tq_natSum1_const]; simp
    | succ m ih =>
      have hsplit : sumLog (fun n => ∃ k : Nat, 1 ≤ k ∧ k ≤ m + 1 ∧ bitLen n = k * k + 1) N N ≤
          sumLog (fun n => ∃ k : Nat, 1 ≤ k ∧ k ≤ m ∧ bitLen n = k * k + 1) N N +
          sumLog (fun n => bitLen n = (m + 1) * (m + 1) + 1) N N := by
        unfold sumLog; rw [← tq_natSum1_add]; refine natSum1_le (fun i _ _ => ?_)
        by_cases hex : ∃ k : Nat, 1 ≤ k ∧ k ≤ m + 1 ∧ bitLen i = k * k + 1
        · rcases hex with ⟨k, hk1, hk2, heq⟩; rw [tq_dec_true ⟨k, hk1, hk2, heq⟩]
          by_cases hkm : k ≤ m
          · rw [tq_dec_true ⟨k, hk1, hkm, heq⟩]; exact Nat.le_add_right _ _
          · have hkeq : k = m + 1 := by omega
            subst hkeq; rw [tq_dec_true heq]; exact Nat.le_add_left _ _
        · rw [tq_dec_false hex]; simp
      have hblk := sparseSqBlocks_single_block N ((m + 1) * (m + 1)); rw [Nat.succ_mul]; omega
  have hcongr : logExceptionalNum (fun n => ¬ SparseSqBlocks n) N =
      sumLog (fun n => ∃ k : Nat, 1 ≤ k ∧ k ≤ K ∧ bitLen n = k * k + 1) N N :=
    tq_natSum1_congr (fun i _ hiN => by
      have hbi := bitLen_mono hiN; by_cases hsp : SparseSqBlocks i
      · rcases hsp with ⟨k, hk1, hkeq⟩
        have hkK : k ≤ K := Nat.le_of_not_lt (fun hgt => by
          have : (K + 1) * (K + 1) ≤ k * k := Nat.mul_le_mul hgt hgt; omega)
        rw [tq_dec_true (fun h => h ⟨k, hk1, hkeq⟩), tq_dec_true ⟨k, hk1, hkK, hkeq⟩]
      · rw [tq_dec_false (fun h => h hsp), tq_dec_false (fun ⟨k, hk1, _, hkeq⟩ =>
          hsp ⟨k, hk1, hkeq⟩)])
  rw [hcongr]; exact haux K

private theorem sparseSqBlocks_lower (K : Nat) :
    let N := 2 ^ (K * K + 1)
    K * natFact N ≤ 2 * logExceptionalNum (fun n => ¬ SparseSqBlocks n) N := by
  intro N
  have haux : ∀ m : Nat, m ≤ K →
      m * natFact N ≤ 2 * sumLog SparseSqBlocks N (2 ^ (m * m + 1) - 1) := by
    intro m hm; induction m with | zero => simp [sumLog, natSum1] | succ m ih =>
      let j := (m + 1) * (m + 1)
      have hm_le_j : m * m + 1 ≤ j := by dsimp [j]; rw [Nat.succ_mul, Nat.mul_succ]; omega
      have hpow_le := Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide : 0 < 2) hm_le_j) 1
      have h2j_le_N : 2 ^ (j + 1) ≤ N := Nat.pow_le_pow_right (by decide : 0 < 2)
        (Nat.add_le_add_right (Nat.mul_le_mul hm hm) 1)
      have hsplit : 2 ^ (j + 1) - 1 = (2 ^ j - 1) + 2 ^ j := by
        have := Nat.two_pow_pos j; rw [Nat.pow_succ]; omega
      have hhead := Nat.le_trans (ih (by omega)) (Nat.mul_le_mul_left 2 (tq_natSum1_mono hpow_le _))
      have hconst := tq_natSum1_const_le (N := 2 ^ j) (c := harmonicWeight N (2 ^ (j + 1)))
        (f := fun x => if @decide (SparseSqBlocks ((2 ^ j - 1) + x)) (Classical.propDecidable _)
          then harmonicWeight N ((2 ^ j - 1) + x) else 0) (fun x hx1 hx2 => by
          have h2j : 1 ≤ 2 ^ j := Nat.two_pow_pos j
          have h1 : 2 ^ j ≤ (2 ^ j - 1) + x := by omega
          have h2 : (2 ^ j - 1) + x < 2 ^ (j + 1) := by rw [Nat.pow_succ]; omega
          rw [tq_dec_true ⟨m + 1, Nat.succ_pos m, bitLen_eq_succ_of_dyadic h1 h2⟩]
          exact harmonicWeight_antitone_le (Nat.le_trans h2j h1) (Nat.le_of_lt h2) h2j_le_N)
      have hmul : 2 * (2 ^ j * harmonicWeight N (2 ^ (j + 1))) = natFact N := by
        rw [← Nat.mul_assoc, Nat.mul_comm 2 (2 ^ j), ← Nat.pow_succ]
        exact mul_harmonicWeight (Nat.two_pow_pos (j + 1)) h2j_le_N
      unfold sumLog at hhead ⊢; rw [hsplit, tq_natSum1_split, Nat.mul_add, Nat.succ_mul]; omega
  have hmono := Nat.mul_le_mul_left 2 (tq_natSum1_mono (Nat.sub_le N 1) (fun n =>
    if @decide (SparseSqBlocks n) (Classical.propDecidable _) then harmonicWeight N n else 0))
  have heq : logExceptionalNum (fun n => ¬ SparseSqBlocks n) N = sumLog SparseSqBlocks N N :=
    tq_natSum1_congr (fun i _ _ => by
      by_cases h : SparseSqBlocks i
      · rw [tq_dec_true (fun nh => nh h), tq_dec_true h]
      · rw [tq_dec_false (fun nh => nh h), tq_dec_false h])
  rw [heq]; exact Nat.le_trans (haux K (Nat.le_refl K)) hmono

private theorem sparseSqBlocks_hasLogDensityOne :
    HasLogDensityOne (fun n => ¬ SparseSqBlocks n) := by
  intro D hD; refine ⟨2 ^ ((2 * D + 2) * (2 * D + 2)), fun N hN => ?_⟩
  have hN1 : 1 ≤ N := Nat.le_trans (Nat.two_pow_pos _) hN
  have hbit_gt : (2 * D + 2) * (2 * D + 2) < bitLen N := Nat.lt_of_not_ge (fun hle =>
    absurd (Nat.pow_le_pow_right (by decide : 0 < 2) hle) (by have := lt_two_pow_bitLen N; omega))
  have hsub : ∀ b : Nat, 1 ≤ b → ∃ K0 : Nat, K0 * K0 + 1 ≤ b ∧ b < (K0 + 1) * (K0 + 1) + 1 := by
    intro b hb; induction b with | zero => omega | succ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact ⟨0, by decide, by decide⟩
      · rcases ih hk with ⟨m, hm1, hm2⟩
        by_cases hlt : k + 1 < (m + 1) * (m + 1) + 1; exact ⟨m, by omega, hlt⟩
        exact ⟨m + 1, by omega, by rw [Nat.succ_mul, Nat.mul_succ]; omega⟩
  rcases hsub (bitLen N) (by omega) with ⟨K0, hK0_le, hK0_lt⟩
  have hK0_ge : 2 * D + 1 ≤ K0 := Nat.le_of_not_lt (fun hlt => by
    have h1 := Nat.mul_le_mul (by omega : K0 + 1 ≤ 2 * D + 1) (by omega : K0 + 1 ≤ 2 * D + 1)
    have h2 := Nat.mul_lt_mul_of_lt_of_lt (by omega : 2 * D + 1 < 2 * D + 2)
      (by omega : 2 * D + 1 < 2 * D + 2); omega)
  have h2DK : 2 * D * K0 < bitLen N :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right (by omega : 2 * D < K0) (by omega)) (by omega)
  have hmul : 2 * (logExceptionalNum (fun n => ¬ SparseSqBlocks n) N * D) < 2 * harmonicSumNum N :=
    calc _ ≤ 2 * (K0 * natFact N * D) :=
            Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right D (sparseSqBlocks_upper N K0 hK0_lt))
      _ = (2 * D * K0) * natFact N := by ac_rfl
      _ < bitLen N * natFact N := Nat.mul_lt_mul_of_pos_right h2DK (natFact_pos N)
      _ ≤ 2 * harmonicSumNum N := bitLen_mul_natFact_le_two_harmonicSumNum hN1
  omega

/-- **Tao (2022) `o(1)` vs `PROVE-A1` Power-Saving Check:**
(1) Qualitative `HasLogDensityOne` does NOT imply `HasConvergentReciprocalExceptions` (`∑ 1/n < ∞`);
(2) `PROVE-A1` power-saving (`p < q`) DOES imply `HasConvergentReciprocalExceptions` and
`HasQuantitativeLogDensityOne`;
(3) unconditionally, `HasFiniteStoppingTime` has convergent exceptional reciprocal sum. -/
theorem tao_almost_bounded_implies_convergent_bad_orbits_check :
    (∃ P : Nat → Prop, HasLogDensityOne P ∧ ¬ HasConvergentReciprocalExceptions P) ∧
    (∀ P : Nat → Prop, ∀ p q : Nat, 0 < q → p < q →
      HasPowerSavingDensityOne P p q →
      HasConvergentReciprocalExceptions P ∧ HasQuantitativeLogDensityOne P) ∧
    (HasConvergentReciprocalExceptions HasFiniteStoppingTime ∧
      HasQuantitativeLogDensityOne HasFiniteStoppingTime) := by
  refine ⟨⟨fun n => ¬ SparseSqBlocks n, sparseSqBlocks_hasLogDensityOne, ?_⟩, ?_,
    hasFiniteStoppingTime_convergent_reciprocal_sum, hasFiniteStoppingTime_quantitative_log_density⟩
  · rintro ⟨M₀, hM₀⟩
    have hlow := sparseSqBlocks_lower (2 * M₀ + 1); dsimp only at hlow
    have hup := hM₀ (2 ^ ((2 * M₀ + 1) * (2 * M₀ + 1) + 1))
    have hpos := natFact_pos (2 ^ ((2 * M₀ + 1) * (2 * M₀ + 1) + 1))
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc] at hlow; omega
  · intro P p q hq hpq hpow
    have hc := convergentReciprocal_of_powerSaving hq hpq hpow
    exact ⟨hc, (quantitativeLogDensity_iff_convergentReciprocal P).mpr hc⟩

/-! ### 4. Explicit Barrier 1–5 Separations -/

private theorem genIter_mod_of_cycle {a b : Int} {n : Int} {k : Nat} (hk : 0 < k)
    (hcyc : Barriers.genIter a b k n = n) :
    ∀ t : Nat, Barriers.genIter a b t n = Barriers.genIter a b (t % k) n := by
  intro t; induction t using Nat.strongRecOn with | ind t ih =>
    by_cases ht : t < k
    · rw [Nat.mod_eq_of_lt ht]
    · have hge : k ≤ t := Nat.le_of_not_lt ht
      have hadd : ∀ u v z, Barriers.genIter a b v (Barriers.genIter a b u z) =
          Barriers.genIter a b (u + v) z := fun u v z => by
        induction u generalizing z with | zero => simp [Barriers.genIter] | succ u ihu =>
          simp only [Barriers.genIter, Nat.succ_add]; exact ihu _
      have hstep : Barriers.genIter a b t n = Barriers.genIter a b (t - k) n := by
        calc Barriers.genIter a b t n
            = Barriers.genIter a b (k + (t - k)) n := by rw [Nat.add_sub_of_le hge]
          _ = Barriers.genIter a b (t - k) (Barriers.genIter a b k n) := (hadd k (t - k) n).symm
          _ = Barriers.genIter a b (t - k) n := by rw [hcyc]
      rw [hstep, ih (t - k) (by omega), Nat.mod_eq_sub_mod hge]

/-- **Barriers 1–3 Separation (`3n - 1`, `5n + 1`, `ℤ_{<0}`):** explicit non-trivial cycles
staying strictly away from `1` and violating finite stopping time (`n_min ≤ genIter t n`). -/
theorem barrier1_3_quantitative_cycles :
    (∀ t : Nat, 5 ≤ Barriers.genIter 3 (-1) t 5 ∧ Barriers.genIter 3 (-1) t 5 ≠ 1) ∧
    (∀ t : Nat, 13 ≤ Barriers.genIter 5 1 t 13 ∧ Barriers.genIter 5 1 t 13 ≠ 1) ∧
    (∀ t : Nat, Barriers.genIter 3 1 t (-5) < 0 ∧ Barriers.genIter 3 1 t (-5) ≠ 1) := by
  refine ⟨fun t => ?_, fun t => ?_, fun t => ?_⟩
  · rw [genIter_mod_of_cycle (by decide : 0 < 5) Barriers.three_n_minus_one_cycle_5.1 t]
    have hlt : t % 5 < 5 := Nat.mod_lt t (by decide)
    match t % 5, hlt with | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => decide
  · rw [genIter_mod_of_cycle (by decide : 0 < 10) Barriers.five_n_plus_one_cycle_13.1 t]
    have hlt : t % 10 < 10 := Nat.mod_lt t (by decide)
    match t % 10, hlt with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => decide
  · rw [genIter_mod_of_cycle (by decide : 0 < 5) Barriers.neg_int_cycle_neg5.1 t]
    have hlt : t % 5 < 5 := Nat.mod_lt t (by decide)
    match t % 5, hlt with | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => decide

private theorem mersenne_dyadic_unique {j x y : Nat} (hx1 : 1 ≤ x) (hx2 : x ≤ 2 ^ j)
    (hy1 : 1 ≤ y) (hy2 : y ≤ 2 ^ j)
    (hm1 : IsMersenneException ((2 ^ j - 1) + x))
    (hm2 : IsMersenneException ((2 ^ j - 1) + y)) : x = y := by
  have hk_eq : ∀ k z, 1 ≤ z → z ≤ 2 ^ j → (2 ^ j - 1) + z = 2 ^ k - 1 → k = j + 1 := by
    intro k z hz1 hz2 heq; have h2j : 1 ≤ 2 ^ j := Nat.two_pow_pos j
    have ha : j < k := Nat.lt_of_not_ge (fun h =>
      absurd (Nat.pow_le_pow_right (by decide : 0 < 2) h) (by omega))
    have hb : k < j + 2 := Nat.lt_of_not_ge (fun h =>
      absurd (Nat.pow_le_pow_right (by decide : 0 < 2) h) (by rw [Nat.pow_succ]; omega))
    omega
  rcases hm1 with ⟨k1, _, hk1⟩; rcases hm2 with ⟨k2, _, hk2⟩
  have he1 := hk_eq k1 x hx1 hx2 hk1; have he2 := hk_eq k2 y hy1 hy2 hk2
  subst he1; subst he2; omega

private theorem mersenne_block_le (j N : Nat) :
    2 ^ j * natSum1 (2 ^ j) (fun x => if @decide (IsMersenneException ((2 ^ j - 1) + x))
      (Classical.propDecidable _) then harmonicWeight N ((2 ^ j - 1) + x) else 0) ≤ natFact N := by
  let g : Nat → Nat := fun x => if @decide (IsMersenneException ((2 ^ j - 1) + x))
    (Classical.propDecidable _) then harmonicWeight N ((2 ^ j - 1) + x) else 0
  have haux : ∀ L : Nat, L ≤ 2 ^ j →
      ((∀ x : Nat, 1 ≤ x → x ≤ L → ¬ IsMersenneException ((2 ^ j - 1) + x)) ∧ natSum1 L g = 0) ∨
      ∃ x₀ : Nat, 1 ≤ x₀ ∧ x₀ ≤ L ∧ IsMersenneException ((2 ^ j - 1) + x₀) ∧
        natSum1 L g = harmonicWeight N ((2 ^ j - 1) + x₀) := fun L hL => by
    induction L with
    | zero => exact Or.inl ⟨fun _ h1 h0 => by omega, rfl⟩
    | succ L ih =>
      rcases ih (by omega) with ⟨hnone, hzero⟩ | ⟨x₀, hx1, hx2, hm0, hsum0⟩
      · by_cases hmL : IsMersenneException ((2 ^ j - 1) + (L + 1))
        · exact Or.inr ⟨L + 1, Nat.succ_pos L, Nat.le_refl _, hmL,
            by dsimp [g]; rw [natSum1, hzero, Nat.zero_add, tq_dec_true hmL]; rfl⟩
        · refine Or.inl ⟨fun x hx1 hx2 => ?_,
            by dsimp [g]; rw [natSum1, hzero, tq_dec_false hmL]; rfl⟩
          rcases Nat.eq_or_lt_of_le hx2 with rfl | hlt; exact hmL; exact hnone x hx1 (by omega)
      · refine Or.inr ⟨x₀, hx1, by omega, hm0, ?_⟩
        have hmL : ¬ IsMersenneException ((2 ^ j - 1) + (L + 1)) := fun hm =>
          by have := mersenne_dyadic_unique hx1 (by omega) (Nat.succ_pos L) hL hm0 hm; omega
        dsimp [g]; rw [natSum1, hsum0, tq_dec_false hmL]; rfl
  rcases haux (2 ^ j) (Nat.le_refl _) with ⟨_, hzero⟩ | ⟨x₀, hx1, _, _, hsum⟩
  · change 2 ^ j * natSum1 (2 ^ j) g ≤ natFact N; rw [hzero, Nat.mul_zero]; exact Nat.zero_le _
  · change 2 ^ j * natSum1 (2 ^ j) g ≤ natFact N; rw [hsum]
    exact Nat.le_trans (Nat.mul_le_mul_right _ (by omega : 2 ^ j ≤ (2 ^ j - 1) + x₀))
      (Nat.mul_div_le (natFact N) _)

private theorem mersenne_dyadic_prefix_le (N m : Nat) :
    2 ^ m * sumLog IsMersenneException N (2 ^ (m + 1) - 1) ≤ (2 ^ (m + 1) - 2) * natFact N := by
  induction m with
  | zero =>
    unfold sumLog; rw [show 2 ^ (0 + 1) - 1 = 1 by decide, show 2 ^ (0 + 1) - 2 = 0 by decide,
      Nat.pow_zero, Nat.one_mul, Nat.zero_mul, natSum1, natSum1, Nat.zero_add,
      tq_dec_false (fun ⟨k, hk, _⟩ => by
        have := Nat.pow_le_pow_right (by decide : 0 < 2) hk; omega)]
    exact Nat.zero_le _
  | succ m ih =>
    have h2m : 1 ≤ 2 ^ (m + 1) := Nat.two_pow_pos (m + 1)
    unfold sumLog at ih ⊢
    rw [show 2 ^ (m + 2) - 1 = (2 ^ (m + 1) - 1) + 2 ^ (m + 1) by rw [Nat.pow_succ]; omega,
      tq_natSum1_split, Nat.mul_add]
    have h1 : 2 ^ (m + 1) * natSum1 (2 ^ (m + 1) - 1) (fun n =>
        if @decide (IsMersenneException n) (Classical.propDecidable _)
        then harmonicWeight N n else 0) ≤ 2 * (2 ^ (m + 1) - 2) * natFact N :=
      calc _ = 2 * (2 ^ m * natSum1 (2 ^ (m + 1) - 1) (fun n => if @decide (IsMersenneException n)
            (Classical.propDecidable _) then harmonicWeight N n else 0)) := by
            conv => lhs; arg 1; rw [Nat.pow_succ, Nat.mul_comm (2 ^ m) 2]
            rw [Nat.mul_assoc]
        _ ≤ 2 * ((2 ^ (m + 1) - 2) * natFact N) := Nat.mul_le_mul_left 2 ih
        _ = 2 * (2 ^ (m + 1) - 2) * natFact N := (Nat.mul_assoc _ _ _).symm
    have hpos2 : 2 ≤ 2 ^ (m + 1) := by have := Nat.two_pow_pos m; rw [Nat.pow_succ]; omega
    calc _ ≤ 2 * (2 ^ (m + 1) - 2) * natFact N + natFact N :=
          Nat.add_le_add h1 (mersenne_block_le (m + 1) N)
      _ = (2 * (2 ^ (m + 1) - 2) + 1) * natFact N := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ (2 ^ (m + 1 + 1) - 2) * natFact N :=
          Nat.mul_le_mul_right _ (by rw [Nat.pow_succ 2 (m + 1)]; omega)

/-- **Mersenne Explicit Convergent Reciprocal Sum:** `∑_{2^k - 1 ≤ N, k ≥ 2} 1 / (2^k - 1) ≤ 2`
for all `N` in pure `Nat`. -/
theorem mersenne_reciprocal_sum_le_two (N : Nat) :
    logExceptionalNum (fun n => ¬ IsMersenneException n) N ≤ 2 * natFact N := by
  have hlt : N ≤ 2 ^ (bitLen N + 1) - 1 := by
    have := lt_two_pow_bitLen N; have := Nat.pow_le_pow_right (by decide : 0 < 2)
      (Nat.le_succ (bitLen N)); omega
  have hcongr : logExceptionalNum (fun n => ¬ IsMersenneException n) N =
      sumLog IsMersenneException N N := tq_natSum1_congr (fun i _ _ => by
    by_cases h : IsMersenneException i
    · rw [tq_dec_true (fun nh => nh h), tq_dec_true h]
    · rw [tq_dec_false (fun nh => nh h), tq_dec_false h])
  have hbd := Nat.le_trans (Nat.mul_le_mul_left (2 ^ bitLen N)
      (tq_natSum1_mono hlt (fun n => if @decide (IsMersenneException n)
        (Classical.propDecidable _) then harmonicWeight N n else 0)))
    (Nat.le_trans (mersenne_dyadic_prefix_le N (bitLen N)) (Nat.mul_le_mul_right _
      (by rw [Nat.pow_succ]; omega : 2 ^ (bitLen N + 1) - 2 ≤ 2 * 2 ^ bitLen N)))
  unfold sumLog at hcongr
  rw [← hcongr, show 2 * 2 ^ bitLen N * natFact N = 2 ^ bitLen N * (2 * natFact N) by ac_rfl]
    at hbd
  exact Nat.le_of_mul_le_mul_left hbd (Nat.two_pow_pos (bitLen N))

/-- **Barrier 4 Separation (`ℤ₂` & Sparse Convergent Counterexamples):**
Mersenne numbers `{2^k - 1 | k ≥ 2}` have convergent reciprocal sum (`≤ 2`) and
`HasQuantitativeLogDensityOne` yet infinitely many exceptions, while `ℤ_(2) ⊂ ℤ₂` admits positive
(`211/13`) and negative non-integral (`-19/11`) periodic orbits avoiding `1`. -/
theorem barrier4_mersenne_convergent_reciprocal :
    (HasConvergentReciprocalExceptions (fun n => ¬ IsMersenneException n) ∧
      HasQuantitativeLogDensityOne (fun n => ¬ IsMersenneException n) ∧
      ∀ M : Nat, ∃ n : Nat, M ≤ n ∧ IsMersenneException n) ∧
    (OddDenomRat.syracuseIter 5 (⟨211, 13, by decide⟩ : OddDenomRat) = ⟨211, 13, by decide⟩ ∧
      OddDenomRat.syracuseIter 3 (⟨-19, 11, by decide⟩ : OddDenomRat) = ⟨-19, 11, by decide⟩) := by
  have hc : HasConvergentReciprocalExceptions (fun n => ¬ IsMersenneException n) :=
    ⟨2, mersenne_reciprocal_sum_le_two⟩
  refine ⟨⟨hc, (quantitativeLogDensity_iff_convergentReciprocal _).mpr hc, fun M => ?_⟩, ?_⟩
  · refine ⟨2 ^ (M + 2) - 1, ?_, ⟨M + 2, by omega, rfl⟩⟩
    have hgt : M + 2 ≤ 2 ^ (M + 2) := by
      induction M with | zero => decide | succ M ih => rw [Nat.pow_succ]; omega
    omega
  · exact ⟨by have h := twoAdic_cycle_211_over_13; rcases h with ⟨hx, _, hcyc, _⟩; rwa [hx] at hcyc,
      by have h := twoAdic_cycle_neg19_over_11; rcases h with ⟨hx, hcyc, _⟩; rwa [hx] at hcyc⟩

/-- **Barrier 5 Separation (Conway / Ergodic-vs-Universal):** convergent exceptional reciprocal
sum (`∑ 1/n < ∞`) and `O(1 / log N)` quantitative logarithmic density still permit excluding any
putative cycle `cycleOrbitList n L`. -/
theorem convergent_reciprocal_allows_cycle (n L : Nat) :
    HasConvergentReciprocalExceptions (fun m => HasFiniteStoppingTime m ∧ m ∉ cycleOrbitList n L) ∧
    HasQuantitativeLogDensityOne (fun m => HasFiniteStoppingTime m ∧ m ∉ cycleOrbitList n L) :=
  have hc := convergentReciprocal_of_powerSaving (by decide) (by decide)
    (sharper_powerSaving_allows_cycle n L)
  ⟨hc, (quantitativeLogDensity_iff_convergentReciprocal _).mpr hc⟩

/-- **Barrier 5 Divergent-Orbit Separation:** excluding any exponentially divergent orbit
(`∀ t, 2 ^ (t / C) ≤ collatzIter t n`) still preserves `HasConvergentReciprocalExceptions` and
`HasQuantitativeLogDensityOne`. -/
theorem convergent_reciprocal_allows_expDivergent {n C : Nat} (hC : 1 ≤ C)
    (hexp : ∀ t : Nat, 2 ^ (t / C) ≤ collatzIter t n) :
    HasConvergentReciprocalExceptions
      (fun m => HasFiniteStoppingTime m ∧ ¬ ∃ t : Nat, collatzIter t n = m) ∧
    HasQuantitativeLogDensityOne
      (fun m => HasFiniteStoppingTime m ∧ ¬ ∃ t : Nat, collatzIter t n = m) :=
  have hc := convergentReciprocal_of_powerSaving (by decide) (by decide)
    (hasPowerSaving_and_expSparse (by decide) (by decide) sharper_power_saving_density_19_20
      (isExpSparse_of_exp_seq (fun t => collatzIter t n) hC hexp))
  ⟨hc, (quantitativeLogDensity_iff_convergentReciprocal _).mpr hc⟩

end SolveCollatz
