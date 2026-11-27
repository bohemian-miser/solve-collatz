/-
Copyright (c) 2026 The solve-collatz contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Collatz.Prove.Automata.ModularDescent
public import Collatz.Known.TerrasDensity
public import Collatz.Core.TwoAdic

/-!
# Sieve Refinement, Higher-Modulus Descent & Covering Obstructions (`PROVE-C1` Phase 2)
Extends `Collatz.Prove.Automata.ModularDescent` in pure Lean 4 core (zero Mathlib):
1. Refinement & density monotonicity (`coveredCount K + uncoveredCount K = 2 ^ K`).
2. Kernel-verified `K = 10` (`960 / 1024`) and `K = 12` (`3870 / 4096`) sieves + small-`n` bridge.
3. Universal incompleteness (`1 ≤ uncoveredCount K`) and exponential survival (`2^m ≤ u(3m+1)`).
4. Projective `ℤ₂` non-dropping towers (`OddDenomRat`) from `-5` and `-19 / 11` (Barrier 4).
5. Barrier 2 (`5n + 1`) contrast (`> 50%` failure at `2 * m`, and `758` vs `960` at `K = 10`).
-/

@[expose] public section
namespace SolveCollatz

/-! ### 1. Sieve Refinement, Complement & Density Monotonicity -/
/-- Number of covered residue classes `r < 2 ^ K` (`dropsWithin K r = true`). -/
def coveredCount (K : Nat) : Nat := sieveCoveredCount K
/-- Number of uncovered residue classes `r < 2 ^ K` (`dropsWithin K r = false`). -/
def uncoveredCount (K : Nat) : Nat := countPow2 (fun r => !dropsWithin K r) K 0
/-- `coveredCount` equals `ModularDescent.sieveCoveredCount`. -/
theorem coveredCount_eq_sieveCoveredCount (K : Nat) :
    coveredCount K = sieveCoveredCount K := rfl
/-- Linear count equivalence for `coveredCount`. -/
theorem coveredCount_eq_countBelow (K : Nat) :
    coveredCount K = countBelow (dropsWithin K) (2 ^ K) := sieveCoveredCount_eq_countBelow K
/-- Linear count equivalence for `uncoveredCount`. -/
theorem uncoveredCount_eq_countBelow (K : Nat) :
    uncoveredCount K = countBelow (fun r => !dropsWithin K r) (2 ^ K) := by
  simpa [uncoveredCount, countBelow] using
    (countBelow_add_two_pow (fun r => !dropsWithin K r) K 0).symm
/-- Dyadic sum of `p` and `!p` over `[lo, lo + 2 ^ d)` equals `2 ^ d`. -/
theorem countPow2_add_compl (p : Nat → Bool) (d lo : Nat) :
    countPow2 p d lo + countPow2 (fun r => !p r) d lo = 2 ^ d := by
  induction d generalizing lo with
  | zero => simp only [countPow2, Nat.pow_zero]; by_cases hp : p lo <;> simp [hp]
  | succ d ih => simp only [countPow2, Nat.pow_succ]; have := ih lo; have := ih (lo + 2 ^ d); omega
/-- Exact partition identity: `coveredCount K + uncoveredCount K = 2 ^ K`. -/
theorem coveredCount_add_uncoveredCount (K : Nat) :
    coveredCount K + uncoveredCount K = 2 ^ K := countPow2_add_compl (dropsWithin K) K 0
/-- Horizon monotonicity: `K₁ ≤ K₂` and `dropsWithin K₁ r = true` give `dropsWithin K₂ r`. -/
theorem dropsWithin_mono_horizon {K₁ K₂ r : Nat} (h : K₁ ≤ K₂)
    (hc : dropsWithin K₁ r = true) : dropsWithin K₂ r = true := by
  induction h with | refl => exact hc | step _ ih => simp [dropsWithin, ih]
private theorem add_two_pow_mul_mod_le {k K r q : Nat} (hk : k ≤ K) :
    (r + 2 ^ K * q) % 2 ^ k = r % 2 ^ k := by
  rcases (⟨2 ^ (K - k), by rw [← Nat.pow_add, Nat.add_sub_of_le hk]⟩ : 2 ^ k ∣ 2 ^ K) with ⟨m, hm⟩
  rw [hm, Nat.mul_assoc, Nat.add_mul_mod_self_left]
/-- Periodicity of `dropsWithin K` modulo `2 ^ K`. -/
theorem dropsWithin_add_two_pow (K r q : Nat) :
    dropsWithin K (r + 2 ^ K * q) = dropsWithin K r := by
  apply Bool.eq_iff_iff.mpr; simp only [dropsWithin_iff]; constructor
  · rintro ⟨k, hk1, hkK, hc⟩; rw [add_two_pow_mul_mod_le hkK] at hc; exact ⟨k, hk1, hkK, hc⟩
  · rintro ⟨k, hk1, hkK, hc⟩; refine ⟨k, hk1, hkK, ?_⟩; rwa [add_two_pow_mul_mod_le hkK]
/-- `dropsWithin K (r % 2 ^ K) = dropsWithin K r`. -/
theorem dropsWithin_mod_eq (K r : Nat) : dropsWithin K (r % 2 ^ K) = dropsWithin K r := by
  have h := dropsWithin_add_two_pow K (r % 2 ^ K) (r / 2 ^ K)
  rw [Nat.mod_add_div] at h; exact h.symm
/-- Every covered residue `r` at `K` lifts to both `r` and `r + 2 ^ K` at `K + 1`. -/
theorem dropsWithin_lift_pair {K r : Nat} (h : dropsWithin K r = true) :
    dropsWithin (K + 1) r = true ∧ dropsWithin (K + 1) (r + 2 ^ K) = true :=
  ⟨dropsWithin_mono_horizon (Nat.le_succ K) h, dropsWithin_mono_horizon (Nat.le_succ K)
    (by simpa [Nat.mul_one] using (dropsWithin_add_two_pow K r 1).trans h)⟩
/-- Pointwise implication on `[lo, lo + 2 ^ d)` yields `countPow2` monotonicity. -/
theorem countPow2_le_of_imp {p q : Nat → Bool} (d lo : Nat)
    (h : ∀ r : Nat, lo ≤ r → r < lo + 2 ^ d → p r = true → q r = true) :
    countPow2 p d lo ≤ countPow2 q d lo := by
  induction d generalizing lo with
  | zero =>
    simp only [countPow2]; cases hp : p lo
    · simp
    · simp [h lo (Nat.le_refl lo) (by simp) hp]
  | succ d ih =>
    have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
    rw [hpow] at h; have := ih lo (fun r hr1 hr2 => h r hr1 (by omega))
    have := ih (lo + 2 ^ d) (fun r hr1 hr2 => h r (by omega) (by omega))
    simp only [countPow2]; omega
/-- Pointwise Boolean equivalence on `[lo, lo + 2 ^ d)` preserves `countPow2`. -/
theorem countPow2_congr {p q : Nat → Bool} (d lo : Nat)
    (h : ∀ r : Nat, lo ≤ r → r < lo + 2 ^ d → p r = q r) :
    countPow2 p d lo = countPow2 q d lo := by
  have h1 := countPow2_le_of_imp d lo (fun r hr1 hr2 hp => (h r hr1 hr2).symm.trans hp)
  have h2 := countPow2_le_of_imp d lo (fun r hr1 hr2 hq => (h r hr1 hr2).trans hq); omega
private theorem countPow2_shift (p : Nat → Bool) (d lo M : Nat) :
    countPow2 (fun r => p (r + M)) d lo = countPow2 p d (lo + M) := by
  induction d generalizing lo with
  | zero => rfl | succ d ih => simp only [countPow2, ih]; rw [Nat.add_right_comm lo (2 ^ d) M]
/-- **Refinement Doubling Law:** `2 * coveredCount K ≤ coveredCount (K + 1)`. -/
theorem two_mul_coveredCount_le (K : Nat) : 2 * coveredCount K ≤ coveredCount (K + 1) := by
  have hlo : coveredCount K ≤ countPow2 (dropsWithin (K + 1)) K 0 :=
    countPow2_le_of_imp K 0 (fun r _ _ hr => (dropsWithin_lift_pair hr).1)
  have hhi : coveredCount K ≤ countPow2 (dropsWithin (K + 1)) K (2 ^ K) := by
    have hs := countPow2_shift (dropsWithin (K + 1)) K 0 (2 ^ K); rw [Nat.zero_add] at hs; rw [← hs]
    exact countPow2_le_of_imp K 0 (fun r _ _ hr => (dropsWithin_lift_pair hr).2)
  change 2 * countPow2 (dropsWithin K) K 0 ≤
    countPow2 (dropsWithin (K + 1)) K 0 + countPow2 (dropsWithin (K + 1)) K (0 + 2 ^ K)
  unfold coveredCount sieveCoveredCount at hlo hhi; rw [Nat.zero_add]; omega
/-- Dual refinement bound: `uncoveredCount (K + 1) ≤ 2 * uncoveredCount K`. -/
theorem uncoveredCount_succ_le (K : Nat) : uncoveredCount (K + 1) ≤ 2 * uncoveredCount K := by
  have := coveredCount_add_uncoveredCount K; have := coveredCount_add_uncoveredCount (K + 1)
  have := two_mul_coveredCount_le K
  have hpow : 2 ^ (K + 1) = 2 * 2 ^ K := by rw [Nat.pow_succ, Nat.mul_comm]
  omega
/-- **Covered Density Monotonicity:** `coveredCount K₁ * 2 ^ K₂ ≤ coveredCount K₂ * 2 ^ K₁`. -/
theorem covered_density_mono {K₁ K₂ : Nat} (h : K₁ ≤ K₂) :
    coveredCount K₁ * 2 ^ K₂ ≤ coveredCount K₂ * 2 ^ K₁ := by
  induction h with
  | refl => exact Nat.le_refl _
  | @step K₂ _ ih =>
    have hmul := Nat.mul_le_mul_right 2 ih
    have hrhs : (coveredCount K₂ * 2 ^ K₁) * 2 ≤ coveredCount (K₂ + 1) * 2 ^ K₁ := by
      rw [Nat.mul_right_comm, Nat.mul_comm (coveredCount K₂) 2]
      exact Nat.mul_le_mul_right _ (two_mul_coveredCount_le K₂)
    rw [Nat.pow_succ 2 K₂, ← Nat.mul_assoc]; exact Nat.le_trans hmul hrhs
/-- **Uncovered Density Antitonicity:**
`uncoveredCount K₂ * 2 ^ K₁ ≤ uncoveredCount K₁ * 2 ^ K₂` for `K₁ ≤ K₂`. -/
theorem uncovered_density_antimono {K₁ K₂ : Nat} (h : K₁ ≤ K₂) :
    uncoveredCount K₂ * 2 ^ K₁ ≤ uncoveredCount K₁ * 2 ^ K₂ := by
  have hc1 := coveredCount_add_uncoveredCount K₁; have hc2 := coveredCount_add_uncoveredCount K₂
  have hm := covered_density_mono h
  have hs1 : coveredCount K₁ * 2 ^ K₂ + uncoveredCount K₁ * 2 ^ K₂ = 2 ^ K₁ * 2 ^ K₂ := by
    rw [← Nat.add_mul, hc1]
  have hs2 : coveredCount K₂ * 2 ^ K₁ + uncoveredCount K₂ * 2 ^ K₁ = 2 ^ K₁ * 2 ^ K₂ := by
    rw [← Nat.add_mul, hc2, Nat.mul_comm]
  omega
/-- Every covered residue `r < 2 ^ K` yields `HasFiniteStoppingTime (2 ^ K * q + r)` for
`2 ^ K * q + r ≥ 3 ^ K`. -/
theorem dropsWithin_covered_finiteStoppingTime {K r q : Nat}
    (hdrop : dropsWithin K r = true) (hr : r < 2 ^ K) (hn : 3 ^ K ≤ 2 ^ K * q + r) :
    HasFiniteStoppingTime (2 ^ K * q + r) :=
  dropsWithin_sound hdrop (by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]) hn

/-! ### 2. Fast Equivalence-Verified Sieves (`K = 10, 12`) & Small-`n` Bridge -/
/-- Fast incremental pure-`Nat` loop checking `3 ^ c < 2 ^ k` over `1 ≤ k ≤ rem`. -/
def fastDropsLoop (rem cur p3 p2 : Nat) : Bool :=
  match rem with
  | 0 => false
  | rem + 1 =>
    let p3' := if cur % 2 == 1 then 3 * p3 else p3; let p2' := 2 * p2
    if p3' < p2' then true else fastDropsLoop rem (terrasStep cur) p3' p2'
/-- Fast pure-`Nat` sieve equivalent to `ModularDescent.dropsWithin`. -/
def fastDropsWithin (K r : Nat) : Bool := fastDropsLoop K r 1 1
private theorem terrasParityVec_succ_right (j r : Nat) :
    terrasParityVec (j + 1) r = terrasParityVec j r ++ [(terrasIter j r % 2 == 1)] := by
  simpa [terrasParityVec] using terrasParityVec_add j 1 r
private theorem terras_step_state_eq (j r : Nat) :
    (if terrasIter j r % 2 == 1 then 3 * 3 ^ countOnes (terrasParityVec j r)
        else 3 ^ countOnes (terrasParityVec j r)) =
      3 ^ countOnes (terrasParityVec (j + 1) r) ∧
    2 * 2 ^ j = 2 ^ (j + 1) ∧ terrasStep (terrasIter j r) = terrasIter (j + 1) r := by
  have hcnt : countOnes (terrasParityVec (j + 1) r) =
      countOnes (terrasParityVec j r) + (if terrasIter j r % 2 == 1 then 1 else 0) := by
    rw [terrasParityVec_succ_right, countOnes_append]; simp [countOnes]
  refine ⟨?_, by rw [Nat.pow_succ, Nat.mul_comm], (terrasIter_succ_right j r).symm⟩
  rw [hcnt]; cases (terrasIter j r % 2 == 1) <;> simp [Nat.pow_succ, Nat.mul_comm]
private theorem fastDropsLoop_iff (rem j r : Nat) :
    fastDropsLoop rem (terrasIter j r) (3 ^ countOnes (terrasParityVec j r)) (2 ^ j) = true ↔
      ∃ k : Nat, j + 1 ≤ k ∧ k ≤ j + rem ∧ 3 ^ countOnes (terrasParityVec k r) < 2 ^ k := by
  induction rem generalizing j with
  | zero => simp only [fastDropsLoop, Bool.false_eq_true, false_iff, not_exists, not_and]; omega
  | succ rem ih =>
    obtain ⟨hp3, hp2, hstep⟩ := terras_step_state_eq j r
    dsimp only [fastDropsLoop]; rw [hp3, hp2, hstep]
    by_cases hlt : 3 ^ countOnes (terrasParityVec (j + 1) r) < 2 ^ (j + 1)
    · simp only [hlt, ↓reduceIte, true_iff]; exact ⟨j + 1, Nat.le_refl _, by omega, hlt⟩
    · simp only [hlt, ↓reduceIte, ih (j + 1)]; constructor
      · rintro ⟨k, hk1, hk2, hc⟩; exact ⟨k, by omega, by omega, hc⟩
      · rintro ⟨k, hk1, hk2, hc⟩; rcases Nat.eq_or_lt_of_le hk1 with rfl | hgt
        · exact absurd hc hlt
        · exact ⟨k, hgt, by omega, hc⟩
/-- Exact equivalence `fastDropsWithin K r = dropsWithin K r` for all `K, r : Nat`. -/
theorem fastDropsWithin_eq_dropsWithin (K r : Nat) : fastDropsWithin K r = dropsWithin K r := by
  apply Bool.eq_iff_iff.mpr; rw [fastDropsWithin]
  have hiff := fastDropsLoop_iff K 0 r
  simp only [terrasIter, terrasParityVec, countOnes, Nat.pow_zero, Nat.zero_add] at hiff
  rw [hiff, dropsWithin_iff]; constructor
  · rintro ⟨k, hk1, hk2, hlt⟩; refine ⟨k, hk1, by omega, ?_⟩
    simp [checkDropsAt, Nat.mod_lt _ (Nat.two_pow_pos k), terrasParityVec_mod_eq, hlt]
  · rintro ⟨k, hk1, hk2, hc⟩
    simp only [checkDropsAt, Bool.and_eq_true, decide_eq_true_eq, terrasParityVec_mod_eq] at hc
    exact ⟨k, hk1, by omega, hc.2⟩
/-- Fast strong loop checking `terrasIter k r + 3 ^ c < r + 2 ^ k` for `2 ^ K ≤ n`. -/
def fastDropsStrongLoop (rem r cur p3 p2 : Nat) : Bool :=
  match rem with
  | 0 => false
  | rem + 1 =>
    let p3' := if cur % 2 == 1 then 3 * p3 else p3; let p2' := 2 * p2
    let cur' := terrasStep cur
    if p3' < p2' && cur' + p3' < r + p2' then true else fastDropsStrongLoop rem r cur' p3' p2'
/-- Fast sharp-threshold sieve starting from step `0`. -/
def fastDropsStrongWithin (K r : Nat) : Bool := fastDropsStrongLoop K r r 1 1
private theorem fastDropsStrongLoop_spec (rem j r : Nat)
    (h : fastDropsStrongLoop rem r (terrasIter j r)
      (3 ^ countOnes (terrasParityVec j r)) (2 ^ j) = true) :
    ∃ k : Nat, 1 ≤ k ∧ k ≤ j + rem ∧ 3 ^ countOnes (terrasParityVec k r) < 2 ^ k ∧
      terrasIter k r + 3 ^ countOnes (terrasParityVec k r) < r + 2 ^ k := by
  induction rem generalizing j with
  | zero => simp [fastDropsStrongLoop] at h
  | succ rem ih =>
    obtain ⟨hp3, hp2, hstep⟩ := terras_step_state_eq j r
    dsimp only [fastDropsStrongLoop] at h; rw [hp3, hp2, hstep] at h
    split at h
    · rename_i hc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact ⟨j + 1, by omega, by omega, hc.1, hc.2⟩
    · rcases ih (j + 1) h with ⟨k, hk1, hk2, hp, hr⟩; exact ⟨k, hk1, by omega, hp, hr⟩
/-- Sharp `2 ^ K ≤ n` soundness for `fastDropsStrongWithin`. -/
theorem fastDropsStrongWithin_sound {K r n : Nat} (hstrong : fastDropsStrongWithin K r = true)
    (hmod : n % 2 ^ K = r) (hn : 2 ^ K ≤ n) : HasFiniteStoppingTime n := by
  rcases fastDropsStrongLoop_spec K 0 r hstrong with ⟨k, hk1, hkK, hpow, hrem⟩
  rw [Nat.zero_add] at hkK; have hq : 1 ≤ n / 2 ^ K := Nat.div_pos hn (Nat.two_pow_pos K)
  have hdecomp : n = r + 2 ^ k * (2 ^ (K - k) * (n / 2 ^ K)) := by
    have hpowK : 2 ^ K = 2 ^ k * 2 ^ (K - k) := by rw [← Nat.pow_add, Nat.add_sub_of_le hkK]
    have hd := (Nat.mod_add_div n (2 ^ K)).symm; rw [hmod] at hd
    conv at hd => rhs; rhs; lhs; rw [hpowK]
    rw [Nat.mul_assoc] at hd; exact hd
  let m := 2 ^ (K - k) * (n / 2 ^ K)
  have hm_ge : 1 ≤ m := Nat.mul_pos (Nat.two_pow_pos (K - k)) hq
  have hcong := (terrasParityVec_mod_two_pow k r m).2; rw [← hdecomp] at hcong
  have hmul : 3 ^ countOnes (terrasParityVec k r) * (m - 1) ≤ 2 ^ k * (m - 1) :=
    Nat.mul_le_mul_right (m - 1) (Nat.le_of_lt hpow)
  have hlt : terrasIter k n < n := by
    rw [hcong, hdecomp]
    change terrasIter k r + 3 ^ countOnes (terrasParityVec k r) * m < r + 2 ^ k * m
    rw [show m = 1 + (m - 1) by omega, Nat.mul_add, Nat.mul_one, Nat.mul_add, Nat.mul_one]; omega
  exact hasFiniteStoppingTime_of_terras_lt hk1 hlt
private theorem dropsWithin_sound_sharp_of_allPow2 {K r n : Nat}
    (hall : allPow2 (fun m => !fastDropsWithin K m || fastDropsStrongWithin K m) K 0 = true)
    (hdrop : dropsWithin K r = true) (hmod : n % 2 ^ K = r) (hn : 2 ^ K ≤ n) :
    HasFiniteStoppingTime n := by
  have hrlt : r < 2 ^ K := by rw [← hmod]; exact Nat.mod_lt n (Nat.two_pow_pos K)
  have himp := allPow2_sound _ K 0 hall r (Nat.zero_le r) (by simpa using hrlt)
  have hf : fastDropsWithin K r = true := (fastDropsWithin_eq_dropsWithin K r).trans hdrop
  simp only [Bool.or_eq_true, Bool.not_eq_true', hf] at himp
  rcases himp with hfalse | hstrong
  · exact absurd hfalse (by decide)
  · exact fastDropsStrongWithin_sound hstrong hmod hn
/-- **Mod-1024 (`K = 10`) Covered Density Certificate:** `960 / 1024` (`93.75%`). -/
theorem sieve_mod1024_covered : coveredCount 10 = 960 := by
  have h := countPow2_congr (p := dropsWithin 10) (q := fastDropsWithin 10) 10 0
    (fun r _ _ => (fastDropsWithin_eq_dropsWithin 10 r).symm)
  change countPow2 (dropsWithin 10) 10 0 = 960; rw [h]; decide
/-- **Mod-1024 Uncovered Certificate:** `64 / 1024` uncovered at `K = 10`. -/
theorem sieve_mod1024_uncovered : uncoveredCount 10 = 64 := by
  have := coveredCount_add_uncoveredCount 10; rw [sieve_mod1024_covered] at this; omega
/-- **Mod-4096 (`K = 12`) Covered Density Certificate:** `3870 / 4096` (`> 94.4%`). -/
theorem sieve_mod4096_covered : coveredCount 12 = 3870 := by
  have h := countPow2_congr (p := dropsWithin 12) (q := fastDropsWithin 12) 12 0
    (fun r _ _ => (fastDropsWithin_eq_dropsWithin 12 r).symm)
  change countPow2 (dropsWithin 12) 12 0 = 3870; rw [h]; decide
/-- **Mod-4096 Uncovered Certificate:** `226 / 4096` uncovered at `K = 12`. -/
theorem sieve_mod4096_uncovered : uncoveredCount 12 = 226 := by
  have := coveredCount_add_uncoveredCount 12; rw [sieve_mod4096_covered] at this; omega
/-- Exact rational density bounds for `K = 10` (`15 / 16`) and `K = 12` (`> 94.4%`). -/
theorem sieve_high_modulus_density_bounds :
    coveredCount 10 * 16 = 15 * 1024 ∧ coveredCount 12 * 1000 > 944 * 4096 := by
  rw [sieve_mod1024_covered, sieve_mod4096_covered]; decide
/-- Sharp `1024 ≤ n` soundness for `dropsWithin 10`. -/
theorem dropsWithin_sound_mod1024 {r n : Nat} (hdrop : dropsWithin 10 r = true)
    (hmod : n % 1024 = r) (hn : 1024 ≤ n) : HasFiniteStoppingTime n :=
  dropsWithin_sound_sharp_of_allPow2 (by decide) hdrop hmod hn
/-- Sharp `4096 ≤ n` soundness for `dropsWithin 12`. -/
theorem dropsWithin_sound_mod4096 {r n : Nat} (hdrop : dropsWithin 12 r = true)
    (hmod : n % 4096 = r) (hn : 4096 ≤ n) : HasFiniteStoppingTime n :=
  dropsWithin_sound_sharp_of_allPow2 (by decide) hdrop hmod hn
/-- Auxiliary loop testing `terrasIter` dropping below `target`. -/
def hasTerrasDropAux (target : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, cur =>
    let nxt := terrasStep cur
    if nxt < target then true else hasTerrasDropAux target fuel nxt
/-- Bounded pure-`Nat` Terras stopping-time checker for small integers `n`. -/
def hasTerrasDrop (fuel n : Nat) : Bool := hasTerrasDropAux n fuel n
private theorem hasTerrasDropAux_sound (fuel j n : Nat)
    (h : hasTerrasDropAux n fuel (terrasIter j n) = true) : HasFiniteStoppingTime n := by
  induction fuel generalizing j with
  | zero => simp [hasTerrasDropAux] at h
  | succ fuel ih =>
    dsimp only [hasTerrasDropAux] at h; rw [← terrasIter_succ_right j n] at h
    split at h
    · rename_i hlt; exact hasFiniteStoppingTime_of_terras_lt (Nat.succ_pos j) hlt
    · exact ih (j + 1) h
/-- Any `n` passing `hasTerrasDrop fuel n = true` has `HasFiniteStoppingTime n`. -/
theorem hasTerrasDrop_sound (fuel n : Nat) (h : hasTerrasDrop fuel n = true) :
    HasFiniteStoppingTime n := hasTerrasDropAux_sound fuel 0 n h
/-- **Small-`n` Completion (`2 ≤ n < 4096`):** every `2 ≤ n < 4096` drops in `≤ 82` steps. -/
theorem small_lt_4096_finiteStoppingTime {n : Nat} (hn2 : 2 ≤ n) (hn4096 : n < 4096) :
    HasFiniteStoppingTime n := by
  have hall : allPow2 (fun m => decide (m < 2) || hasTerrasDrop 82 m) 12 0 = true := by decide
  have hm := allPow2_sound _ 12 0 hall n (Nat.zero_le n) (by simpa using hn4096)
  simp only [Bool.or_eq_true, decide_eq_false (by omega : ¬ n < 2)] at hm
  rcases hm with hf | hok
  · exact absurd hf (by decide)
  · exact hasTerrasDrop_sound 82 n hok
/-- **Unconditional `mod 1024` Covered Descent:** every `n ≥ 2` covered mod `1024` drops. -/
theorem mod1024_covered_finiteStoppingTime {n : Nat} (hn : 2 ≤ n)
    (hdrop : dropsWithin 10 (n % 1024) = true) : HasFiniteStoppingTime n :=
  if hlt : n < 4096 then small_lt_4096_finiteStoppingTime hn hlt
  else dropsWithin_sound_mod1024 hdrop rfl (by omega)
/-- **Unconditional `mod 4096` Covered Descent:** every `n ≥ 2` covered mod `4096` drops. -/
theorem mod4096_covered_finiteStoppingTime {n : Nat} (hn : 2 ≤ n)
    (hdrop : dropsWithin 12 (n % 4096) = true) : HasFiniteStoppingTime n :=
  if hlt : n < 4096 then small_lt_4096_finiteStoppingTime hn hlt
  else dropsWithin_sound_mod4096 hdrop rfl (by omega)

/-! ### 3. Universal Incompleteness & Exponential Survival (`REF-002`) -/
private theorem countPow2_pos_of_witness {p : Nat → Bool} {d lo r : Nat}
    (hr1 : lo ≤ r) (hr2 : r < lo + 2 ^ d) (hp : p r = true) : 0 < countPow2 p d lo := by
  induction d generalizing lo with
  | zero => have heq : r = lo := by simp at hr2; omega
            subst heq; simp [countPow2, hp]
  | succ d ih =>
    have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
    rw [hpow] at hr2; simp only [countPow2]
    by_cases hmid : r < lo + 2 ^ d
    · have := ih hr1 hmid; omega
    · have := ih (Nat.le_of_not_lt hmid) (by omega); omega
/-- **Universal Incompleteness (`no_finite_modulus_complete_sieve`, `REF-002`):**
for every finite horizon `K ≥ 1`, `1 ≤ uncoveredCount K` and `coveredCount K < 2 ^ K`. -/
theorem no_finite_modulus_complete_sieve (K : Nat) (hK : 1 ≤ K) :
    1 ≤ uncoveredCount K ∧ coveredCount K < 2 ^ K := by
  have hkpos : 0 < 2 ^ K := Nat.two_pow_pos K
  have hmiss : (!dropsWithin K (2 ^ K - 1)) = true := by rw [sieve_misses_all_odd_class hK]; rfl
  have hpos := countPow2_pos_of_witness (p := fun r => !dropsWithin K r) (d := K) (lo := 0)
    (r := 2 ^ K - 1) (Nat.zero_le _) (by simpa using Nat.sub_lt hkpos (by decide)) hmiss
  have hpart := coveredCount_add_uncoveredCount K
  change 0 < uncoveredCount K at hpos; omega
/-- Constructive 1-step odd-extension lift of `r` from mod `2 ^ K` to mod `2 ^ (K + 1)`. -/
def liftUncoveredStep (K r : Nat) : Nat := if terrasIter K r % 2 = 1 then r else r + 2 ^ K
/-- `liftUncoveredStep K r < 2 ^ (K + 1)` whenever `r < 2 ^ K`. -/
theorem liftUncoveredStep_lt {K r : Nat} (hr : r < 2 ^ K) :
    liftUncoveredStep K r < 2 ^ (K + 1) := by
  have hpow : 2 ^ (K + 1) = 2 ^ K + 2 ^ K := by rw [Nat.pow_succ]; omega
  unfold liftUncoveredStep; split <;> omega
/-- `liftUncoveredStep K r ≡ r (mod 2 ^ K)` whenever `r < 2 ^ K`. -/
theorem liftUncoveredStep_mod {K r : Nat} (hr : r < 2 ^ K) :
    liftUncoveredStep K r % 2 ^ K = r := by
  unfold liftUncoveredStep; split
  · exact Nat.mod_eq_of_lt hr
  · simpa [Nat.mul_one] using (Nat.add_mul_mod_self_left r (2 ^ K) 1).trans (Nat.mod_eq_of_lt hr)
private theorem three_pow_mod_two (c : Nat) : 3 ^ c % 2 = 1 := by
  induction c with | zero => rfl | succ c ih => rw [Nat.pow_succ]; omega
/-- `terrasIter K (liftUncoveredStep K r)` is always odd. -/
theorem liftUncoveredStep_iter_odd (K r : Nat) :
    terrasIter K (liftUncoveredStep K r) % 2 = 1 := by
  unfold liftUncoveredStep; split
  · assumption
  · have hcong := (terrasParityVec_mod_two_pow K r 1).2; rw [Nat.mul_one] at hcong
    rw [hcong]; have h3 := three_pow_mod_two (countOnes (terrasParityVec K r)); omega
/-- Two-step all-odd lift plus third-step binary split into `[0, 2 ^ (K + 3))`. -/
def liftUncovered3 (K r : Nat) (b : Bool) : Nat :=
  let r2 := liftUncoveredStep (K + 1) (liftUncoveredStep K r)
  if b then r2 + 2 ^ (K + 2) else r2
private theorem pow_le_three_pow_of_uncovered {K r : Nat}
    (huncov : dropsWithin K r = false) : 2 ^ K ≤ 3 ^ countOnes (terrasParityVec K r) := by
  cases K with
  | zero => simp [terrasParityVec, countOnes]
  | succ K =>
    have hnot : checkDropsAt (K + 1) (r % 2 ^ (K + 1)) = false := by
      simp only [dropsWithin, Bool.or_eq_false_iff] at huncov; exact huncov.2
    by_cases hlt : 3 ^ countOnes (terrasParityVec (K + 1) r) < 2 ^ (K + 1)
    · exfalso; have hc : checkDropsAt (K + 1) (r % 2 ^ (K + 1)) = true := by
        simp [checkDropsAt, Nat.mod_lt r (Nat.two_pow_pos (K + 1)), terrasParityVec_mod_eq, hlt]
      rw [hc] at hnot; exact absurd hnot (by decide)
    · exact Nat.le_of_not_lt hlt
private theorem liftUncovered3_lt_mod {K r : Nat} (hr : r < 2 ^ K) (b : Bool) :
    liftUncovered3 K r b < 2 ^ (K + 3) ∧ liftUncovered3 K r b % 2 ^ K = r ∧
      liftUncovered3 K r b % 2 ^ (K + 2) = liftUncoveredStep (K + 1) (liftUncoveredStep K r) := by
  have hr1 := liftUncoveredStep_lt hr; have hr2 := liftUncoveredStep_lt hr1
  have hr2K : liftUncoveredStep (K + 1) (liftUncoveredStep K r) % 2 ^ K = r := by
    have hdvd : 2 ^ K ∣ 2 ^ (K + 1) := ⟨2, by rw [Nat.pow_succ]⟩
    rw [← Nat.mod_mod_of_dvd _ hdvd, liftUncoveredStep_mod hr1, liftUncoveredStep_mod hr]
  have hpow3 : 2 ^ (K + 3) = 2 ^ (K + 2) + 2 ^ (K + 2) := by rw [Nat.pow_succ]; omega
  have hpow2 : 2 ^ (K + 2) = 2 ^ K * 4 := by rw [Nat.pow_succ, Nat.pow_succ]; omega
  unfold liftUncovered3; cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact ⟨by omega, hr2K, Nat.mod_eq_of_lt hr2⟩
  · refine ⟨by omega, by rw [hpow2, Nat.add_mul_mod_self_left, hr2K], ?_⟩
    simpa [Nat.mul_one] using
      (Nat.add_mul_mod_self_left _ (2 ^ (K + 2)) 1).trans (Nat.mod_eq_of_lt hr2)
private theorem append_singleton_last_eq {u v : List Bool} {a b : Bool}
    (hlen : u.length = v.length) (h : u ++ [a] = v ++ [b]) : a = b := by
  induction u generalizing v with
  | nil => cases v with | nil => simpa using h | cons _ _ => simp at hlen
  | cons x xs ih => cases v with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      simp only [List.cons_append, List.cons.injEq] at h; exact ih hlen h.2
private theorem iter_mod_two_of_mod_eq {j x y : Nat}
    (hmod : x % 2 ^ (j + 1) = y % 2 ^ (j + 1)) (hy : terrasIter j y % 2 = 1) :
    terrasIter j x % 2 = 1 := by
  have hstep : terrasParityVec (j + 1) x = terrasParityVec (j + 1) y := by
    rw [← terrasParityVec_mod_eq (j + 1) x, hmod, terrasParityVec_mod_eq]
  rw [terrasParityVec_succ_right, terrasParityVec_succ_right] at hstep
  have heq := append_singleton_last_eq
    ((terrasParityVec_length j x).trans (terrasParityVec_length j y).symm) hstep
  exact beq_iff_eq.mp (heq.trans (beq_iff_eq.mpr hy))
/-- Uncovered survival for `liftUncovered3 K r b` at horizon `K + 3`. -/
theorem liftUncovered3_spec {K r : Nat} (hr : r < 2 ^ K) (huncov : dropsWithin K r = false)
    (b : Bool) :
    liftUncovered3 K r b < 2 ^ (K + 3) ∧ liftUncovered3 K r b % 2 ^ K = r ∧
      dropsWithin (K + 3) (liftUncovered3 K r b) = false := by
  let u := liftUncovered3 K r b
  obtain ⟨hlt, hmodK, hx_mod2⟩ := liftUncovered3_lt_mod hr b; refine ⟨hlt, hmodK, ?_⟩
  let r1 := liftUncoveredStep K r; let r2 := liftUncoveredStep (K + 1) r1
  have hr1_lt := liftUncoveredStep_lt hr; have hr2_lt := liftUncoveredStep_lt hr1_lt
  have hx_mod1 : u % 2 ^ (K + 1) = r1 := by
    have hdvd : 2 ^ (K + 1) ∣ 2 ^ (K + 2) := ⟨2, Nat.pow_succ _ _⟩
    rw [← Nat.mod_mod_of_dvd u hdvd, hx_mod2, liftUncoveredStep_mod hr1_lt]
  have hb1 := iter_mod_two_of_mod_eq (hx_mod1.trans (Nat.mod_eq_of_lt hr1_lt).symm)
    (liftUncoveredStep_iter_odd K r)
  have hb2 := iter_mod_two_of_mod_eq (hx_mod2.trans (Nat.mod_eq_of_lt hr2_lt).symm)
    (liftUncoveredStep_iter_odd (K + 1) r1)
  have hbase : 2 ^ K ≤ 3 ^ countOnes (terrasParityVec K u) := by
    rw [← terrasParityVec_mod_eq K, hmodK]; exact pow_le_three_pow_of_uncovered huncov
  have hc1 : countOnes (terrasParityVec (K + 1) u) = countOnes (terrasParityVec K u) + 1 := by
    rw [terrasParityVec_succ_right, countOnes_append, beq_iff_eq.mpr hb1]; simp [countOnes]
  have hc2 : countOnes (terrasParityVec (K + 2) u) = countOnes (terrasParityVec (K + 1) u) + 1 := by
    rw [terrasParityVec_succ_right, countOnes_append, beq_iff_eq.mpr hb2]; simp [countOnes]
  have hc3 : countOnes (terrasParityVec (K + 2) u) ≤ countOnes (terrasParityVec (K + 3) u) := by
    conv => rhs; rw [show K + 3 = (K + 2) + 1 from rfl,
      terrasParityVec_succ_right, countOnes_append]
    exact Nat.le_add_right _ _
  have hK0 : dropsWithin K u = false := by rw [← dropsWithin_mod_eq K, hmodK, huncov]
  have h31 : 2 ^ (K + 1) ≤ 3 ^ countOnes (terrasParityVec (K + 1) u) := by
    rw [hc1, Nat.pow_succ, Nat.pow_succ]; omega
  have h32 : 2 ^ (K + 2) ≤ 3 ^ countOnes (terrasParityVec (K + 2) u) := by
    rw [hc2, hc1, Nat.pow_succ 3, Nat.pow_succ 3, Nat.pow_succ 2, Nat.pow_succ 2]; omega
  have h33 : 2 ^ (K + 3) ≤ 3 ^ countOnes (terrasParityVec (K + 3) u) := by
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 3) hc3
    have : 2 ^ (K + 3) ≤ 3 ^ countOnes (terrasParityVec (K + 2) u) := by
      rw [hc2, hc1, Nat.pow_succ 3, Nat.pow_succ 3, Nat.pow_succ 2, Nat.pow_succ 2,
        Nat.pow_succ 2]
      omega
    omega
  simp [u, dropsWithin, checkDropsAt, terrasParityVec_mod_eq, hK0, h31, h32, h33]
private theorem nodup_map_inj {α β : Type} {f : α → β} {l : List α} (hl : l.Nodup)
    (hinj : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons, List.nodup_cons]; rw [List.nodup_cons] at hl
    refine ⟨fun hm => ?_, ih hl.2 (fun a ha b hb =>
      hinj a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb))⟩
    rcases List.mem_map.mp hm with ⟨y, hy, hxy⟩
    exact hl.1 ((hinj y (List.mem_cons_of_mem x hy) x List.mem_cons_self hxy) ▸ hy)
private theorem nodup_length_le_of_subset {α : Type} [BEq α] [LawfulBEq α] {l₁ l₂ : List α}
    (h1 : l₁.Nodup) (hsub : ∀ x ∈ l₁, x ∈ l₂) : l₁.length ≤ l₂.length := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at h1; have hx : x ∈ l₂ := hsub x List.mem_cons_self
    have hlen := ih h1.2 (fun y hy =>
      (List.mem_erase_of_ne (fun hxy => h1.1 (by subst hxy; exact hy))).mpr
        (hsub y (List.mem_cons_of_mem x hy)))
    have her : (l₂.erase x).length + 1 = l₂.length := by
      rw [List.length_erase_of_mem hx]; have := List.length_pos_of_mem hx; omega
    simp only [List.length_cons]; omega
private theorem countBelow_eq_filter_range (p : Nat → Bool) (n : Nat) :
    countBelow p n = ((List.range n).filter p).length := by
  induction n with | zero => rfl | succ n ih =>
    rw [countBelow, List.range_succ, List.filter_append, List.length_append, ih]
    cases hp : p n <;> simp [hp]
private theorem liftUncovered3_nodup_pair (K : Nat) :
    let lK := (List.range (2 ^ K)).filter (fun r => !dropsWithin K r)
    ((lK.map (liftUncovered3 K · false)) ++ (lK.map (liftUncovered3 K · true))).Nodup := by
  intro lK; have hlK_nd : lK.Nodup := List.nodup_range.filter _
  have hlK_lt : ∀ r ∈ lK, r < 2 ^ K := fun r hr => List.mem_range.mp (List.mem_filter.mp hr).1
  have hinj : ∀ b : Bool, ∀ r₁ ∈ lK, ∀ r₂ ∈ lK,
      liftUncovered3 K r₁ b = liftUncovered3 K r₂ b → r₁ = r₂ := fun b r₁ hr₁ r₂ hr₂ heq => by
    rw [← (liftUncovered3_lt_mod (hlK_lt r₁ hr₁) b).2.1,
      ← (liftUncovered3_lt_mod (hlK_lt r₂ hr₂) b).2.1, heq]
  refine List.nodup_append.mpr ⟨nodup_map_inj hlK_nd (hinj false),
    nodup_map_inj hlK_nd (hinj true), fun x hx y hy hxy => ?_⟩
  rcases List.mem_map.mp hx with ⟨r₁, hr₁, rfl⟩; rcases List.mem_map.mp hy with ⟨r₂, hr₂, rfl⟩
  have hm1 : liftUncovered3 K r₁ false < 2 ^ (K + 2) := by
    simpa [liftUncovered3] using liftUncoveredStep_lt (liftUncoveredStep_lt (hlK_lt r₁ hr₁))
  have hm2 : 2 ^ (K + 2) ≤ liftUncovered3 K r₂ true := by simp [liftUncovered3]
  omega
/-- **Exponential Uncovered Survival (`2 * u(K) ≤ u(K + 3)`):** every uncovered residue at
`K` generates at least two distinct uncovered descendants at `K + 3`. -/
theorem two_mul_uncoveredCount_le_add_three (K : Nat) :
    2 * uncoveredCount K ≤ uncoveredCount (K + 3) := by
  let lK := (List.range (2 ^ K)).filter (fun r => !dropsWithin K r)
  let lK3 := (List.range (2 ^ (K + 3))).filter (fun r => !dropsWithin (K + 3) r)
  have hsub : ∀ x ∈ (lK.map (liftUncovered3 K · false)) ++ (lK.map (liftUncovered3 K · true)),
      x ∈ lK3 := by
    intro x hx; simp only [lK3, List.mem_filter, List.mem_range, Bool.not_eq_true']
    rcases List.mem_append.mp hx with hxA | hxB <;>
      rcases List.mem_map.mp (by assumption) with ⟨r, hr, rfl⟩ <;>
      simp only [lK, List.mem_filter, List.mem_range, Bool.not_eq_true'] at hr
    · exact ⟨(liftUncovered3_spec hr.1 hr.2 false).1, (liftUncovered3_spec hr.1 hr.2 false).2.2⟩
    · exact ⟨(liftUncovered3_spec hr.1 hr.2 true).1, (liftUncovered3_spec hr.1 hr.2 true).2.2⟩
  have hlen := nodup_length_le_of_subset (liftUncovered3_nodup_pair K) hsub
  have huK : uncoveredCount K = lK.length := by
    rw [uncoveredCount_eq_countBelow, countBelow_eq_filter_range]
  have huK3 : uncoveredCount (K + 3) = lK3.length := by
    rw [uncoveredCount_eq_countBelow, countBelow_eq_filter_range]
  dsimp only [lK, lK3] at huK huK3
  rw [List.length_append, List.length_map, List.length_map, ← huK, ← huK3] at hlen; omega
/-- **Exponential Uncovered Lower Bound:** for every `m : Nat`,
`2 ^ m ≤ uncoveredCount (3 * m + 1)`. -/
theorem exp_uncoveredCount_lower_bound (m : Nat) : 2 ^ m ≤ uncoveredCount (3 * m + 1) := by
  induction m with
  | zero => exact (no_finite_modulus_complete_sieve 1 (by decide)).1
  | succ m ih =>
    have hstep := two_mul_uncoveredCount_le_add_three (3 * m + 1)
    rw [show 3 * m + 1 + 3 = 3 * (m + 1) + 1 by omega] at hstep
    rw [Nat.pow_succ, Nat.mul_comm]; omega

/-! ### 4. Projective `ℤ₂` Periodic Orbit Towers (`CORE-004`, Barrier 4) -/
/-- One compressed Terras step extended to `ℤ_(2) ⊂ ℤ₂` (`OddDenomRat`). -/
def OddDenomRat.terrasStep (a : OddDenomRat) : OddDenomRat :=
  if h : a.num % 2 = 0 then
    a.divTwoPow 1 (by simpa [Int.pow_one] using Int.dvd_of_emod_eq_zero h)
  else
    a.step3n1.divTwoPow 1 (by
      have hd : (a.den : Int) % 2 = 1 := by have := a.den_odd; omega
      have hn : a.step3n1.num % 2 = 0 := by simp [OddDenomRat.step3n1]; omega
      simpa [Int.pow_one] using Int.dvd_of_emod_eq_zero hn)
/-- Iterated `OddDenomRat.terrasStep` on `ℤ_(2)`. -/
def OddDenomRat.terrasIter : Nat → OddDenomRat → OddDenomRat
  | 0, a => a | k + 1, a => OddDenomRat.terrasIter k a.terrasStep
/-- Length-`k` `2`-adic Terras parity vector in `ℤ_(2)`. -/
def OddDenomRat.terrasParityVec : Nat → OddDenomRat → List Bool
  | 0, _ => [] | k + 1, a => (a.num % 2 != 0) :: OddDenomRat.terrasParityVec k a.terrasStep
/-- Exact congruence modulo `2 ^ k` on `ℤ_(2)`. -/
def OddDenomRat.ModEqTwoPow (k : Nat) (a b : OddDenomRat) : Prop :=
  (2 : Int) ^ k ∣ a.num * (b.den : Int) - b.num * (a.den : Int)
/-- `OddDenomRat.terrasStep` agrees with `SolveCollatz.terrasStep` on `ofNat n`. -/
theorem OddDenomRat.terrasStep_ofNat (n : Nat) :
    OddDenomRat.terrasStep (OddDenomRat.ofNat n) =
      OddDenomRat.ofNat (SolveCollatz.terrasStep n) := by
  unfold OddDenomRat.terrasStep SolveCollatz.terrasStep OddDenomRat.ofNat
  by_cases h : n % 2 = 0
  · rw [dite_eq_left (by omega : (n : Int) % 2 = 0), ite_eq_left h]
    exact OddDenomRat.ext (by simp [OddDenomRat.divTwoPow, Int.pow_one]) rfl
  · rw [dite_eq_right (by omega : ¬ (n : Int) % 2 = 0), ite_eq_right h]
    exact OddDenomRat.ext (by simp [OddDenomRat.divTwoPow, OddDenomRat.step3n1, Int.pow_one]) rfl
/-- `OddDenomRat.terrasParityVec` agrees with `SolveCollatz.terrasParityVec` on `ofNat n`. -/
theorem OddDenomRat.terrasParityVec_ofNat (k n : Nat) :
    OddDenomRat.terrasParityVec k (OddDenomRat.ofNat n) = SolveCollatz.terrasParityVec k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    simp only [OddDenomRat.terrasParityVec, SolveCollatz.terrasParityVec,
      OddDenomRat.terrasStep_ofNat, ih]
    congr 1; have hn : (n : Int) % 2 = ((n % 2 : Nat) : Int) := by omega
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [OddDenomRat.ofNat, hn, h]
/-- `ModEqTwoPow (k + 1) a b` implies equal parity and `ModEqTwoPow k` after `terrasStep`. -/
theorem OddDenomRat.terrasStep_modTwoPow {k : Nat} {a b : OddDenomRat}
    (h : OddDenomRat.ModEqTwoPow (k + 1) a b) :
    (a.num % 2 = 0 ↔ b.num % 2 = 0) ∧ OddDenomRat.ModEqTwoPow k a.terrasStep b.terrasStep := by
  rcases h with ⟨m, hm⟩; have had : (a.den : Int) % 2 = 1 := by have := a.den_odd; omega
  have hbd : (b.den : Int) % 2 = 1 := by have := b.den_odd; omega
  rw [show (2 : Int) ^ (k + 1) = 2 * (2 : Int) ^ k by rw [Int.pow_succ, Int.mul_comm],
    Int.mul_assoc] at hm
  have hpar : a.num % 2 = 0 ↔ b.num % 2 = 0 := by
    have hm2 : (a.num * (b.den : Int) - b.num * (a.den : Int)) % 2 = 0 := by omega
    rw [Int.sub_emod, Int.mul_emod a.num, Int.mul_emod b.num, had, hbd] at hm2; omega
  refine ⟨hpar, ?_⟩
  by_cases ha : a.num % 2 = 0
  · have hb := hpar.mp ha; refine ⟨m, ?_⟩
    simp only [OddDenomRat.terrasStep, dite_eq_left ha, dite_eq_left hb,
      OddDenomRat.divTwoPow, Int.pow_one]
    have ha2 : 2 * (a.num / 2) = a.num := by omega
    have hb2 : 2 * (b.num / 2) = b.num := by omega
    apply Int.eq_of_mul_eq_mul_left (by decide : (2 : Int) ≠ 0)
    rw [Int.mul_sub, ← Int.mul_assoc, ← Int.mul_assoc, ha2, hb2, hm]
  · have hb : ¬ b.num % 2 = 0 := fun h0 => ha (hpar.mpr h0); refine ⟨3 * m, ?_⟩
    simp only [OddDenomRat.terrasStep, dite_eq_right ha, dite_eq_right hb,
      OddDenomRat.divTwoPow, OddDenomRat.step3n1, Int.pow_one]
    have ha2 : 2 * ((3 * a.num + (a.den : Int)) / 2) = 3 * a.num + (a.den : Int) := by omega
    have hb2 : 2 * ((3 * b.num + (b.den : Int)) / 2) = 3 * b.num + (b.den : Int) := by omega
    have h3 : 3 * (a.num * (b.den : Int) - b.num * (a.den : Int)) =
        (3 * a.num + (a.den : Int)) * (b.den : Int) -
          (3 * b.num + (b.den : Int)) * (a.den : Int) := by
      rw [Int.add_mul, Int.add_mul, Int.mul_comm (a.den : Int) (b.den : Int),
        Int.add_sub_add_right, Int.mul_sub, Int.mul_assoc, Int.mul_assoc]
    apply Int.eq_of_mul_eq_mul_left (by decide : (2 : Int) ≠ 0)
    rw [Int.mul_sub, ← Int.mul_assoc, ← Int.mul_assoc, ha2, hb2, ← h3, hm]
    rw [Int.mul_left_comm 3 2, Int.mul_left_comm 3 ((2 : Int) ^ k) m]
/-- `ModEqTwoPow k a b` implies identical length-`k` `terrasParityVec` in `ℤ_(2)`. -/
theorem OddDenomRat.terrasParityVec_congr_modTwoPow {k : Nat} {a b : OddDenomRat}
    (h : OddDenomRat.ModEqTwoPow k a b) :
    OddDenomRat.terrasParityVec k a = OddDenomRat.terrasParityVec k b := by
  induction k generalizing a b with
  | zero => rfl
  | succ k ih =>
    obtain ⟨hpar, hstep⟩ := OddDenomRat.terrasStep_modTwoPow h
    simp only [OddDenomRat.terrasParityVec, List.cons.injEq]; refine ⟨?_, ih hstep⟩
    by_cases ha : a.num % 2 = 0
    · simp [ha, hpar.mp ha]
    · have hb : b.num % 2 ≠ 0 := fun h0 => ha (hpar.mpr h0)
      exact Bool.eq_iff_iff.mpr (by simp [ha, hb])
/-- Constructive Hensel-lifted inverse of any odd `d` modulo `2 ^ k`. -/
def invOddModTwoPow (d : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, y =>
    let x₀ := invOddModTwoPow d k y
    if (d * x₀) % 2 ^ (k + 1) = y % 2 ^ (k + 1) then x₀ else x₀ + 2 ^ k
private theorem mod_two_pow_succ_cases (z k : Nat) :
    z % 2 ^ (k + 1) = z % 2 ^ k ∨ z % 2 ^ (k + 1) = z % 2 ^ k + 2 ^ k := by
  have hkpos := Nat.two_pow_pos k; have hz := (Nat.mod_add_div z (2 ^ k)).symm
  have hz2 := (Nat.mod_add_div (z / 2 ^ k) 2).symm; have hlt := Nat.mod_lt z hkpos
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [hpow]
  rcases Nat.mod_two_eq_zero_or_one (z / 2 ^ k) with h0 | h1
  · left; have : z = z % 2 ^ k + (2 * 2 ^ k) * (z / 2 ^ k / 2) := by
      conv => lhs; rw [hz, hz2, h0, Nat.zero_add, Nat.mul_left_comm (2 ^ k) 2, ← Nat.mul_assoc]
    conv => lhs; rw [this]; rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  · right; have : z = (z % 2 ^ k + 2 ^ k) + (2 * 2 ^ k) * (z / 2 ^ k / 2) := by
      conv => lhs; rw [hz, hz2, h1, Nat.mul_add, Nat.mul_one, Nat.mul_left_comm (2 ^ k) 2,
        ← Nat.mul_assoc, ← Nat.add_assoc]
    conv => lhs; rw [this]; rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
private theorem add_two_pow_mod_succ {u y k : Nat}
    (h1 : u % 2 ^ k = y % 2 ^ k) (h2 : u % 2 ^ (k + 1) ≠ y % 2 ^ (k + 1)) :
    (u + 2 ^ k) % 2 ^ (k + 1) = y % 2 ^ (k + 1) := by
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
  have hkpos := Nat.two_pow_pos k; have hlt := Nat.mod_lt u hkpos
  have hklt : 2 ^ k < 2 ^ (k + 1) := by rw [hpow]; omega
  rw [Nat.add_mod, Nat.mod_eq_of_lt hklt]
  rcases mod_two_pow_succ_cases u k with hu | hu <;>
    rcases mod_two_pow_succ_cases y k with hy | hy
  · exact absurd (by omega) h2
  · rw [hu, hy, ← h1, Nat.mod_eq_of_lt (by rw [hpow]; omega)]
  · rw [hu, hy, ← h1]; simp only [Nat.add_assoc]
    rw [show 2 ^ k + 2 ^ k = 2 ^ (k + 1) * 1 by rw [hpow]; omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (Nat.lt_trans hlt hklt)]
  · exact absurd (by omega) h2
/-- Correctness of `invOddModTwoPow` for any odd `d`. -/
theorem invOddModTwoPow_spec {d : Nat} (hd : d % 2 = 1) (k y : Nat) :
    invOddModTwoPow d k y < 2 ^ k ∧ (d * invOddModTwoPow d k y) % 2 ^ k = y % 2 ^ k := by
  induction k with
  | zero => simp [invOddModTwoPow, Nat.mod_one]
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    simp only [invOddModTwoPow]
    by_cases hm : (d * invOddModTwoPow d k y) % 2 ^ (k + 1) = y % 2 ^ (k + 1)
    · rw [ite_eq_left hm]; exact ⟨Nat.lt_of_lt_of_le ih.1 (by rw [hpow]; omega), hm⟩
    · rw [ite_eq_right hm]; refine ⟨by rw [hpow]; omega, ?_⟩
      have hd2 : d = 1 + 2 * (d / 2) := by omega
      have hmul : d * (invOddModTwoPow d k y + 2 ^ k) =
          (d * invOddModTwoPow d k y + 2 ^ k) + 2 ^ (k + 1) * (d / 2) := by
        rw [Nat.mul_add, show d * 2 ^ k = 2 ^ k + 2 ^ (k + 1) * (d / 2) by
          conv => lhs; rw [hd2, Nat.add_mul, Nat.one_mul, Nat.mul_right_comm, ← hpow]]
        omega
      rw [hmul, Nat.add_mul_mod_self_left]; exact add_two_pow_mod_succ ih.2 hm

/-- Canonical residue of `a ∈ ℤ_(2)` modulo `2 ^ K`. -/
def OddDenomRat.residueModTwoPow (K : Nat) (a : OddDenomRat) : Nat :=
  ((a.num % ((2 ^ K : Nat) : Int)).toNat * invOddModTwoPow a.den K 1) % 2 ^ K
/-- `a.residueModTwoPow K < 2 ^ K`. -/
theorem OddDenomRat.residueModTwoPow_lt (K : Nat) (a : OddDenomRat) :
    a.residueModTwoPow K < 2 ^ K := Nat.mod_lt _ (Nat.two_pow_pos K)
/-- `OddDenomRat.ofNat (a.residueModTwoPow K)` is congruent to `a` modulo `2 ^ K`. -/
theorem OddDenomRat.modEqTwoPow_residueModTwoPow (K : Nat) (a : OddDenomRat) :
    OddDenomRat.ModEqTwoPow K (OddDenomRat.ofNat (a.residueModTwoPow K)) a := by
  cases K with
  | zero => simp [OddDenomRat.ModEqTwoPow]
  | succ K' =>
    let K := K' + 1; let M : Nat := 2 ^ K; have h1M : 1 < M := Nat.one_lt_two_pow (by omega)
    let nMod := (a.num % (M : Int)).toNat; let inv := invOddModTwoPow a.den K 1
    have hnMod : (nMod : Int) = a.num % (M : Int) :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
    have hinv : ((a.den * inv : Nat) : Int) % (M : Int) = 1 := by
      have h := congrArg (fun x : Nat => (x : Int)) (invOddModTwoPow_spec a.den_odd K 1).2
      rw [Nat.mod_eq_of_lt h1M] at h; rw [← Int.natCast_emod]; exact h
    have hmod : (((a.residueModTwoPow K : Nat) : Int) * (a.den : Int) -
        a.num * ((OddDenomRat.ofNat (a.residueModTwoPow K)).den : Int)) % (M : Int) = 0 := by
      simp only [OddDenomRat.ofNat, Int.natCast_one, Int.mul_one]
      have hr : ((a.residueModTwoPow K : Nat) : Int) % (M : Int) =
          ((nMod : Int) * (inv : Int)) % (M : Int) := by
        change (((nMod * inv) % M : Nat) : Int) % (M : Int) = _
        rw [Int.natCast_emod, Int.emod_emod_of_dvd _ (Int.dvd_refl _), Int.natCast_mul]
      rw [Int.sub_emod, Int.mul_emod (a.residueModTwoPow K : Int), hr, ← Int.mul_emod,
        Int.mul_assoc (nMod : Int), Int.mul_comm (inv : Int), ← Int.natCast_mul,
        Int.mul_emod (nMod : Int), hinv, Int.mul_one, Int.emod_emod_of_dvd _ (Int.dvd_refl _),
        hnMod, Int.emod_emod_of_dvd _ (Int.dvd_refl _), Int.sub_self, Int.zero_emod]
    exact Int.dvd_of_emod_eq_zero hmod
/-- Projective tower compatibility: `a.residueModTwoPow (K + 1) % 2 ^ K = a.residueModTwoPow K`. -/
theorem OddDenomRat.residueModTwoPow_proj (K : Nat) (a : OddDenomRat) :
    a.residueModTwoPow (K + 1) % 2 ^ K = a.residueModTwoPow K := by
  have hkpos : 0 < 2 ^ K := Nat.two_pow_pos K
  have hinv : invOddModTwoPow a.den (K + 1) 1 % 2 ^ K = invOddModTwoPow a.den K 1 := by
    dsimp only [invOddModTwoPow]; have hlt := (invOddModTwoPow_spec a.den_odd K 1).1
    split
    · exact Nat.mod_eq_of_lt hlt
    · rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
  have hkI : (0 : Int) < ((2 ^ K : Nat) : Int) := Int.natCast_pos.mpr hkpos
  have hn0 : 0 ≤ a.num % ((2 ^ K : Nat) : Int) := Int.emod_nonneg _ (Int.ne_of_gt hkI)
  have hnum : (a.num % ((2 ^ (K + 1) : Nat) : Int)).toNat % 2 ^ K =
      (a.num % ((2 ^ K : Nat) : Int)).toNat := by
    have hn1 : 0 ≤ a.num % ((2 ^ (K + 1) : Nat) : Int) :=
      Int.emod_nonneg _ (Int.ne_of_gt (Int.natCast_pos.mpr (Nat.two_pow_pos (K + 1))))
    have heq : (a.num % ((2 ^ (K + 1) : Nat) : Int)) % ((2 ^ K : Nat) : Int) =
        a.num % ((2 ^ K : Nat) : Int) := by
      rw [show ((2 ^ (K + 1) : Nat) : Int) = ((2 ^ K : Nat) : Int) * 2 by
        rw [Nat.pow_succ, Int.natCast_mul]; rfl]
      exact Int.emod_emod_of_dvd _ ⟨2, rfl⟩
    apply Int.ofNat.inj
    change (((a.num % ((2 ^ (K + 1) : Nat) : Int)).toNat % 2 ^ K : Nat) : Int) =
      ((a.num % ((2 ^ K : Nat) : Int)).toNat : Int)
    rw [Int.natCast_emod, Int.toNat_of_nonneg hn1, Int.toNat_of_nonneg hn0, heq]
  unfold OddDenomRat.residueModTwoPow
  rw [Nat.mod_mod_of_dvd _ ⟨2, by rw [Nat.pow_succ]⟩, Nat.mul_mod, hnum, hinv]
/-- **General Projective `ℤ₂` Obstruction Theorem (`Barrier 4`):** any `a : OddDenomRat` whose
`terrasParityVec` prefixes never contract generates an infinite projective tower of uncovered
residues (`dropsWithin K (a.residueModTwoPow K) = false`). -/
theorem twoAdic_tower_uncovered {a : OddDenomRat}
    (hnon : ∀ j : Nat, 1 ≤ j → 2 ^ j ≤ 3 ^ countOnes (OddDenomRat.terrasParityVec j a))
    (K : Nat) (_hK : 1 ≤ K) :
    a.residueModTwoPow K < 2 ^ K ∧
      OddDenomRat.ModEqTwoPow K (OddDenomRat.ofNat (a.residueModTwoPow K)) a ∧
      a.residueModTwoPow (K + 1) % 2 ^ K = a.residueModTwoPow K ∧
      dropsWithin K (a.residueModTwoPow K) = false := by
  refine ⟨a.residueModTwoPow_lt K, a.modEqTwoPow_residueModTwoPow K, a.residueModTwoPow_proj K, ?_⟩
  cases hdrop : dropsWithin K (a.residueModTwoPow K)
  · rfl
  · exfalso; rcases (dropsWithin_iff K (a.residueModTwoPow K)).mp hdrop with ⟨k, hk1, hkK, hc⟩
    simp only [checkDropsAt, Bool.and_eq_true, decide_eq_true_eq, terrasParityVec_mod_eq] at hc
    have hmod_k : OddDenomRat.ModEqTwoPow k (OddDenomRat.ofNat (a.residueModTwoPow K)) a := by
      rcases a.modEqTwoPow_residueModTwoPow K with ⟨m, hm⟩
      rcases (⟨(2 : Int) ^ (K - k), by rw [← Int.pow_add, Nat.add_sub_of_le hkK]⟩ :
        (2 : Int) ^ k ∣ (2 : Int) ^ K) with ⟨t, ht⟩
      exact ⟨t * m, by rw [hm, ht, Int.mul_assoc]⟩
    have hvec := OddDenomRat.terrasParityVec_congr_modTwoPow hmod_k
    rw [OddDenomRat.terrasParityVec_ofNat] at hvec
    have hge := hnon k hk1; rw [← hvec] at hge; omega
private theorem oddDenom_terrasIter_add (k m : Nat) (a : OddDenomRat) :
    OddDenomRat.terrasIter m (OddDenomRat.terrasIter k a) = OddDenomRat.terrasIter (k + m) a := by
  induction k generalizing a with
  | zero => simp [OddDenomRat.terrasIter]
  | succ k ih => simp only [OddDenomRat.terrasIter, Nat.succ_add]; exact ih a.terrasStep
private theorem oddDenom_terrasParityVec_add (k m : Nat) (a : OddDenomRat) :
    OddDenomRat.terrasParityVec (k + m) a = OddDenomRat.terrasParityVec k a ++
        OddDenomRat.terrasParityVec m (OddDenomRat.terrasIter k a) := by
  induction k generalizing a with
  | zero => simp [OddDenomRat.terrasParityVec, OddDenomRat.terrasIter]
  | succ k ih =>
    simp only [Nat.succ_add, OddDenomRat.terrasParityVec, OddDenomRat.terrasIter, List.cons_append]
    rw [ih a.terrasStep]
private theorem periodic_terras_noncontracting {a : OddDenomRat} {P : Nat} (hP : 0 < P)
    (hcyc : OddDenomRat.terrasIter P a = a)
    (hfull : 2 ^ P ≤ 3 ^ countOnes (OddDenomRat.terrasParityVec P a))
    (hrem : ∀ r : Nat, r < P → 2 ^ r ≤ 3 ^ countOnes (OddDenomRat.terrasParityVec r a))
    (j : Nat) : 2 ^ j ≤ 3 ^ countOnes (OddDenomRat.terrasParityVec j a) := by
  have hdiv := (Nat.div_add_mod j P).symm
  let q := j / P; let r := j % P; have hr : r < P := Nat.mod_lt j hP
  have hit : ∀ m : Nat, OddDenomRat.terrasIter (P * m) a = a := fun m => by
    induction m with
    | zero => rfl
    | succ m ih => rw [Nat.mul_succ, ← oddDenom_terrasIter_add, ih, hcyc]
  have hcnt : ∀ m : Nat, countOnes (OddDenomRat.terrasParityVec (P * m) a) =
      m * countOnes (OddDenomRat.terrasParityVec P a) := fun m => by
    induction m with
    | zero => simp [OddDenomRat.terrasParityVec, countOnes]
    | succ m ih =>
      rw [Nat.mul_succ, oddDenom_terrasParityVec_add, hit, countOnes_append, ih, Nat.succ_mul]
  conv => lhs; rw [hdiv]
  conv => rhs; rw [hdiv]
  rw [oddDenom_terrasParityVec_add, countOnes_append, hit, hcnt,
    Nat.pow_add, Nat.pow_add, Nat.pow_mul, Nat.mul_comm q _, Nat.pow_mul]
  exact Nat.mul_le_mul (Nat.pow_le_pow_left hfull q) (hrem r hr)
/-- **Barrier 4 Witness (`-5 ∈ ℤ_(2)`):** `periodicPoint [1, 2] = -5` generates an infinite
projective tower of uncovered residues (`dropsWithin K (x.residueModTwoPow K) = false`). -/
theorem twoAdic_neg5_tower_uncovered (K : Nat) (hK : 1 ≤ K) :
    let x := periodicPoint [1, 2] (by decide)
    dropsWithin K (x.residueModTwoPow K) = false ∧
      x.residueModTwoPow (K + 1) % 2 ^ K = x.residueModTwoPow K := by
  intro x; have hx : x = OddDenomRat.ofInt (-5) := twoAdic_cycle_neg5.1
  have hcyc : OddDenomRat.terrasIter 3 x = x := by rw [hx]; decide
  have hfull : 2 ^ 3 ≤ 3 ^ countOnes (OddDenomRat.terrasParityVec 3 x) := by rw [hx]; decide
  have hrem : ∀ r : Nat, r < 3 → 2 ^ r ≤ 3 ^ countOnes (OddDenomRat.terrasParityVec r x) := by
    intro r hr; rw [hx]; match r, hr with | 0, _ => decide | 1, _ => decide | 2, _ => decide
  have ht := twoAdic_tower_uncovered
    (fun j _ => periodic_terras_noncontracting (by decide) hcyc hfull hrem j) K hK
  exact ⟨ht.2.2.2, ht.2.2.1⟩
/-- **Barrier 4 Witness (`-19 / 11 ∈ ℤ_(2) \ ℤ`):** `periodicPoint [1, 1, 2] = -19 / 11`
generates an infinite projective tower of uncovered residues for every `K ≥ 1`. -/
theorem twoAdic_neg19_over_11_tower_uncovered (K : Nat) (hK : 1 ≤ K) :
    let x := periodicPoint [1, 1, 2] (by decide)
    dropsWithin K (x.residueModTwoPow K) = false ∧
      x.residueModTwoPow (K + 1) % 2 ^ K = x.residueModTwoPow K := by
  intro x; have hx : x = ⟨-19, 11, by decide⟩ := twoAdic_cycle_neg19_over_11.1
  have hcyc : OddDenomRat.terrasIter 4 x = x := by rw [hx]; decide
  have hfull : 2 ^ 4 ≤ 3 ^ countOnes (OddDenomRat.terrasParityVec 4 x) := by rw [hx]; decide
  have hrem : ∀ r : Nat, r < 4 → 2 ^ r ≤ 3 ^ countOnes (OddDenomRat.terrasParityVec r x) := by
    intro r hr; rw [hx]
    match r, hr with | 0, _ => decide | 1, _ => decide | 2, _ => decide | 3, _ => decide
  have ht := twoAdic_tower_uncovered
    (fun j _ => periodic_terras_noncontracting (by decide) hcyc hfull hrem j) K hK
  exact ⟨ht.2.2.2, ht.2.2.1⟩

/-! ### 5. Barrier 2 (`5n + 1`) Quantitative Contrast -/
/-- Compressed `5n + 1` step: `n / 2` if even, `(5 * n + 1) / 2` if odd. -/
def fiveStep (n : Nat) : Nat := if n % 2 = 0 then n / 2 else (5 * n + 1) / 2
/-- Length-`k` `5n + 1` parity vector. -/
def fiveParityVec : Nat → Nat → List Bool
  | 0, _ => [] | k + 1, n => (n % 2 == 1) :: fiveParityVec k (fiveStep n)
/-- Bad-residue indicator for `5n + 1`: `2 ^ k ≤ 5 ^ countOnes (fiveParityVec k r)`. -/
def fiveBadResidue (k r : Nat) : Bool := decide (2 ^ k ≤ 5 ^ countOnes (fiveParityVec k r))
/-- Number of residues `r < 2 ^ k` failing single-horizon `5n + 1` contraction. -/
def fiveBadCount (k : Nat) : Nat := countLt (fiveBadResidue k) (2 ^ k)
/-- Fast `5n + 1` cumulative sieve loop checking `5 ^ c < 2 ^ k` over `1 ≤ k ≤ rem`. -/
def fiveDropsLoop (rem cur p5 p2 : Nat) : Bool :=
  match rem with
  | 0 => false
  | rem + 1 =>
    let p5' := if cur % 2 == 1 then 5 * p5 else p5; let p2' := 2 * p2
    if p5' < p2' then true else fiveDropsLoop rem (fiveStep cur) p5' p2'
/-- Covered count of the cumulative `5n + 1` sieve at horizon `K`. -/
def fiveCoveredCount (K : Nat) : Nat := countPow2 (fun r => fiveDropsLoop K r 1 1) K 0
private theorem fiveParityVec_mod_two_pow (k n q : Nat) :
    fiveParityVec k (n + 2 ^ k * q) = fiveParityVec k n := by
  induction k generalizing n q with
  | zero => rfl
  | succ k ih =>
    have hm : 2 ^ (k + 1) * q = 2 * (2 ^ k * q) := by
      rw [Nat.pow_succ, Nat.mul_comm _ 2, Nat.mul_assoc]
    have hmod : (n + 2 ^ (k + 1) * q) % 2 = n % 2 := by rw [hm, Nat.add_mul_mod_self_left]
    simp only [fiveParityVec, hmod]; congr 1
    by_cases he : n % 2 = 0
    · have he' : (n + 2 ^ (k + 1) * q) % 2 = 0 := hmod.trans he
      have hst : fiveStep (n + 2 ^ (k + 1) * q) = fiveStep n + 2 ^ k * q := by
        simp only [fiveStep]; rw [ite_eq_left he', ite_eq_left he, hm]
        exact Nat.add_mul_div_left n (2 ^ k * q) (by decide : 0 < 2)
      rw [hst, ih]
    · have hst : fiveStep (n + 2 ^ (k + 1) * q) = fiveStep n + 2 ^ k * (5 * q) := by
        simp only [fiveStep]; rw [ite_eq_right (fun h => he (hmod.symm.trans h)), ite_eq_right he]
        have hnum : 5 * (n + 2 ^ (k + 1) * q) + 1 = (5 * n + 1) + 2 * (2 ^ k * (5 * q)) := by
          rw [hm, Nat.mul_add, Nat.mul_left_comm 5 2, Nat.mul_left_comm 5 (2 ^ k)]; omega
        rw [hnum]; exact Nat.add_mul_div_left (5 * n + 1) (2 ^ k * (5 * q)) (by decide : 0 < 2)
      rw [hst, ih]
private theorem fiveParityVec_mod_eq (k n : Nat) :
    fiveParityVec k (n % 2 ^ k) = fiveParityVec k n := by
  have h := fiveParityVec_mod_two_pow k (n % 2 ^ k) (n / 2 ^ k)
  rw [Nat.mod_add_div] at h; exact h.symm
/-- Constructive residue witness `< 2 ^ v.length` realizing `5n + 1` parity vector `v`. -/
def fiveVecWitness : List Bool → Nat
  | [] => 0
  | b :: bs =>
    let r' := fiveVecWitness bs
    if b then 2 * invOddModTwoPow 5 bs.length (r' + (3 * 2 ^ bs.length - 3)) + 1 else 2 * r'
/-- Correctness of `fiveVecWitness`: `< 2 ^ v.length` and `fiveParityVec v.length _ = v`. -/
theorem fiveVecWitness_spec (v : List Bool) :
    fiveVecWitness v < 2 ^ v.length ∧ fiveParityVec v.length (fiveVecWitness v) = v := by
  induction v with
  | nil => simp [fiveVecWitness, fiveParityVec]
  | cons b bs ih =>
    have hpow : 2 ^ (bs.length + 1) = 2 * 2 ^ bs.length := by rw [Nat.pow_succ, Nat.mul_comm]
    cases b
    · simp only [fiveVecWitness, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      have he : (2 * fiveVecWitness bs) % 2 = 0 := Nat.mul_mod_right _ _
      have hst : fiveStep (2 * fiveVecWitness bs) = fiveVecWitness bs := by simp [fiveStep, he]
      refine ⟨by rw [hpow]; omega, by simp [fiveParityVec, hst, ih.2]⟩
    · simp only [fiveVecWitness, ↓reduceIte, List.length_cons]
      let x := invOddModTwoPow 5 bs.length (fiveVecWitness bs + (3 * 2 ^ bs.length - 3))
      have hinv := invOddModTwoPow_spec (d := 5) (by decide) bs.length
        (fiveVecWitness bs + (3 * 2 ^ bs.length - 3))
      have hodd : (2 * x + 1) % 2 = 1 := by omega
      have hst : fiveStep (2 * x + 1) = 5 * x + 3 := by
        unfold fiveStep; rw [ite_eq_right (by omega : (2 * x + 1) % 2 ≠ 0)]; omega
      have hmod : (5 * x + 3) % 2 ^ bs.length = fiveVecWitness bs := by
        change (5 * invOddModTwoPow 5 bs.length
          (fiveVecWitness bs + (3 * 2 ^ bs.length - 3)) + 3) % 2 ^ bs.length = fiveVecWitness bs
        rw [Nat.add_mod, hinv.2, ← Nat.add_mod]
        cases hm : bs.length with
        | zero =>
          have : fiveVecWitness bs = 0 := by have := ih.1; rw [hm, Nat.pow_zero] at this; omega
          simp [this]
        | succ m =>
          have : 3 ≤ 3 * 2 ^ (m + 1) := by have := Nat.two_pow_pos (m + 1); omega
          have hltm : fiveVecWitness bs < 2 ^ (m + 1) := by rw [← hm]; exact ih.1
          rw [show fiveVecWitness bs + (3 * 2 ^ (m + 1) - 3) + 3 =
            fiveVecWitness bs + 2 ^ (m + 1) * 3 by omega,
            Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hltm]
      refine ⟨by change 2 * x + 1 < 2 ^ (bs.length + 1); rw [hpow]; omega, ?_⟩
      change ((2 * x + 1) % 2 == 1) :: fiveParityVec bs.length (fiveStep (2 * x + 1)) = true :: bs
      rw [beq_iff_eq.mpr hodd, hst, ← fiveParityVec_mod_eq bs.length (5 * x + 3), hmod, ih.2]
private def flipBits (v : List Bool) : List Bool := v.map (!·)
private theorem countOnes_flipBits (v : List Bool) :
    countOnes v + countOnes (flipBits v) = v.length := by
  induction v with
  | nil => rfl | cons b bs ih => cases b <;> simp [flipBits, countOnes] at ih ⊢ <;> omega
private theorem filter_split_length {α : Type} (p : α → Bool) (l : List α) :
    (l.filter p).length + (l.filter (fun x => !p x)).length = l.length := by
  induction l with
  | nil => rfl | cons x xs ih => cases hp : p x <;> simp [List.filter, hp] <;> omega
private theorem flipBits_inj {v₁ v₂ : List Bool} (h : flipBits v₁ = flipBits v₂) : v₁ = v₂ := by
  have hinv : ∀ v : List Bool, flipBits (flipBits v) = v := fun v => by
    induction v with | nil => rfl | cons b bs ih =>
      change (!!b) :: flipBits (flipBits bs) = b :: bs; rw [Bool.not_not, ih]
  rw [← hinv v₁, ← hinv v₂, h]
private theorem highOnes_le_fiveBadCount (m : Nat) :
    ((allBitVecs (2 * m)).filter (fun v => decide (m ≤ countOnes v))).length ≤
      fiveBadCount (2 * m) := by
  let k := 2 * m; let lHigh := (allBitVecs k).filter (fun v => decide (m ≤ countOnes v))
  let lBad := (List.range (2 ^ k)).filter (fiveBadResidue k)
  have hsub : ∀ r ∈ lHigh.map fiveVecWitness, r ∈ lBad := by
    intro r hr; rcases List.mem_map.mp hr with ⟨v, hv, rfl⟩
    simp only [lHigh, List.mem_filter] at hv; have hlen := (mem_allBitVecs_iff k v).mp hv.1
    have hspec := fiveVecWitness_spec v; rw [hlen] at hspec
    have h4le5 : 2 ^ k ≤ 5 ^ m := by
      change 2 ^ (2 * m) ≤ 5 ^ m; rw [Nat.pow_mul]; exact Nat.pow_le_pow_left (by decide) m
    have hpow : 2 ^ k ≤ 5 ^ countOnes v :=
      Nat.le_trans h4le5 (Nat.pow_le_pow_right (by decide) (of_decide_eq_true hv.2))
    simp only [lBad, List.mem_filter, List.mem_range, fiveBadResidue, decide_eq_true_eq]
    exact ⟨hspec.1, by rw [hspec.2]; exact hpow⟩
  have hinj : ∀ v₁ ∈ lHigh, ∀ v₂ ∈ lHigh, fiveVecWitness v₁ = fiveVecWitness v₂ → v₁ = v₂ := by
    intro v₁ hv₁ v₂ hv₂ heq
    have s1 := (fiveVecWitness_spec v₁).2; have s2 := (fiveVecWitness_spec v₂).2
    rw [(mem_allBitVecs_iff k v₁).mp (List.mem_filter.mp hv₁).1] at s1
    rw [(mem_allBitVecs_iff k v₂).mp (List.mem_filter.mp hv₂).1] at s2
    rw [← s1, ← s2, heq]
  have h1 := nodup_length_le_of_subset (nodup_map_inj ((allBitVecs_nodup k).filter _) hinj) hsub
  rw [List.length_map] at h1
  have h2 : fiveBadCount k = lBad.length := countLt_eq_filter_range (fiveBadResidue k) (2 ^ k)
  dsimp only [k] at h1 h2; omega
/-- **Barrier 2 (`5n + 1`) Majority Failure Theorem:** for every `m ≥ 1`, strictly more than
`50%` of residues mod `2 ^ (2 * m)` fail single-horizon `5n + 1` contraction. -/
theorem fiveBadCount_even_gt_half {m : Nat} (_hm : 1 ≤ m) :
    2 ^ (2 * m) < 2 * fiveBadCount (2 * m) := by
  let k := 2 * m
  let lHigh := (allBitVecs k).filter (fun v => decide (m ≤ countOnes v))
  let lLow := (allBitVecs k).filter (fun v => !decide (m ≤ countOnes v))
  let v₀ := List.replicate m true ++ List.replicate m false
  have hlen0 : v₀.length = k := by simp [v₀, k]; omega
  have hc0 : countOnes v₀ = m := by
    have htr : ∀ n, countOnes (List.replicate n true) = n := fun n => by
      induction n with | zero => rfl | succ n ih => simp [List.replicate_succ, countOnes, ih]; omega
    have hfa : ∀ n, countOnes (List.replicate n false) = 0 := fun n => by
      induction n with | zero => rfl | succ n ih => simp [List.replicate_succ, countOnes, ih]
    simp [v₀, countOnes_append, htr, hfa]
  have hnot : v₀ ∉ lLow.map flipBits := by
    intro hm; rcases List.mem_map.mp hm with ⟨v, hv, heq⟩
    simp only [lLow, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le] at hv
    have hlen := (mem_allBitVecs_iff k v).mp hv.1; have hcf := countOnes_flipBits v
    have hce : countOnes (flipBits v) = countOnes v₀ := congrArg countOnes heq
    dsimp only [k] at hlen; omega
  have hnd : (v₀ :: lLow.map flipBits).Nodup :=
    List.nodup_cons.mpr ⟨hnot, nodup_map_inj ((allBitVecs_nodup k).filter _)
      (fun _ _ _ _ h => flipBits_inj h)⟩
  have hsub : ∀ w ∈ v₀ :: lLow.map flipBits, w ∈ lHigh := by
    intro w hw; simp only [lHigh, List.mem_filter, decide_eq_true_eq]
    rcases List.mem_cons.mp hw with rfl | hm
    · exact ⟨(mem_allBitVecs_iff k v₀).mpr hlen0, by omega⟩
    · rcases List.mem_map.mp hm with ⟨v, hv, rfl⟩
      simp only [lLow, List.mem_filter, Bool.not_eq_true',
        decide_eq_false_iff_not, Nat.not_le] at hv
      have hlen := (mem_allBitVecs_iff k v).mp hv.1; have hcf := countOnes_flipBits v
      dsimp only [k] at hlen
      exact ⟨(mem_allBitVecs_iff k _).mpr (by simp [flipBits, hlen, k]), by omega⟩
  have hlt := nodup_length_le_of_subset hnd hsub
  simp only [List.length_cons, List.length_map] at hlt
  have hsplit := filter_split_length (fun v => decide (m ≤ countOnes v)) (allBitVecs k)
  have hpow_len : (allBitVecs k).length = 2 ^ k := by
    simpa [List.length_map, List.length_range] using
      (map_terrasParityVec_perm_allBitVecs k).length_eq.symm
  have hbad := highOnes_le_fiveBadCount m
  dsimp only [lHigh, lLow, k] at hsplit hpow_len hlt hbad; omega
/-- **Mod-1024 `5n + 1` Sieve Certificate:** `fiveCoveredCount 10 = 758 < 960`. -/
theorem five_sieve_mod1024_covered :
    fiveCoveredCount 10 = 758 ∧ fiveCoveredCount 10 * 4 < 3 * 1024 ∧
      fiveCoveredCount 10 < coveredCount 10 := by
  have h5 : fiveCoveredCount 10 = 758 := by decide
  rw [h5, sieve_mod1024_covered]; decide
/-- **Barrier 2 (`3n + 1` vs `5n + 1`) Formal Separation Theorem:** contrasts `3n + 1`
vanishing bad density (`3 < 4`) against `5n + 1` majority failure (`5 > 4`) and mod-`1024`
cumulative gap (`758` vs `960`). -/
theorem barrier2_three_vs_five_contrast :
    (∀ D : Nat, 0 < D → ∃ m : Nat, 0 < m ∧ badCount (5 * m) * D < 2 ^ (5 * m)) ∧
    (∀ m : Nat, 1 ≤ m → 2 ^ (2 * m) < 2 * fiveBadCount (2 * m)) ∧
    (fiveCoveredCount 10 = 758 ∧ coveredCount 10 = 960) :=
  ⟨badCount_five_mul_lt_div, fun _ hm => fiveBadCount_even_gt_half hm,
    five_sieve_mod1024_covered.1, sieve_mod1024_covered⟩
end SolveCollatz
