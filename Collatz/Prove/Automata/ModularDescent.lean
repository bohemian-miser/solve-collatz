/-
Copyright (c) 2026 The solve-collatz contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Collatz.Known.TerrasParity

/-!
# Modular Covering & Stopping-Time Descent Certificates (`PROVE-C1`)

Kernel-verified modular covering sieves built on `Collatz.Known.TerrasParity`:
- Decidable residue-class descent predicate `checkDropsAt k r` and bounded sieve `dropsWithin K r`.
- Universal soundness `dropsWithin_sound`: any covered residue class drops strictly below `n` in
  `collatzIter` steps for all `n ≥ 3 ^ K`, plus sharpened `2 ^ K ≤ n` certificates for moduli
  `4`, `16`, and `256`.
- Pure `decide` (zero `native_decide`) density certificates:
  `3 / 4` (`75%` mod `4`), `13 / 16` (`81.25%` mod `16`), and `237 / 256` (`92.578125%` mod `256`).
- Explicit `REF-002` incompleteness complement `sieve_misses_all_odd_class`: for every `1 ≤ K`,
  `dropsWithin K (2 ^ K - 1) = false`, proved directly from `terras_all_odd_rising`.
-/

@[expose] public section

namespace SolveCollatz

/-! ### 1. Decidable Modular Descent Checker -/

/-- Decidable check that residue `r < 2 ^ k` contracts multiplicatively over `k` Terras steps:
`3 ^ countOnes (terrasParityVec k r) < 2 ^ k`. -/
def checkDropsAt (k r : Nat) : Bool :=
  (r < 2 ^ k) && (3 ^ countOnes (terrasParityVec k r) < 2 ^ k)

/-- Decidable bounded sieve checking whether some step horizon `1 ≤ k ≤ K` witnesses
contraction on `r % 2 ^ k` via `checkDropsAt`. -/
def dropsWithin : Nat → Nat → Bool
  | 0, _ => false
  | k + 1, r => dropsWithin k r || checkDropsAt (k + 1) (r % 2 ^ (k + 1))

/-- At horizon `k = 0`, `checkDropsAt 0 r` is always `false` since `3 ^ 0 < 2 ^ 0` fails. -/
theorem checkDropsAt_zero (r : Nat) : checkDropsAt 0 r = false := by
  simp [checkDropsAt, terrasParityVec, countOnes]

/-- Specification of `dropsWithin`: `dropsWithin K r = true` iff there exists `1 ≤ k ≤ K`
with `checkDropsAt k (r % 2 ^ k) = true`. -/
theorem dropsWithin_iff (K r : Nat) :
    dropsWithin K r = true ↔
      ∃ k : Nat, 1 ≤ k ∧ k ≤ K ∧ checkDropsAt k (r % 2 ^ k) = true := by
  induction K with
  | zero =>
    simp only [dropsWithin, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro k hk1 hk0
    omega
  | succ K ih =>
    simp only [dropsWithin, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨k, hk1, hkK, hchk⟩ | htop)
      · exact ⟨k, hk1, Nat.le_succ_of_le hkK, hchk⟩
      · exact ⟨K + 1, Nat.succ_pos K, Nat.le_refl _, htop⟩
    · rintro ⟨k, hk1, hkK, hchk⟩
      rcases Nat.eq_or_lt_of_le hkK with rfl | hlt
      · exact Or.inr hchk
      · exact Or.inl ⟨k, hk1, Nat.lt_succ_iff.mp hlt, hchk⟩

/-! ### 2. Affine Upper Bound & Kernel Soundness -/

/-- Exact one-step doubling identity for `terrasStep`. -/
private theorem two_mul_terrasStep_even {x : Nat} (heven : x % 2 = 0) :
    2 * terrasStep x = x := by
  rw [terrasStep_even heven]
  omega

/-- Exact one-step doubling identity for `terrasStep` on odd inputs. -/
private theorem two_mul_terrasStep_odd {x : Nat} (hodd : x % 2 = 1) :
    2 * terrasStep x = 3 * x + 1 := by
  rw [terrasStep_odd hodd]
  omega

/-- Elementary affine upper bound on `k` Terras steps:
`2 ^ k * terrasIter k n + 2 ^ k ≤ 3 ^ countOnes (terrasParityVec k n) * n + 3 ^ k`. -/
theorem two_pow_mul_terrasIter_add_le (k n : Nat) :
    2 ^ k * terrasIter k n + 2 ^ k ≤ 3 ^ countOnes (terrasParityVec k n) * n + 3 ^ k := by
  induction k generalizing n with
  | zero => simp [terrasIter, terrasParityVec, countOnes]
  | succ k ih =>
    have hih := ih (terrasStep n)
    have hmul2 : 2 ^ (k + 1) * terrasIter (k + 1) n + 2 ^ (k + 1) =
        2 * (2 ^ k * terrasIter k (terrasStep n) + 2 ^ k) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc, ← Nat.mul_add]
      rfl
    have hsc : 2 * (3 ^ countOnes (terrasParityVec k (terrasStep n)) * terrasStep n + 3 ^ k) =
        3 ^ countOnes (terrasParityVec k (terrasStep n)) * (2 * terrasStep n) + 2 * 3 ^ k := by
      rw [Nat.mul_add, Nat.mul_left_comm 2 _ (terrasStep n)]
    rw [hmul2]
    have hle2 := Nat.le_trans (Nat.mul_le_mul_left 2 hih) (Nat.le_of_eq hsc)
    by_cases heven : n % 2 = 0
    · have hbool : (n % 2 == 1) = false := by
        cases h : (n % 2 == 1)
        · rfl
        · exfalso; have := beq_iff_eq.mp h; omega
      simp only [terrasParityVec, countOnes, hbool, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      rw [two_mul_terrasStep_even heven] at hle2
      have h3pow : 2 * 3 ^ k ≤ 3 ^ (k + 1) := by rw [Nat.pow_succ]; omega
      omega
    · have hodd : n % 2 = 1 := by omega
      have hbool : (n % 2 == 1) = true := beq_iff_eq.mpr hodd
      simp only [terrasParityVec, countOnes, hbool, ↓reduceIte]
      rw [two_mul_terrasStep_odd hodd] at hle2
      have hcnt : countOnes (terrasParityVec k (terrasStep n)) ≤ k := by
        simpa [terrasParityVec_length] using countOnes_le_length (terrasParityVec k (terrasStep n))
      have h3le : 3 ^ countOnes (terrasParityVec k (terrasStep n)) ≤ 3 ^ k :=
        Nat.pow_le_pow_right (by decide) hcnt
      have h3succ : 3 ^ (1 + countOnes (terrasParityVec k (terrasStep n))) =
          3 ^ countOnes (terrasParityVec k (terrasStep n)) * 3 := by
        rw [Nat.add_comm, Nat.pow_succ]
      have hrhs : 3 ^ countOnes (terrasParityVec k (terrasStep n)) * (3 * n + 1) + 2 * 3 ^ k =
          3 ^ countOnes (terrasParityVec k (terrasStep n)) * (3 * n) +
            3 ^ countOnes (terrasParityVec k (terrasStep n)) + 2 * 3 ^ k := by
        rw [Nat.mul_add, Nat.mul_one]
      rw [h3succ, Nat.mul_assoc, Nat.pow_succ 3 k]
      omega

/-- Modulo reduction compatibility `(n % 2 ^ K) % 2 ^ k = n % 2 ^ k` for `k ≤ K`. -/
private theorem mod_two_pow_of_le {k K : Nat} (hk : k ≤ K) (n : Nat) :
    (n % 2 ^ K) % 2 ^ k = n % 2 ^ k := by
  have hdvd : 2 ^ k ∣ 2 ^ K := ⟨2 ^ (K - k), by rw [← Nat.pow_add, Nat.add_sub_of_le hk]⟩
  exact Nat.mod_mod_of_dvd n hdvd

/-- One-horizon soundness: if `checkDropsAt k (n % 2 ^ k) = true` with `1 ≤ k` and `3 ^ k ≤ n`,
then `collatzIter j n < n` for `j = k + countOnes (terrasParityVec k n) > 0`. -/
theorem checkDropsAt_sound {k n : Nat} (hk : 1 ≤ k)
    (hchk : checkDropsAt k (n % 2 ^ k) = true) (hn : 3 ^ k ≤ n) :
    ∃ j : Nat, 0 < j ∧ collatzIter j n < n := by
  simp only [checkDropsAt, Bool.and_eq_true, decide_eq_true_eq] at hchk
  rw [terrasParityVec_mod_eq] at hchk
  have hpow_lt : 3 ^ countOnes (terrasParityVec k n) < 2 ^ k := hchk.2
  have hkpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hbound := two_pow_mul_terrasIter_add_le k n
  have hmul_lt : 2 ^ k * terrasIter k n < 2 ^ k * n := by
    have h1 : 3 ^ countOnes (terrasParityVec k n) + 1 ≤ 2 ^ k := hpow_lt
    have h2 : (3 ^ countOnes (terrasParityVec k n) + 1) * n ≤ 2 ^ k * n :=
      Nat.mul_le_mul_right n h1
    have h3 : 3 ^ countOnes (terrasParityVec k n) * n + 3 ^ k ≤
        (3 ^ countOnes (terrasParityVec k n) + 1) * n := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    omega
  have hterras_lt : terrasIter k n < n := Nat.lt_of_mul_lt_mul_left hmul_lt
  refine ⟨k + countOnes (terrasParityVec k n), by omega, ?_⟩
  rwa [collatzIter_eq_terrasIter k n]

/-- **Kernel Soundness (`PROVE-C1`):** whenever `dropsWithin K r = true`, every `n ≥ 3 ^ K`
satisfying `n % 2 ^ K = r` strictly descends below `n` in finitely many Collatz steps. -/
theorem dropsWithin_sound {K r n : Nat} (hdrop : dropsWithin K r = true)
    (hmod : n % 2 ^ K = r) (hn : 3 ^ K ≤ n) :
    ∃ j : Nat, 0 < j ∧ collatzIter j n < n := by
  rcases (dropsWithin_iff K r).mp hdrop with ⟨k, hk1, hkK, hchk⟩
  rw [← hmod, mod_two_pow_of_le hkK] at hchk
  have hn_k : 3 ^ k ≤ n := Nat.le_trans (Nat.pow_le_pow_right (by decide) hkK) hn
  exact checkDropsAt_sound hk1 hchk hn_k

/-- Strengthened one-horizon check requiring `terrasIter k r + 3 ^ c < r + 2 ^ k`, which yields
strict descent already from the sharp threshold `2 ^ k ≤ n`. -/
def checkDropsStrong (k r : Nat) : Bool :=
  checkDropsAt k r && (terrasIter k r + 3 ^ countOnes (terrasParityVec k r) < r + 2 ^ k)

/-- Bounded strong sieve checking whether some `1 ≤ k ≤ K` satisfies `checkDropsStrong`. -/
def dropsWithinStrong : Nat → Nat → Bool
  | 0, _ => false
  | k + 1, r => dropsWithinStrong k r || checkDropsStrong (k + 1) (r % 2 ^ (k + 1))

/-- Specification of `dropsWithinStrong`. -/
theorem dropsWithinStrong_iff (K r : Nat) :
    dropsWithinStrong K r = true ↔
      ∃ k : Nat, 1 ≤ k ∧ k ≤ K ∧ checkDropsStrong k (r % 2 ^ k) = true := by
  induction K with
  | zero =>
    simp only [dropsWithinStrong, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro k hk1 hk0
    omega
  | succ K ih =>
    simp only [dropsWithinStrong, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨k, hk1, hkK, hchk⟩ | htop)
      · exact ⟨k, hk1, Nat.le_succ_of_le hkK, hchk⟩
      · exact ⟨K + 1, Nat.succ_pos K, Nat.le_refl _, htop⟩
    · rintro ⟨k, hk1, hkK, hchk⟩
      rcases Nat.eq_or_lt_of_le hkK with rfl | hlt
      · exact Or.inr hchk
      · exact Or.inl ⟨k, hk1, Nat.lt_succ_iff.mp hlt, hchk⟩

/-- Strong one-horizon soundness from the sharp threshold `2 ^ k ≤ n`. -/
theorem checkDropsStrong_sound {k n : Nat} (hk : 1 ≤ k)
    (hchk : checkDropsStrong k (n % 2 ^ k) = true) (hn : 2 ^ k ≤ n) :
    ∃ j : Nat, 0 < j ∧ collatzIter j n < n := by
  simp only [checkDropsStrong, checkDropsAt, Bool.and_eq_true, decide_eq_true_eq] at hchk
  rcases hchk with ⟨⟨_, hpow⟩, hrem⟩
  rw [terrasParityVec_mod_eq] at hpow hrem
  have hq : 1 ≤ n / 2 ^ k := Nat.div_pos hn (Nat.two_pow_pos k)
  have hmul : 3 ^ countOnes (terrasParityVec k n) * (n / 2 ^ k - 1) ≤
      2 ^ k * (n / 2 ^ k - 1) :=
    Nat.mul_le_mul_right (n / 2 ^ k - 1) (Nat.le_of_lt hpow)
  have hsum : terrasIter k (n % 2 ^ k) + 3 ^ countOnes (terrasParityVec k n) * (n / 2 ^ k) <
      n % 2 ^ k + 2 ^ k * (n / 2 ^ k) := by
    have hqeq : n / 2 ^ k = 1 + (n / 2 ^ k - 1) := by omega
    rw [hqeq, Nat.mul_add, Nat.mul_one, Nat.mul_add, Nat.mul_one]
    omega
  have hterras : terrasIter k n < n := by
    rw [terrasIter_mod_eq k n]
    simpa [Nat.mod_add_div] using hsum
  refine ⟨k + countOnes (terrasParityVec k n), by omega, ?_⟩
  rwa [collatzIter_eq_terrasIter k n]

/-- Sharp `2 ^ K ≤ n` soundness for `dropsWithinStrong`. -/
theorem dropsWithinStrong_sound {K r n : Nat} (hdrop : dropsWithinStrong K r = true)
    (hmod : n % 2 ^ K = r) (hn : 2 ^ K ≤ n) :
    ∃ j : Nat, 0 < j ∧ collatzIter j n < n := by
  rcases (dropsWithinStrong_iff K r).mp hdrop with ⟨k, hk1, hkK, hchk⟩
  rw [← hmod, mod_two_pow_of_le hkK] at hchk
  have hn_k : 2 ^ k ≤ n := Nat.le_trans (Nat.pow_le_pow_right (by decide) hkK) hn
  exact checkDropsStrong_sound hk1 hchk hn_k

/-- Dyadic universal checker over `[lo, lo + 2 ^ d)` for shallow kernel reduction. -/
def allPow2 (p : Nat → Bool) : Nat → Nat → Bool
  | 0, lo => p lo
  | d + 1, lo => allPow2 p d lo && allPow2 p d (lo + 2 ^ d)

/-- Soundness of `allPow2`: `allPow2 p d lo = true` implies `p r = true` on `[lo, lo + 2 ^ d)`. -/
theorem allPow2_sound (p : Nat → Bool) (d lo : Nat) (hall : allPow2 p d lo = true) :
    ∀ r : Nat, lo ≤ r → r < lo + 2 ^ d → p r = true := by
  induction d generalizing lo with
  | zero =>
    intro r hlo hlt
    have heq : r = lo := by simp at hlt; omega
    subst heq
    exact hall
  | succ d ih =>
    intro r hlo hlt
    simp only [allPow2, Bool.and_eq_true] at hall
    have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
    rw [hpow] at hlt
    by_cases hmid : r < lo + 2 ^ d
    · exact ih lo hall.1 r hlo hmid
    · exact ih (lo + 2 ^ d) hall.2 r (Nat.le_of_not_lt hmid) (by omega)

/-- Helper lifting `allPow2` equivalence between `dropsWithin` and `dropsWithinStrong`. -/
private theorem dropsWithin_sound_of_allPow2 {K r n : Nat}
    (hall : allPow2 (fun m => !dropsWithin K m || dropsWithinStrong K m) K 0 = true)
    (hdrop : dropsWithin K r = true) (hmod : n % 2 ^ K = r) (hn : 2 ^ K ≤ n) :
    ∃ j : Nat, 0 < j ∧ collatzIter j n < n := by
  have hrlt : r < 2 ^ K := by rw [← hmod]; exact Nat.mod_lt n (Nat.two_pow_pos K)
  have himp := allPow2_sound _ K 0 hall r (Nat.zero_le r) (by simpa using hrlt)
  simp only [Bool.or_eq_true, Bool.not_eq_true', hdrop] at himp
  rcases himp with hfalse | hstrong
  · exact absurd hfalse (by decide)
  · exact dropsWithinStrong_sound hstrong hmod hn

/-- Sharp `4 ≤ n` soundness for the mod-`4` (`K = 2`) sieve. -/
theorem dropsWithin_sound_mod4 {r n : Nat} (hdrop : dropsWithin 2 r = true)
    (hmod : n % 4 = r) (hn : 4 ≤ n) :
    ∃ j : Nat, 0 < j ∧ collatzIter j n < n :=
  dropsWithin_sound_of_allPow2 (by decide) hdrop hmod hn

/-- Sharp `16 ≤ n` soundness for the mod-`16` (`K = 4`) sieve. -/
theorem dropsWithin_sound_mod16 {r n : Nat} (hdrop : dropsWithin 4 r = true)
    (hmod : n % 16 = r) (hn : 16 ≤ n) :
    ∃ j : Nat, 0 < j ∧ collatzIter j n < n :=
  dropsWithin_sound_of_allPow2 (by decide) hdrop hmod hn

/-- Sharp `256 ≤ n` soundness for the mod-`256` (`K = 8`) sieve. -/
theorem dropsWithin_sound_mod256 {r n : Nat} (hdrop : dropsWithin 8 r = true)
    (hmod : n % 256 = r) (hn : 256 ≤ n) :
    ∃ j : Nat, 0 < j ∧ collatzIter j n < n :=
  dropsWithin_sound_of_allPow2 (by decide) hdrop hmod hn

/-! ### 3. Kernel-Verified Density Certificates (`mod 4`, `mod 16`, `mod 256`) -/

/-- Linear count of `r < m` satisfying Boolean predicate `p r = true`. -/
def countBelow (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | m + 1 => countBelow p m + (if p m then 1 else 0)

/-- Dyadic bisection count of `r ∈ [lo, lo + 2 ^ d)` satisfying `p r = true` (depth `d`). -/
def countPow2 (p : Nat → Bool) : Nat → Nat → Nat
  | 0, lo => if p lo then 1 else 0
  | d + 1, lo => countPow2 p d lo + countPow2 p d (lo + 2 ^ d)

/-- Splitting identity linking `countBelow` and `countPow2`. -/
theorem countBelow_add_two_pow (p : Nat → Bool) (d lo : Nat) :
    countBelow p (lo + 2 ^ d) = countBelow p lo + countPow2 p d lo := by
  induction d generalizing lo with
  | zero => rfl
  | succ d ih =>
    have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
    rw [hpow, ← Nat.add_assoc, ih (lo + 2 ^ d), ih lo, countPow2, Nat.add_assoc]

/-- Number of residue classes `r < 2 ^ K` covered by `dropsWithin K r = true`. -/
def sieveCoveredCount (K : Nat) : Nat :=
  countPow2 (dropsWithin K) K 0

/-- Equivalence between `sieveCoveredCount K` and the linear count `countBelow`. -/
theorem sieveCoveredCount_eq_countBelow (K : Nat) :
    sieveCoveredCount K = countBelow (dropsWithin K) (2 ^ K) := by
  have h := countBelow_add_two_pow (dropsWithin K) K 0
  simpa [sieveCoveredCount, countBelow] using h.symm

/-- **Mod-4 Density Certificate:** `3` of `4` residue classes (`75%`) drop within `2` Terras
steps (`r ∈ {0, 1, 2}`). -/
theorem sieve_mod4_count : sieveCoveredCount 2 = 3 := by
  decide

/-- **Mod-16 Density Certificate:** `13` of `16` residue classes (`81.25%`) drop within `4`
Terras steps. -/
theorem sieve_mod16_count : sieveCoveredCount 4 = 13 := by
  decide

/-- **Mod-256 Density Certificate:** `237` of `256` residue classes (`92.578125%`) drop within
`8` Terras steps. -/
theorem sieve_mod256_count : sieveCoveredCount 8 = 237 := by
  decide

/-! ### 4. Explicit `REF-002` Incompleteness Complement -/

/-- For `k ≤ K`, `(2 ^ K - 1) % 2 ^ k = 2 ^ k - 1`. -/
private theorem two_pow_sub_one_mod {k K : Nat} (hk : k ≤ K) :
    (2 ^ K - 1) % 2 ^ k = 2 ^ k - 1 := by
  have hkpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hqpos : 0 < 2 ^ (K - k) := Nat.two_pow_pos (K - k)
  have hpow : 2 ^ K = 2 ^ k * 2 ^ (K - k) := by rw [← Nat.pow_add, Nat.add_sub_of_le hk]
  have hle : 2 ^ k ≤ 2 ^ k * 2 ^ (K - k) := Nat.le_mul_of_pos_right _ hqpos
  have heq : 2 ^ K - 1 = (2 ^ k - 1) + 2 ^ k * (2 ^ (K - k) - 1) := by
    rw [hpow, Nat.mul_sub_left_distrib, Nat.mul_one]
    omega
  rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- `countOnes (List.replicate k true) = k`. -/
private theorem countOnes_replicate_true' (k : Nat) :
    countOnes (List.replicate k true) = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, countOnes, ih]; omega

/-- For every `1 ≤ k`, `checkDropsAt k (2 ^ k - 1) = false`, certified directly via
`TerrasParity.terras_all_odd_rising`. -/
private theorem checkDropsAt_two_pow_sub_one {k : Nat} (hk : 1 ≤ k) :
    checkDropsAt k (2 ^ k - 1) = false := by
  have hkpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hmod : (2 ^ k - 1) % 2 ^ k = 2 ^ k - 1 := Nat.mod_eq_of_lt (by omega)
  have hvec := (terras_all_odd_rising hk hmod).1
  cases hchk : checkDropsAt k (2 ^ k - 1)
  · rfl
  · exfalso
    simp only [checkDropsAt, Bool.and_eq_true, decide_eq_true_eq] at hchk
    rw [hvec, countOnes_replicate_true'] at hchk
    have h2le3 : 2 ^ k ≤ 3 ^ k := Nat.pow_le_pow_left (by decide) k
    omega

/-- **Explicit `REF-002` Incompleteness Complement (`ℤ₂` Barrier):** for every horizon `1 ≤ K`,
the all-odd residue class `2 ^ K - 1 (mod 2 ^ K)` is missed by `dropsWithin K`. -/
theorem sieve_misses_all_odd_class {K : Nat} (_hK : 1 ≤ K) :
    dropsWithin K (2 ^ K - 1) = false := by
  cases h : dropsWithin K (2 ^ K - 1)
  · rfl
  · exfalso
    rcases (dropsWithin_iff K (2 ^ K - 1)).mp h with ⟨k, hk1, hkK, hchk⟩
    rw [two_pow_sub_one_mod hkK, checkDropsAt_two_pow_sub_one hk1] at hchk
    exact Bool.false_ne_true hchk

end SolveCollatz
