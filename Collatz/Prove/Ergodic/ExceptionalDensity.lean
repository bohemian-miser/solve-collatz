/-
Copyright (c) 2026 The solve-collatz contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Collatz.Known.TaoBridge

/-!
# Quantitative Exceptional-Set Decay & Density Obstructions (`PROVE-A1`)

Pure Lean 4 core formalization (zero Mathlib, zero reals) advancing Track A node `PROVE-A1`:
1. Bounded stopping-time predicate `HasStoppingTimeLe`, bridging `terrasIter` and
   `HasFiniteStoppingTime`.
2. Quantitative exponential Chernoff decay (`3125 < 3456`) on shifted blocks `[A, A + 2^(5*m))`
   and prefixes `[0, N)`, explicit constructive natural-density modulus
   `explicitDensityThreshold D = 2 ^ (119 * bitLen (4 * D))`, and unconditional power-saving
   decay `HasPowerSavingDensityOne HasFiniteStoppingTime 237 238` (`O(N^(237/238))`).
3. Exact Track A equivalence theorems linking frozen `Challenge.CollatzConjecture` to
   `HasFiniteStoppingTime` (noting `¬ HasFiniteStoppingTime 1`, so `1` is always exceptional).
4. Formal `PROVE-A1` density-vs-universality obstruction (`Barriers 4 & 5`): `IsExpSparse`
   (`O(log N)` sparse sets, including finite cycle orbits `cycleOrbitList` and exponentially
   divergent orbits) beats every subpolynomial exceptional-set bound `N^(a/b)`, proving that
   even `O(N^(1-δ))` or `O(log N)` density bounds cannot rule out cycles or divergent orbits.

Barrier survival note (`frontier/BARRIERS.md`):
- Barriers 1 & 2 (`3n-1`, `5n+1`): quantitative Chernoff decay (`3125 < 3456`) uses `3n+1`'s
  negative average log-drift `log₂(3/4) < 0`, which fails for `5n+1`.
- Barrier 3 (`ℤ_{<0}`): equivalence `collatzConjecture_iff_forall_finiteStoppingTime` relies on
  archimedean well-ordering below `1` in `ℕ`, which fails on `ℤ_{<0}`.
- Barriers 4 & 5 (`ℤ₂`, Conway): Section 4 proves why exceptional-density improvements alone
  cannot cross the global universality gap without Diophantine (`PROVE-B1`) input.
-/

@[expose] public section

namespace SolveCollatz

private theorem dec_true' {P : Prop} (h : P) : @decide P (Classical.propDecidable P) = true :=
  @decide_eq_true P (Classical.propDecidable P) h
private theorem dec_false' {P : Prop} (h : ¬ P) : @decide P (Classical.propDecidable P) = false :=
  @decide_eq_false P (Classical.propDecidable P) h
private theorem of_dec_true' {P : Prop} (h : @decide P (Classical.propDecidable P) = true) : P :=
  @of_decide_eq_true P (Classical.propDecidable P) h

/-! ### 1. Bounded Stopping Time & Core Bridges -/

/-- `HasStoppingTimeLe n K` holds if `collatzIter t n < n` for some `t ≤ K`. -/
def HasStoppingTimeLe (n K : Nat) : Prop := ∃ t : Nat, t ≤ K ∧ collatzIter t n < n

/-- No natural number drops strictly below itself in `0` Collatz steps. -/
theorem hasStoppingTimeLe_zero (n : Nat) : ¬ HasStoppingTimeLe n 0 := by
  rintro ⟨t, ht, hlt⟩; have h0 := Nat.eq_zero_of_le_zero ht; subst h0
  simp only [collatzIter] at hlt; omega

/-- `HasStoppingTimeLe n K` automatically forces `0 < t` since `collatzIter 0 n = n`. -/
theorem hasStoppingTimeLe_iff_pos (n K : Nat) :
    HasStoppingTimeLe n K ↔ ∃ t : Nat, 0 < t ∧ t ≤ K ∧ collatzIter t n < n :=
  ⟨fun ⟨t, ht, hlt⟩ => match t with
    | 0 => by simp only [collatzIter] at hlt; omega
    | t' + 1 => ⟨t' + 1, Nat.succ_pos t', ht, hlt⟩,
   fun ⟨t, _, ht, hlt⟩ => ⟨t, ht, hlt⟩⟩

/-- Any bounded stopping time implies `HasFiniteStoppingTime`. -/
theorem hasFiniteStoppingTime_of_hasStoppingTimeLe {n K : Nat} (h : HasStoppingTimeLe n K) :
    HasFiniteStoppingTime n :=
  let ⟨t, ht0, _, hlt⟩ := (hasStoppingTimeLe_iff_pos n K).mp h; ⟨t, ht0, hlt⟩

/-- `HasFiniteStoppingTime n` is equivalent to `∃ K, HasStoppingTimeLe n K`. -/
theorem hasFiniteStoppingTime_iff_exists_le (n : Nat) :
    HasFiniteStoppingTime n ↔ ∃ K : Nat, HasStoppingTimeLe n K :=
  ⟨fun ⟨t, _, hlt⟩ => ⟨t, t, Nat.le_refl t, hlt⟩,
   fun ⟨_, h⟩ => hasFiniteStoppingTime_of_hasStoppingTimeLe h⟩

/-- Monotonicity of `HasStoppingTimeLe` in the step horizon `K`. -/
theorem hasStoppingTimeLe_mono {n K₁ K₂ : Nat} (hK : K₁ ≤ K₂)
    (h : HasStoppingTimeLe n K₁) : HasStoppingTimeLe n K₂ :=
  let ⟨t, ht, hlt⟩ := h; ⟨t, Nat.le_trans ht hK, hlt⟩

/-- Any `k`-step compressed Terras drop yields a bounded standard Collatz drop within `2 * k`. -/
theorem hasStoppingTimeLe_of_terras_lt {k n : Nat} (hlt : terrasIter k n < n) :
    HasStoppingTimeLe n (2 * k) := by
  refine ⟨k + countOnes (terrasParityVec k n), ?_, by rw [collatzIter_eq_terrasIter]; exact hlt⟩
  have hlen := countOnes_le_length (terrasParityVec k n)
  rw [terrasParityVec_length] at hlen; omega

/-! ### 2. Quantitative Exponential Chernoff Decay & Constructive Density Modulus -/

private theorem countLt_badResidue_mod_eq' (k : Nat) :
    countLt (fun n => badResidue k (n % 2 ^ k)) (2 ^ k) = badCount k :=
  Nat.le_antisymm
    (countLt_mono_pred (2 ^ k) (fun _ hi h => by rw [Nat.mod_eq_of_lt hi] at h; exact h))
    (countLt_mono_pred (2 ^ k) (fun _ hi h => by rw [Nat.mod_eq_of_lt hi]; exact h))

/-- Periodicity preserves block counts over any shifted interval `[A, A + M)`. -/
theorem countLt_periodic_shift (p : Nat → Bool) (M A : Nat)
    (hper : ∀ i : Nat, p (i + M) = p i) :
    countLt (fun i => p (A + i)) M = countLt p M := by
  have hL := countLt_add p A M; have hR := countLt_add p M A
  have htail : countLt (fun i => p (M + i)) A = countLt p A := by
    have heq : (fun i => p (M + i)) = p := funext (fun i => by rw [Nat.add_comm]; exact hper i)
    rw [heq]
  rw [htail] at hR; rw [Nat.add_comm A M] at hL; omega

/-- Explicit upper bound on integers `n < N` failing `terrasIter k n < n`. -/
theorem countLt_fails_terras_le_public (k N : Nat) :
    countLt (fun n => decide (¬ terrasIter k n < n)) N ≤
      2 ^ (3 * k) + badCount k * (N / 2 ^ k) + 2 ^ k := by
  let badPred : Nat → Bool := fun n => decide (n < 2 ^ (3 * k)) || badResidue k (n % 2 ^ k)
  have hmono : countLt (fun n => decide (¬ terrasIter k n < n)) N ≤ countLt badPred N := by
    refine countLt_mono_pred N (fun n _ hn => ?_)
    by_cases hsmall : n < 2 ^ (3 * k)
    · simp [badPred, hsmall]
    · by_cases hbadres : badResidue k (n % 2 ^ k) = true
      · simp [badPred, hbadres]
      · exfalso
        have hlow := Nat.lt_of_not_le (fun (hge : 2 ^ k ≤
          3 ^ countOnes (terrasParityVec k (n % 2 ^ k))) => absurd (decide_eq_true hge) hbadres)
        exact of_decide_eq_true hn (terras_lt_of_large_low_ones (Nat.le_of_not_lt hsmall) hlow).1
  have hor := countLt_or_le (fun n => decide (n < 2 ^ (3 * k)))
    (fun n => badResidue k (n % 2 ^ k)) N
  dsimp only [badPred] at hmono
  have hsmall_bd := countLt_lt_bound (2 ^ (3 * k)) N
  have hper_bd := countLt_periodic_le (fun n => badResidue k (n % 2 ^ k)) (Nat.two_pow_pos k)
    (badResidue_mod_periodic k) N
  rw [countLt_badResidue_mod_eq' k] at hper_bd
  have hbad_le_M : badCount k ≤ 2 ^ k := countLt_le _ (2 ^ k)
  omega

/-- **Block Exponential Decay (Bounded Stopping Time):** on any interval `[A, A + 2^(5*m))`
with `A ≥ 2^(15*m)`, the count of integers failing `HasStoppingTimeLe _ (10*m)` satisfies the
exact Chernoff ratio `(3125 / 3456)^m`. -/
theorem exceptionalBlock_bounded_exp_decay (m A : Nat) (hA : 2 ^ (15 * m) ≤ A) :
    countLt (fun i => @decide (¬ HasStoppingTimeLe (A + i) (10 * m))
      (Classical.propDecidable _)) (2 ^ (5 * m)) * 3456 ^ m ≤ 3125 ^ m * 2 ^ (5 * m) := by
  have hmono : countLt (fun i => @decide (¬ HasStoppingTimeLe (A + i) (10 * m))
      (Classical.propDecidable _)) (2 ^ (5 * m)) ≤ badCount (5 * m) := by
    rw [← countLt_badResidue_mod_eq' (5 * m),
      ← countLt_periodic_shift (fun n => badResidue (5 * m) (n % 2 ^ (5 * m)))
        (2 ^ (5 * m)) A (badResidue_mod_periodic (5 * m))]
    refine countLt_mono_pred (2 ^ (5 * m)) (fun i _ hi => ?_)
    have hnot : ¬ HasStoppingTimeLe (A + i) (10 * m) := of_dec_true' hi
    by_cases hbad : badResidue (5 * m) ((A + i) % 2 ^ (5 * m)) = true
    · exact hbad
    · exfalso
      have hlow : 3 ^ countOnes (terrasParityVec (5 * m) ((A + i) % 2 ^ (5 * m))) < 2 ^ (5 * m) :=
        Nat.lt_of_not_le (fun hge => absurd (decide_eq_true hge) hbad)
      have hgeA : 2 ^ (3 * (5 * m)) ≤ A + i := by rw [show 3 * (5 * m) = 15 * m by omega]; omega
      have hdrop := hasStoppingTimeLe_of_terras_lt (terras_lt_of_large_low_ones hgeA hlow).1
      exact hnot (by rwa [show 2 * (5 * m) = 10 * m by omega] at hdrop)
  exact Nat.le_trans (Nat.mul_le_mul_right _ hmono) (badCount_five_mul_decay m)

/-- **Block Exponential Decay (Finite Stopping Time):** on any interval `[A, A + 2^(5*m))`
with `A ≥ 2^(15*m)`, the exceptional count for `HasFiniteStoppingTime` decays as `(3125/3456)^m`.
-/
theorem exceptionalBlock_exp_decay (m A : Nat) (hA : 2 ^ (15 * m) ≤ A) :
    countLt (fun i => @decide (¬ HasFiniteStoppingTime (A + i))
      (Classical.propDecidable _)) (2 ^ (5 * m)) * 3456 ^ m ≤ 3125 ^ m * 2 ^ (5 * m) := by
  have hmono : countLt (fun i => @decide (¬ HasFiniteStoppingTime (A + i))
      (Classical.propDecidable _)) (2 ^ (5 * m)) ≤
      countLt (fun i => @decide (¬ HasStoppingTimeLe (A + i) (10 * m))
        (Classical.propDecidable _)) (2 ^ (5 * m)) :=
    countLt_mono_pred _ (fun i _ hi =>
      dec_true' (fun h => of_dec_true' hi (hasFiniteStoppingTime_of_hasStoppingTimeLe h)))
  exact Nat.le_trans (Nat.mul_le_mul_right _ hmono) (exceptionalBlock_bounded_exp_decay m A hA)

private theorem chernoff_tail_absorb {m N : Nat} (hm : 1 ≤ m) (hN : 2 ^ (17 * m) ≤ N) :
    2 ^ (15 * m) * 3456 ^ m + 2 ^ (5 * m) * 3456 ^ m ≤ 3125 ^ m * N := by
  have h3456 : 3456 ^ m ≤ (2 * 3125) ^ m := Nat.pow_le_pow_left (by decide : 3456 ≤ 2 * 3125) m
  rw [Nat.mul_pow] at h3456
  have ha : 2 ^ (15 * m) * 3456 ^ m ≤ 3125 ^ m * 2 ^ (16 * m) := by
    calc 2 ^ (15 * m) * 3456 ^ m ≤ 2 ^ (15 * m) * (2 ^ m * 3125 ^ m) :=
          Nat.mul_le_mul_left _ h3456
      _ = 3125 ^ m * 2 ^ (16 * m) := by
          rw [← Nat.mul_assoc, ← Nat.pow_add, Nat.mul_comm _ (3125 ^ m),
            show 15 * m + m = 16 * m by omega]
  have hb : 2 ^ (5 * m) * 3456 ^ m ≤ 3125 ^ m * 2 ^ (16 * m) :=
    Nat.le_trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))) ha
  have hpow : 2 ^ (16 * m) + 2 ^ (16 * m) ≤ 2 ^ (17 * m) := by
    rw [show 2 ^ (16 * m) + 2 ^ (16 * m) = 2 ^ (16 * m + 1) by rw [Nat.pow_succ]; omega]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have hsum : 3125 ^ m * 2 ^ (16 * m) + 3125 ^ m * 2 ^ (16 * m) ≤ 3125 ^ m * N := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (Nat.le_trans hpow hN)
  omega

/-- **Quantitative Exponential Decay on `[0, N)` (Bounded Stopping Time):** for all
`N ≥ 2^(17*m)`, failures of `HasStoppingTimeLe _ (10*m)` below `N` are at most
`2 * (3125 / 3456)^m * N`. -/
theorem exceptionalCount_bounded_exp_decay_ge (m N : Nat) (hN : 2 ^ (17 * m) ≤ N) :
    countLt (fun n => @decide (¬ HasStoppingTimeLe n (10 * m)) (Classical.propDecidable _)) N *
      3456 ^ m ≤ 2 * 3125 ^ m * N := by
  cases m with
  | zero =>
    have := countLt_le (fun n => @decide (¬ HasStoppingTimeLe n 0) (Classical.propDecidable _)) N
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.mul_one]; omega
  | succ k =>
    have hmono : countLt (fun n => @decide (¬ HasStoppingTimeLe n (10 * (k + 1)))
        (Classical.propDecidable _)) N ≤
        countLt (fun n => decide (¬ terrasIter (5 * (k + 1)) n < n)) N :=
      countLt_mono_pred N (fun n _ hn => decide_eq_true (fun hlt => by
        have hd := hasStoppingTimeLe_of_terras_lt hlt
        rw [show 2 * (5 * (k + 1)) = 10 * (k + 1) by omega] at hd; exact of_dec_true' hn hd))
    have h1 := Nat.mul_le_mul_right (3456 ^ (k + 1))
      (Nat.le_trans hmono (countLt_fails_terras_le_public (5 * (k + 1)) N))
    rw [show 3 * (5 * (k + 1)) = 15 * (k + 1) by omega, Nat.add_mul, Nat.add_mul,
      Nat.mul_right_comm (badCount (5 * (k + 1))) (N / 2 ^ (5 * (k + 1))) (3456 ^ (k + 1))] at h1
    have hmid : badCount (5 * (k + 1)) * 3456 ^ (k + 1) * (N / 2 ^ (5 * (k + 1))) ≤
        3125 ^ (k + 1) * N := by
      calc badCount (5 * (k + 1)) * 3456 ^ (k + 1) * (N / 2 ^ (5 * (k + 1)))
          ≤ (3125 ^ (k + 1) * 2 ^ (5 * (k + 1))) * (N / 2 ^ (5 * (k + 1))) :=
            Nat.mul_le_mul_right _ (badCount_five_mul_decay (k + 1))
        _ = 3125 ^ (k + 1) * (2 ^ (5 * (k + 1)) * (N / 2 ^ (5 * (k + 1)))) := Nat.mul_assoc _ _ _
        _ ≤ 3125 ^ (k + 1) * N := Nat.mul_le_mul_left _ (Nat.mul_div_le N (2 ^ (5 * (k + 1))))
    have htail : 2 ^ (15 * (k + 1)) * 3456 ^ (k + 1) + 2 ^ (5 * (k + 1)) * 3456 ^ (k + 1) ≤
        3125 ^ (k + 1) * N := chernoff_tail_absorb (Nat.succ_pos k) hN
    have h2 : 2 * 3125 ^ (k + 1) * N = 3125 ^ (k + 1) * N + 3125 ^ (k + 1) * N := by
      rw [Nat.mul_right_comm 2 (3125 ^ (k + 1)) N, Nat.two_mul, Nat.add_mul, Nat.mul_comm N]
    omega

/-- **Quantitative Exponential Decay on `[0, N)` (Finite Stopping Time):** for all
`N ≥ 2^(17*m)`, `exceptionalCount N * 3456 ^ m ≤ 2 * 3125 ^ m * N`. -/
theorem exceptionalCount_exp_decay_ge (m N : Nat) (hN : 2 ^ (17 * m) ≤ N) :
    exceptionalCount N * 3456 ^ m ≤ 2 * 3125 ^ m * N := by
  have hmono : exceptionalCount N ≤ countLt (fun n => @decide (¬ HasStoppingTimeLe n (10 * m))
      (Classical.propDecidable _)) N := by
    unfold exceptionalCount
    exact countLt_mono_pred N (fun n _ hn =>
      dec_true' (fun h => of_dec_true' hn (hasFiniteStoppingTime_of_hasStoppingTimeLe h)))
  exact Nat.le_trans (Nat.mul_le_mul_right _ hmono) (exceptionalCount_bounded_exp_decay_ge m N hN)

/-- **Dyadic-Block Prefix Exponential Decay (`2^(5*L)`):** for any `4 * m ≤ L`,
`exceptionalCount (2^(5*L)) * 3456 ^ m ≤ 2 * 3125 ^ m * 2^(5*L)`. -/
theorem exceptionalCount_two_pow_exp_decay (m L : Nat) (hL : 4 * m ≤ L) :
    exceptionalCount (2 ^ (5 * L)) * 3456 ^ m ≤ 2 * 3125 ^ m * 2 ^ (5 * L) :=
  exceptionalCount_exp_decay_ge m (2 ^ (5 * L))
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))

private theorem two_mul_two_mul_right (a b : Nat) : 2 * a * (2 * b) = 4 * a * b := by
  have h : 2 * a * (2 * b) = (2 * 2) * a * b := by ac_rfl
  exact h

/-- Dyadic-block prefix exponential decay over `[1, 2^(5*L)]` for `natExceptionalCount`. -/
theorem natExceptionalCount_two_pow_exp_decay (m L : Nat) (hL : 4 * m ≤ L) :
    natExceptionalCount HasFiniteStoppingTime (2 ^ (5 * L)) * 3456 ^ m ≤
      4 * 3125 ^ m * 2 ^ (5 * L) := by
  have hle : natExceptionalCount HasFiniteStoppingTime (2 ^ (5 * L)) ≤
      exceptionalCount (2 ^ (5 * L) + 1) := by
    unfold natExceptionalCount exceptionalCount
    exact countLt_mono_pred _ (fun n _ hn => dec_true' (of_dec_true' hn).2)
  have hpow : 2 ^ (17 * m) ≤ 2 ^ (5 * L) + 1 :=
    Nat.le_trans (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)) (Nat.le_succ _)
  have hdec := exceptionalCount_exp_decay_ge m (2 ^ (5 * L) + 1) hpow
  have h2 : 1 ≤ 2 ^ (5 * L) := Nat.two_pow_pos (5 * L)
  have hmul : 2 * 3125 ^ m * (2 ^ (5 * L) + 1) ≤ 4 * 3125 ^ m * 2 ^ (5 * L) :=
    two_mul_two_mul_right (3125 ^ m) (2 ^ (5 * L)) ▸ Nat.mul_le_mul_left _ (by omega)
  exact Nat.le_trans (Nat.mul_le_mul_right _ hle) (Nat.le_trans hdec hmul)

/-- `bitLen (N + 1) ≥ 1` for every `N`. -/
theorem bitLen_pos_succ (N : Nat) : 1 ≤ bitLen (N + 1) := by
  rw [bitLen]; exact Nat.succ_pos _

/-- **Explicit Constructive Density Modulus:** `N₀(D) = 2 ^ (119 * bitLen (4 * D))`, giving
logarithmic-in-`D` exponent `m = 7 * bitLen (4 * D)` for `natExceptionalCount _ N * D < N`. -/
def explicitDensityThreshold (D : Nat) : Nat :=
  2 ^ (119 * bitLen (4 * D))

private theorem two_mul_3125_pow_7_le : 2 * 3125 ^ 7 ≤ 3456 ^ 7 := by decide

private theorem chernoff_pow_beat_bitLen (D : Nat) :
    4 * D * 3125 ^ (7 * bitLen (4 * D)) < 3456 ^ (7 * bitLen (4 * D)) := by
  let t := bitLen (4 * D)
  have h1 : 4 * D * 3125 ^ (7 * t) < 2 ^ t * 3125 ^ (7 * t) :=
    Nat.mul_lt_mul_of_pos_right (lt_two_pow_bitLen (4 * D)) (Nat.pow_pos (by decide))
  have h2 : 2 ^ t * 3125 ^ (7 * t) ≤ 3456 ^ (7 * t) := by
    rw [Nat.pow_mul 3125 7 t, ← Nat.mul_pow, Nat.pow_mul 3456 7 t]
    exact Nat.pow_le_pow_left two_mul_3125_pow_7_le t
  exact Nat.lt_of_lt_of_le h1 h2

/-- **Explicit Quantitative Modulus (Bounded Stopping Time):** for every `D > 0` and every
`N ≥ explicitDensityThreshold D`, `natExceptionalCount` for dropping within `70 * bitLen (4 * D)`
steps satisfies `count * D < N`. -/
theorem exceptionalCount_bounded_explicit_modulus (D : Nat) (_hD : 0 < D) (N : Nat)
    (hN : explicitDensityThreshold D ≤ N) :
    natExceptionalCount (fun n => HasStoppingTimeLe n (70 * bitLen (4 * D))) N * D < N := by
  let t := bitLen (4 * D); let m := 7 * t
  have h17 : 17 * m = 119 * t := by dsimp [m]; omega
  have h70 : 10 * m = 70 * t := by dsimp [m]; omega
  have hNpos : 1 ≤ N := Nat.le_trans (Nat.two_pow_pos _) hN
  have hdec := exceptionalCount_bounded_exp_decay_ge m (N + 1)
    (Nat.le_trans (by rw [h17]; exact hN) (Nat.le_succ N))
  have hle_cnt : natExceptionalCount (fun n => HasStoppingTimeLe n (70 * bitLen (4 * D))) N ≤
      countLt (fun n => @decide (¬ HasStoppingTimeLe n (10 * m))
        (Classical.propDecidable _)) (N + 1) := by
    unfold natExceptionalCount
    exact countLt_mono_pred (N + 1) (fun n _ hn => by rw [h70]; exact dec_true' (of_dec_true' hn).2)
  have h2le : 2 * 3125 ^ m * (2 * N) * D = (4 * D * 3125 ^ m) * N := by
    rw [two_mul_two_mul_right (3125 ^ m) N]; ac_rfl
  have hmul : natExceptionalCount (fun n => HasStoppingTimeLe n (70 * bitLen (4 * D))) N * D *
      3456 ^ m ≤ (4 * D * 3125 ^ m) * N := by
    calc natExceptionalCount (fun n => HasStoppingTimeLe n (70 * bitLen (4 * D))) N * D * 3456 ^ m
        = natExceptionalCount (fun n => HasStoppingTimeLe n (70 * bitLen (4 * D))) N *
            3456 ^ m * D := Nat.mul_right_comm _ D _
      _ ≤ 2 * 3125 ^ m * (N + 1) * D :=
          Nat.mul_le_mul_right D (Nat.le_trans (Nat.mul_le_mul_right _ hle_cnt) hdec)
      _ ≤ 2 * 3125 ^ m * (2 * N) * D :=
          Nat.mul_le_mul_right D (Nat.mul_le_mul_left _ (by omega : N + 1 ≤ 2 * N))
      _ = (4 * D * 3125 ^ m) * N := h2le
  have hbeat := Nat.mul_lt_mul_of_pos_right (chernoff_pow_beat_bitLen D) hNpos
  rw [Nat.mul_comm (3456 ^ m) N] at hbeat
  exact Nat.lt_of_mul_lt_mul_right (Nat.lt_of_le_of_lt hmul hbeat)

/-- **Explicit Quantitative Modulus (Finite Stopping Time):** for every `D > 0` and every
`N ≥ explicitDensityThreshold D`, `natExceptionalCount HasFiniteStoppingTime N * D < N`. -/
theorem exceptionalCount_explicit_modulus (D : Nat) (hD : 0 < D) (N : Nat)
    (hN : explicitDensityThreshold D ≤ N) :
    natExceptionalCount HasFiniteStoppingTime N * D < N := by
  have hle : natExceptionalCount HasFiniteStoppingTime N ≤
      natExceptionalCount (fun n => HasStoppingTimeLe n (70 * bitLen (4 * D))) N := by
    unfold natExceptionalCount
    refine countLt_mono_pred (N + 1) (fun n _ hn => ?_)
    have h1 := of_dec_true' hn
    exact dec_true' ⟨h1.1, fun h => h1.2 (hasFiniteStoppingTime_of_hasStoppingTimeLe h)⟩
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right D hle)
    (exceptionalCount_bounded_explicit_modulus D hD N hN)

/-- Pure-`Nat` power-saving density `1`: eventually `natExceptionalCount P N ^ b < N ^ a`. -/
def HasPowerSavingDensityOne (P : Nat → Prop) (a b : Nat) : Prop :=
  ∃ N₀ : Nat, ∀ N : Nat, N₀ ≤ N → (natExceptionalCount P N) ^ b < N ^ a

private theorem terras_two_pow_r_bound {N : Nat} (hN : 1 ≤ N) :
    let r := (bitLen (N + 1) - 1) / 119
    natExceptionalCount HasFiniteStoppingTime N * 2 ^ r ≤ 4 * N := by
  intro r; let m := 7 * r
  have hm_le : 17 * m ≤ bitLen (N + 1) - 1 := by
    have := Nat.mul_div_le (bitLen (N + 1) - 1) 119; dsimp [m, r]; omega
  have hdec := exceptionalCount_exp_decay_ge m (N + 1)
    (Nat.le_trans (Nat.pow_le_pow_right (by decide : 0 < 2) hm_le)
      (two_pow_pred_bitLen_le (Nat.succ_pos N)))
  have hle_cnt : natExceptionalCount HasFiniteStoppingTime N ≤ exceptionalCount (N + 1) := by
    unfold natExceptionalCount exceptionalCount
    exact countLt_mono_pred (N + 1) (fun n _ hn => dec_true' (of_dec_true' hn).2)
  have h2pow : 2 ^ r * 3125 ^ m ≤ 3456 ^ m := by
    dsimp [m]; rw [Nat.pow_mul 3125 7 r, ← Nat.mul_pow, Nat.pow_mul 3456 7 r]
    exact Nat.pow_le_pow_left two_mul_3125_pow_7_le r
  have hmul : natExceptionalCount HasFiniteStoppingTime N * 2 ^ r * 3125 ^ m ≤
      4 * N * 3125 ^ m := by
    rw [Nat.mul_assoc, Nat.mul_right_comm 4 N (3125 ^ m), ← two_mul_two_mul_right (3125 ^ m) N]
    exact Nat.le_trans (Nat.mul_le_mul hle_cnt h2pow)
      (Nat.le_trans hdec (Nat.mul_le_mul_left _ (by omega : N + 1 ≤ 2 * N)))
  exact Nat.le_of_mul_le_mul_right hmul (Nat.pow_pos (by decide))

private theorem terras_pow119_bound {N : Nat} (hN : 1 ≤ N) :
    (natExceptionalCount HasFiniteStoppingTime N) ^ 119 ≤ (2 ^ 119) ^ 3 * N ^ 118 := by
  let c := natExceptionalCount HasFiniteStoppingTime N
  let b := bitLen (N + 1); let r := (b - 1) / 119
  have hpow119 : c ^ 119 * 2 ^ (119 * r) ≤ 2 ^ 238 * N ^ 119 := by
    have h1 := Nat.pow_le_pow_left (terras_two_pow_r_bound hN) 119
    rwa [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm _ 119,
      show 4 ^ 119 = 2 ^ 238 by decide] at h1
  have hb_pos : 1 ≤ b := bitLen_pos_succ N
  have hb_lt : b < 119 * r + 120 := by
    have := Nat.lt_div_mul_add (by decide : 0 < 119) (a := b - 1); dsimp [r]; omega
  have hN_lt : N < 2 ^ (119 * r + 119) := by
    have hlt : N + 1 < 2 ^ b := lt_two_pow_bitLen (N + 1)
    have hle : 2 ^ b ≤ 2 ^ (119 * r + 119) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    omega
  have h2pow3 : 2 ^ 119 * 2 ^ 238 = (2 ^ 119) ^ 3 := by
    rw [show 238 = 119 * 2 by decide, Nat.pow_mul, ← Nat.pow_succ']
  have hmulN : c ^ 119 * N ≤ (2 ^ 119) ^ 3 * N ^ 119 := by
    calc c ^ 119 * N ≤ c ^ 119 * 2 ^ (119 * r + 119) := Nat.mul_le_mul_left _ (Nat.le_of_lt hN_lt)
      _ = 2 ^ 119 * (c ^ 119 * 2 ^ (119 * r)) := by rw [Nat.pow_add]; ac_rfl
      _ ≤ 2 ^ 119 * (2 ^ 238 * N ^ 119) := Nat.mul_le_mul_left _ hpow119
      _ = (2 ^ 119) ^ 3 * N ^ 119 := by rw [← Nat.mul_assoc, h2pow3]
  rw [show N ^ 119 = N ^ 118 * N by rw [Nat.pow_succ], ← Nat.mul_assoc] at hmulN
  exact Nat.le_of_mul_le_mul_right hmulN hN

/-- **Unconditional Power-Saving Exceptional Bound:** for all `N ≥ 2^(5 * 143) = 2^715`, the
exceptional set for `HasFiniteStoppingTime` satisfies `count^238 < N^237` (`O(N^(237/238))`). -/
theorem terras_power_saving_explicit (N : Nat) (hN : 2 ^ (5 * 143) ≤ N) :
    (natExceptionalCount HasFiniteStoppingTime N) ^ 238 < N ^ 237 := by
  have hNpos : 1 ≤ N := Nat.le_trans (Nat.two_pow_pos _) hN
  have hsq : (natExceptionalCount HasFiniteStoppingTime N) ^ 238 ≤
      ((2 ^ 119) ^ 3) ^ 2 * N ^ 236 := by
    have h1 := Nat.pow_le_pow_left (terras_pow119_bound hNpos) 2
    rwa [← Nat.pow_mul _ 119 2, Nat.mul_pow, ← Nat.pow_mul N 118 2] at h1
  have hexp : 119 * (3 * 2) < 5 * 143 := by decide
  have h714 : ((2 ^ 119) ^ 3) ^ 2 < N := by
    have hlt := Nat.pow_lt_pow_right (by decide : 1 < 2) hexp
    rw [Nat.pow_mul 2 119 (3 * 2), Nat.pow_mul (2 ^ 119) 3 2] at hlt
    exact Nat.lt_of_lt_of_le hlt hN
  rw [show N ^ 237 = N * N ^ 236 by rw [Nat.pow_succ, Nat.mul_comm]]
  exact Nat.lt_of_le_of_lt hsq (Nat.mul_lt_mul_of_pos_right h714 (Nat.pow_pos hNpos))

/-- Unconditional Terras-Chernoff power-saving density `1`:
`HasPowerSavingDensityOne HasFiniteStoppingTime 237 238`. -/
theorem terras_power_saving_density :
    HasPowerSavingDensityOne HasFiniteStoppingTime 237 238 :=
  ⟨2 ^ (5 * 143), terras_power_saving_explicit⟩

/-! ### 3. Exact Track A Equivalence with Frozen `Challenge.lean` -/

/-- `0` never has a finite stopping time (`collatzIter k 0 = 0`). -/
theorem not_hasFiniteStoppingTime_zero : ¬ HasFiniteStoppingTime 0 := fun ⟨_, _, hlt⟩ => by omega

/-- `1` never has a finite stopping time (`1 → 4 → 2 → 1` stays positive). -/
theorem not_hasFiniteStoppingTime_one : ¬ HasFiniteStoppingTime 1 :=
  fun ⟨k, _, hlt⟩ => by have := collatzIter_pos k (by decide : 0 < 1); omega

/-- **Track A Equivalence (`Challenge.lean`):** `CollatzConjecture` holds iff every `n ≥ 2` has
a finite stopping time. -/
theorem collatzConjecture_iff_forall_finiteStoppingTime :
    CollatzConjecture ↔ ∀ n : Nat, 2 ≤ n → HasFiniteStoppingTime n := by
  constructor
  · intro hconj n hn; rcases hconj n (by omega) with ⟨k, hk⟩
    cases k with
    | zero => simp only [collatzIter] at hk; omega
    | succ k' => exact ⟨k' + 1, Nat.succ_pos k', by omega⟩
  · intro hstop; rw [collatzConjecture_iff_orbitMinLe_one]
    exact fun n _ => orbitMinLe_of_le_below (fun m hm1 _ => hstop m (by omega))

/-- `natExceptionalCount P N = 0` iff `P n` holds for all `1 ≤ n ≤ N`. -/
theorem natExceptionalCount_eq_zero_iff (P : Nat → Prop) (N : Nat) :
    natExceptionalCount P N = 0 ↔ ∀ n : Nat, 1 ≤ n → n ≤ N → P n := by
  induction N with
  | zero => exact ⟨fun _ n hn1 hn0 => by omega, fun _ => by simp [natExceptionalCount, countLt]⟩
  | succ N ih =>
    unfold natExceptionalCount at ih ⊢; rw [countLt]
    by_cases hP : P (N + 1)
    · rw [dec_false' (fun h => h.2 hP), ite_eq_right (by decide), Nat.add_zero, ih]
      refine ⟨fun h n hn1 hnle => ?_, fun h n hn1 hnle => h n hn1 (Nat.le_succ_of_le hnle)⟩
      rcases Nat.eq_or_lt_of_le hnle with rfl | hlt
      · exact hP
      · exact h n hn1 (Nat.lt_succ_iff.mp hlt)
    · rw [dec_true' ⟨Nat.succ_pos N, hP⟩, ite_eq_left rfl]
      exact ⟨fun h => by omega, fun h => absurd (h (N + 1) (Nat.succ_pos N) (Nat.le_refl _)) hP⟩

/-- Because `¬ HasFiniteStoppingTime 1`, `natExceptionalCount HasFiniteStoppingTime N ≥ 1` for
every `N ≥ 1`. -/
theorem natExceptionalCount_hasFiniteStoppingTime_pos {N : Nat} (hN : 1 ≤ N) :
    1 ≤ natExceptionalCount HasFiniteStoppingTime N := by
  by_cases h0 : natExceptionalCount HasFiniteStoppingTime N = 0
  · exact absurd ((natExceptionalCount_eq_zero_iff _ N).mp h0 1 (Nat.le_refl 1) hN)
      not_hasFiniteStoppingTime_one
  · omega

/-- **Empty Exceptional Set Equivalence:** `CollatzConjecture` holds iff the exceptional set for
`n ≤ 1 ∨ HasFiniteStoppingTime n` is empty on every `[1, N]`. -/
theorem collatzConjecture_iff_empty_exceptional_set :
    CollatzConjecture ↔
      ∀ N : Nat, natExceptionalCount (fun n => n ≤ 1 ∨ HasFiniteStoppingTime n) N = 0 := by
  rw [collatzConjecture_iff_forall_finiteStoppingTime]; constructor
  · intro h N; rw [natExceptionalCount_eq_zero_iff]; intro n _ _
    by_cases hn : n ≤ 1; exact Or.inl hn; exact Or.inr (h n (by omega))
  · intro h N hN
    rcases (natExceptionalCount_eq_zero_iff _ N).mp (h N) N (by omega) (Nat.le_refl N) with
      hle | hstop; omega; exact hstop

/-- **Exact-One Exceptional Count Equivalence:** `CollatzConjecture` holds iff for every `N ≥ 1`,
`n = 1` is the sole exception in `[1, N]`. -/
theorem collatzConjecture_iff_natExceptionalCount_eq_one :
    CollatzConjecture ↔ ∀ N : Nat, 1 ≤ N → natExceptionalCount HasFiniteStoppingTime N = 1 := by
  rw [collatzConjecture_iff_forall_finiteStoppingTime]; constructor
  · intro hstop N hN; induction N with
    | zero => omega
    | succ N ih => cases N with
      | zero =>
        unfold natExceptionalCount
        rw [countLt, countLt, dec_false' (fun h => by have := h.1; omega),
          dec_true' ⟨Nat.le_refl 1, not_hasFiniteStoppingTime_one⟩]; rfl
      | succ k =>
        have hih := ih (Nat.succ_pos k); unfold natExceptionalCount at hih ⊢
        rw [countLt, hih, dec_false' (fun h => h.2 (hstop (k + 2) (by omega)))]; rfl
  · intro hcnt n hn; have hnn := hcnt n (by omega)
    by_cases hstop : HasFiniteStoppingTime n; exact hstop
    exfalso; have hge1 := natExceptionalCount_hasFiniteStoppingTime_pos (by omega : 1 ≤ n - 1)
    have heq : n = (n - 1) + 1 := by omega
    have hstop' : ¬ HasFiniteStoppingTime ((n - 1) + 1) := by rwa [← heq]
    have hstep : natExceptionalCount HasFiniteStoppingTime n =
        natExceptionalCount HasFiniteStoppingTime (n - 1) + 1 := by
      conv => lhs; rw [heq]; unfold natExceptionalCount
      rw [countLt, dec_true' ⟨Nat.succ_pos _, hstop'⟩]; rfl
    omega

/-! ### 4. Formal `PROVE-A1` Quantitative Density-vs-Universality Obstruction -/

/-- A predicate `P` has subpolynomial exceptional set (`o(N^(a/b))` for every `a, b > 0`). -/
def HasSubpolyExceptionalSet (P : Nat → Prop) : Prop :=
  ∀ a b : Nat, 0 < a → 0 < b → HasPowerSavingDensityOne P a b

/-- Any power-saving bound `N^(a/b)` (`0 < a < b`) implies `HasNaturalDensityOne`. -/
theorem hasNaturalDensityOne_of_powerSaving {P : Nat → Prop} {a b : Nat}
    (_ha : 0 < a) (hab : a < b) (h : HasPowerSavingDensityOne P a b) :
    HasNaturalDensityOne P := by
  intro D hD; rcases h with ⟨N₀, hN₀⟩; refine ⟨max N₀ (D ^ b), fun N hN => ?_⟩
  have hNpos : 0 < N :=
    Nat.lt_of_lt_of_le (Nat.pow_pos hD) (Nat.le_trans (Nat.le_max_right _ _) hN)
  have hmul : (natExceptionalCount P N * D) ^ b < N ^ a * D ^ b := by
    rw [Nat.mul_pow]
    exact Nat.mul_lt_mul_of_pos_right
      (hN₀ N (Nat.le_trans (Nat.le_max_left _ _) hN)) (Nat.pow_pos hD)
  have hDb : N ^ a * D ^ b ≤ N ^ b := by
    calc N ^ a * D ^ b ≤ N ^ a * N := Nat.mul_le_mul_left _ (Nat.le_trans (Nat.le_max_right _ _) hN)
      _ = N ^ (a + 1) := (Nat.pow_succ N a).symm
      _ ≤ N ^ b := Nat.pow_le_pow_right hNpos hab
  have hlt := Nat.lt_of_lt_of_le hmul hDb
  exact Nat.lt_of_not_ge (fun hge => Nat.not_lt_of_ge (Nat.pow_le_pow_left hge b) hlt)

/-- Any power-saving bound `N^(a/b)` (`0 < a < b`) implies `HasLogDensityOne`. -/
theorem hasLogDensityOne_of_powerSaving {P : Nat → Prop} {a b : Nat}
    (ha : 0 < a) (hab : a < b) (h : HasPowerSavingDensityOne P a b) : HasLogDensityOne P :=
  hasLogDensityOne_of_hasNaturalDensityOne (hasNaturalDensityOne_of_powerSaving ha hab h)

/-- `HasSubpolyExceptionalSet P` is equivalent to beating `N^(1/k)` for every `k ≥ 1`. -/
theorem hasSubpolyExceptionalSet_iff_pow_lt (P : Nat → Prop) :
    HasSubpolyExceptionalSet P ↔
      ∀ k : Nat, 1 ≤ k → ∃ N₀ : Nat, ∀ N : Nat, N₀ ≤ N → (natExceptionalCount P N) ^ k < N := by
  constructor
  · intro h k hk; rcases h 1 k (by decide) hk with ⟨N₀, hN₀⟩
    exact ⟨N₀, fun N hN => by simpa using hN₀ N hN⟩
  · intro h a b ha hb; rcases h b hb with ⟨N₀, hN₀⟩; refine ⟨max N₀ 1, fun N hN => ?_⟩
    have hlt := hN₀ N (Nat.le_trans (Nat.le_max_left _ _) hN)
    have hpow : N ≤ N ^ a := by
      calc N = N ^ 1 := (Nat.pow_one N).symm
        _ ≤ N ^ a := Nat.pow_le_pow_right (Nat.le_trans (Nat.le_max_right _ _) hN) ha
    exact Nat.lt_of_lt_of_le hlt hpow

/-- `E` is `O(log N)` sparse (`IsExpSparse`) if `|E ∩ [1, N]| ≤ C * bitLen (N + 1)` for all `N`.
-/
def IsExpSparse (E : Nat → Prop) : Prop :=
  ∃ C : Nat, ∀ N : Nat, natExceptionalCount (fun n => ¬ E n) N ≤ C * bitLen (N + 1)

private theorem countLt_eq_le_one (a L : Nat) : countLt (fun n => decide (n = a)) L ≤ 1 := by
  have hz : ∀ m, m ≤ a → countLt (fun n => decide (n = a)) m = 0 := fun m hm => by
    induction m with
    | zero => rfl
    | succ k ih => rw [countLt, ih (by omega), decide_eq_false (by omega)]; rfl
  induction L with | zero => exact Nat.zero_le 1 | succ L ih =>
    rw [countLt]; by_cases h : L = a
    · subst h; rw [hz L (Nat.le_refl L)]; simp
    · rw [decide_eq_false h]; exact ih

/-- Any image `{f t | t < M}` contains at most `M` elements below `L`. -/
theorem countLt_image_lt_le (f : Nat → Nat) (M L : Nat) :
    countLt (fun n => @decide (∃ t : Nat, t < M ∧ n = f t) (Classical.propDecidable _)) L ≤ M := by
  induction M with
  | zero =>
    have h0 := countLt_mono_pred L (q := fun _ => false)
      (p := fun n => @decide (∃ t : Nat, t < 0 ∧ n = f t) (Classical.propDecidable _))
      (fun _ _ hi => by rcases of_dec_true' hi with ⟨t, ht, _⟩; omega)
    have hz : countLt (fun _ => false) L = 0 := by
      clear h0; induction L with | zero => rfl | succ m ihm => simp [countLt, ihm]
    omega
  | succ M ih =>
    have hor := countLt_or_le
      (fun n => @decide (∃ t : Nat, t < M ∧ n = f t) (Classical.propDecidable _))
      (fun n => decide (n = f M)) L
    have hmono : countLt (fun n => @decide (∃ t : Nat, t < M + 1 ∧ n = f t)
        (Classical.propDecidable _)) L ≤ countLt (fun n => @decide (∃ t : Nat, t < M ∧
          n = f t) (Classical.propDecidable _) || decide (n = f M)) L := by
      refine countLt_mono_pred L (fun _ _ hi => ?_); rcases of_dec_true' hi with ⟨t, ht, rfl⟩
      by_cases htM : t < M
      · rw [Bool.or_eq_true, dec_true' ⟨t, htM, rfl⟩]; exact Or.inl rfl
      · have heq : t = M := by omega
        simp [heq]
    have hc := countLt_eq_le_one (f M) L; omega

/-- Every finite list `S` contributes at most `S.length` exceptions in `[1, N]`. -/
theorem natExceptionalCount_mem_list_le (S : List Nat) (N : Nat) :
    natExceptionalCount (fun n => n ∉ S) N ≤ S.length := by
  have hmono : natExceptionalCount (fun n => n ∉ S) N ≤
      countLt (fun n => @decide (∃ t : Nat, t < S.length ∧ n = S.getD t 0)
        (Classical.propDecidable _)) (N + 1) := by
    unfold natExceptionalCount; refine countLt_mono_pred (N + 1) (fun n _ hn => ?_)
    have hmem : n ∈ S := Classical.byContradiction (fun hnot => (of_dec_true' hn).2 hnot)
    rcases List.getElem_of_mem hmem with ⟨t, ht, rfl⟩
    exact dec_true' ⟨t, ht, by simp [List.getD, ht]⟩
  exact Nat.le_trans hmono (countLt_image_lt_le (fun t => S.getD t 0) S.length (N + 1))

/-- Every finite list defines an `IsExpSparse` set (`O(1) ≤ C * bitLen (N + 1)`). -/
theorem isExpSparse_of_finite (S : List Nat) : IsExpSparse (fun n => n ∈ S) :=
  ⟨S.length, fun N => Nat.le_trans (natExceptionalCount_mem_list_le S N)
    (Nat.le_mul_of_pos_right S.length (bitLen_pos_succ N))⟩

/-- Any putative cycle orbit `cycleOrbitList n L` is `IsExpSparse`. -/
theorem isExpSparse_cycleOrbitList (n L : Nat) : IsExpSparse (fun m => m ∈ cycleOrbitList n L) :=
  isExpSparse_of_finite (cycleOrbitList n L)

/-- Any exponentially growing sequence `a` (`∀ t, 2 ^ (t / C) ≤ a t` with `1 ≤ C`) hits at
most `C * bitLen (N + 1)` integers in `[1, N]`. -/
theorem natExceptionalCount_exp_seq_le (a : Nat → Nat) {C : Nat} (hC : 1 ≤ C)
    (ha : ∀ t : Nat, 2 ^ (t / C) ≤ a t) (N : Nat) :
    natExceptionalCount (fun m => ¬ ∃ t : Nat, a t = m) N ≤ C * bitLen (N + 1) := by
  have hmono : natExceptionalCount (fun m => ¬ ∃ t : Nat, a t = m) N ≤
      countLt (fun m => @decide (∃ t : Nat, t < C * bitLen (N + 1) ∧ m = a t)
        (Classical.propDecidable _)) (N + 1) := by
    unfold natExceptionalCount; refine countLt_mono_pred (N + 1) (fun m hm hm_dec => ?_)
    rcases Classical.byContradiction (fun hnot => (of_dec_true' hm_dec).2 hnot) with ⟨t, ht⟩
    have hpow : 2 ^ (t / C) < 2 ^ bitLen (N + 1) :=
      Nat.lt_of_le_of_lt (Nat.le_trans (ha t) (by omega)) (lt_two_pow_bitLen (N + 1))
    have hdiv_lt : t / C < bitLen (N + 1) :=
      Nat.lt_of_not_ge (fun h => absurd (Nat.pow_le_pow_right (by decide : 0 < 2) h) (by omega))
    have h1 := Nat.lt_div_mul_add hC (a := t)
    have h2 := Nat.mul_le_mul_left C hdiv_lt
    rw [Nat.mul_succ, Nat.mul_comm C (t / C)] at h2
    exact dec_true' ⟨t, by omega, ht.symm⟩
  exact Nat.le_trans hmono (countLt_image_lt_le a (C * bitLen (N + 1)) (N + 1))

/-- Every exponentially growing sequence `a` (`∀ t, 2 ^ (t / C) ≤ a t`) defines an `IsExpSparse`
set. -/
theorem isExpSparse_of_exp_seq (a : Nat → Nat) {C : Nat} (hC : 1 ≤ C)
    (ha : ∀ t : Nat, 2 ^ (t / C) ≤ a t) : IsExpSparse (fun m => ∃ t : Nat, a t = m) :=
  ⟨C, natExceptionalCount_exp_seq_le a hC ha⟩

/-- Any doubling sequence `∀ t, 2 ^ t ≤ a t` has `≤ bitLen (N + 1)` elements in `[1, N]` and is
`IsExpSparse`. -/
theorem isExpSparse_of_doubling_seq (a : Nat → Nat) (ha : ∀ t : Nat, 2 ^ t ≤ a t) :
    IsExpSparse (fun m => ∃ t : Nat, a t = m) :=
  isExpSparse_of_exp_seq a (C := 1) (by decide) (fun t => by simpa using ha t)

private theorem lt_two_pow_self' : ∀ n : Nat, n < 2 ^ n
  | 0 => by decide
  | n + 1 => by have := lt_two_pow_self' n; rw [Nat.pow_succ]; omega

/-- Any orbit satisfying `∀ t, 2 ^ (t / C) ≤ collatzIter t n` (`1 ≤ C`, `0 < n`) is a
genuine divergent orbit (`HasDivergentOrbit`). -/
theorem hasDivergentOrbit_of_exp_growth {n C : Nat} (hC : 1 ≤ C) (hn : 0 < n)
    (hexp : ∀ t : Nat, 2 ^ (t / C) ≤ collatzIter t n) : HasDivergentOrbit := by
  refine ⟨n, hn, fun B => ⟨C * B, ?_⟩⟩
  have hdiv : C * B / C = B := by rw [Nat.mul_comm C B]; exact Nat.mul_div_cancel B hC
  have hlt := lt_two_pow_self' B
  have hge := hexp (C * B); rw [hdiv] at hge; omega

private theorem linear_lt_two_pow_ge' (x r : Nat) (hr : x + 4 ≤ r) : r * x < 2 ^ r := by
  have hbase : (x + 4) * x < 2 ^ (x + 4) := by
    have h2x : ∀ k : Nat, 2 * k + 5 ≤ 2 ^ (k + 4) := fun k => by
      induction k with | zero => decide | succ k ih => rw [Nat.pow_succ]; omega
    induction x with | zero => decide | succ x ih =>
      have := h2x x; rw [show x + 1 + 4 = (x + 4) + 1 by omega, Nat.pow_succ,
        Nat.add_mul, Nat.mul_add, Nat.one_mul]; omega
  induction hr with | refl => exact hbase | @step k hk ih =>
    have h1 := Nat.le_mul_of_pos_left x (Nat.le_trans (by omega : 1 ≤ x + 4) hk)
    rw [Nat.succ_mul, Nat.pow_succ]; omega

private theorem log_bound_pow_lt_N (C k N : Nat) (hk : 1 ≤ k)
    (hN : 2 ^ (k * (2 * (C + 1) * (k + 1) + 4) + 1) ≤ N) :
    (C * bitLen (N + 1)) ^ k < N := by
  let A := 2 * (C + 1) * (k + 1); let b := bitLen (N + 1)
  have hbit : k * (A + 4) + 2 ≤ b := by
    have hlt : N + 1 < 2 ^ b := lt_two_pow_bitLen (N + 1)
    refine Nat.le_of_not_lt (fun h => ?_)
    have hle : b ≤ k * (2 * (C + 1) * (k + 1) + 4) + 1 := by dsimp [A] at h; omega
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hle; omega
  let r := b - 1; let s := (r - 1) / k
  have hs_ge : A + 4 ≤ s := (Nat.le_div_iff_mul_le hk).mpr (by rw [Nat.mul_comm]; omega)
  have hr_lt : r - 1 < k * (s + 1) := by
    dsimp [s]; rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm k]; exact Nat.lt_div_mul_add hk
  have hb_le_As : C * b ≤ A * s := by
    have hs1 : 1 ≤ s := by omega
    have hb_le : b ≤ 2 * (k + 1) * s := by
      have hks : k ≤ k * s := Nat.le_mul_of_pos_right k hs1
      have hbk : b ≤ k * s + k + 2 := by rw [Nat.mul_add, Nat.mul_one] at hr_lt; omega
      rw [Nat.mul_add 2 k 1, Nat.mul_one, Nat.add_mul, Nat.mul_assoc 2 k s]; omega
    calc C * b ≤ (C + 1) * b := Nat.mul_le_mul_right b (Nat.le_succ C)
      _ ≤ (C + 1) * (2 * (k + 1) * s) := Nat.mul_le_mul_left _ hb_le
      _ = A * s := by dsimp [A]; ac_rfl
  have hpow_lt : (C * b) ^ k < 2 ^ (k * s) := by
    rw [Nat.mul_comm k s, Nat.pow_mul]
    exact Nat.pow_lt_pow_left
      (Nat.lt_of_le_of_lt hb_le_As (by rw [Nat.mul_comm]; exact linear_lt_two_pow_ge' A s hs_ge))
      (Nat.ne_of_gt hk)
  have h2_le_N : 2 ^ (r - 1) ≤ N := by
    have h2r : 2 ^ r ≤ N + 1 := two_pow_pred_bitLen_le (Nat.succ_pos N)
    have hN1 : 1 ≤ N := Nat.le_trans (Nat.two_pow_pos _) hN
    have hpow2 : 2 ^ r = 2 * 2 ^ (r - 1) := by
      conv => lhs; rw [show r = (r - 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    omega
  exact Nat.lt_of_lt_of_le hpow_lt (Nat.le_trans (Nat.pow_le_pow_right (by decide : 0 < 2)
    (by have := Nat.mul_div_le (r - 1) k; dsimp [s]; omega)) h2_le_N)

/-- **Sparsity Beats Every Power-Saving Bound (`PROVE-A1`):** every `IsExpSparse` set `E` has
complement satisfying `HasSubpolyExceptionalSet (fun n => ¬ E n)`. -/
theorem isExpSparse_hasSubpoly {E : Nat → Prop} (hE : IsExpSparse E) :
    HasSubpolyExceptionalSet (fun n => ¬ E n) := by
  rw [hasSubpolyExceptionalSet_iff_pow_lt]; rcases hE with ⟨C, hC⟩; intro k hk
  exact ⟨2 ^ (k * (2 * (C + 1) * (k + 1) + 4) + 1), fun N hN =>
    Nat.lt_of_le_of_lt (Nat.pow_le_pow_left (hC N) k) (log_bound_pow_lt_N C k N hk hN)⟩

private theorem natExceptionalCount_and_le (P Q : Nat → Prop) (N : Nat) :
    natExceptionalCount (fun n => P n ∧ Q n) N ≤
      natExceptionalCount P N + natExceptionalCount Q N := by
  unfold natExceptionalCount
  refine Nat.le_trans (countLt_mono_pred (N + 1) (fun n _ hn => ?_)) (countLt_or_le
    (fun n => @decide (1 ≤ n ∧ ¬ P n) (Classical.propDecidable _))
    (fun n => @decide (1 ≤ n ∧ ¬ Q n) (Classical.propDecidable _)) (N + 1))
  rcases of_dec_true' hn with ⟨hn1, hnot⟩; rw [Bool.or_eq_true]
  by_cases hP : P n
  · exact Or.inr (dec_true' ⟨hn1, fun hq => hnot ⟨hP, hq⟩⟩)
  · exact Or.inl (dec_true' ⟨hn1, hP⟩)

private theorem natExceptionalCount_and_pow_lt {P Q : Nat → Prop} {k M N : Nat}
    (hP : (natExceptionalCount P N) ^ k < M) (hQ : (natExceptionalCount Q N) ^ k < M) :
    (natExceptionalCount (fun n => P n ∧ Q n) N) ^ k < 2 ^ k * M := by
  let mx := max (natExceptionalCount P N) (natExceptionalCount Q N)
  have hmx : mx ^ k < M := by
    by_cases h : natExceptionalCount P N ≤ natExceptionalCount Q N
    · simpa [mx, Nat.max_eq_right h] using hQ
    · simpa [mx, Nat.max_eq_left (Nat.le_of_not_le h)] using hP
  have hsum : natExceptionalCount (fun n => P n ∧ Q n) N ≤ 2 * mx := by
    have := natExceptionalCount_and_le P Q N
    have := Nat.le_max_left (natExceptionalCount P N) (natExceptionalCount Q N)
    have := Nat.le_max_right (natExceptionalCount P N) (natExceptionalCount Q N); omega
  exact Nat.lt_of_le_of_lt (Nat.pow_le_pow_left hsum k)
    (Nat.mul_pow 2 mx k ▸ Nat.mul_lt_mul_of_pos_left hmx (Nat.two_pow_pos k))

/-- Combining a power-saving bound `N^(a/b)` with any `IsExpSparse` set preserves a
power-saving bound `N^((2a+1)/(2b))` (if `a < b`, then `2a+1 < 2b` still holds!). -/
theorem hasPowerSaving_and_expSparse {P E : Nat → Prop} {a b : Nat}
    (_ha : 0 < a) (_hb : 0 < b) (hP : HasPowerSavingDensityOne P a b) (hE : IsExpSparse E) :
    HasPowerSavingDensityOne (fun n => P n ∧ ¬ E n) (2 * a + 1) (2 * b) := by
  rcases hP with ⟨N₁, hN₁⟩
  rcases (hasSubpolyExceptionalSet_iff_pow_lt _).mp (isExpSparse_hasSubpoly hE) (2 * b)
    (by omega) with ⟨N₂, hN₂⟩
  refine ⟨max (max N₁ N₂) (2 ^ (2 * b) + 1), fun N hN => ?_⟩
  have hNpos := Nat.lt_of_lt_of_le (Nat.succ_pos _) (Nat.le_trans (Nat.le_max_right _ _) hN)
  have h1 : (natExceptionalCount P N) ^ (2 * b) < N ^ (2 * a) := by
    have hp := hN₁ N (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_left _ _) hN))
    rw [Nat.mul_comm 2 b, Nat.pow_mul, Nat.mul_comm 2 a, Nat.pow_mul]
    exact Nat.pow_lt_pow_left hp (by decide)
  have h2 : (natExceptionalCount (fun n => ¬ E n) N) ^ (2 * b) < N ^ (2 * a) := Nat.lt_of_lt_of_le
    (hN₂ N (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_left _ _) hN)))
    (Nat.le_trans (by simp) (Nat.pow_le_pow_right hNpos (by omega : 1 ≤ 2 * a)))
  have hNbig : 2 ^ (2 * b) < N := by have := Nat.le_trans (Nat.le_max_right _ _) hN; omega
  rw [Nat.pow_succ, Nat.mul_comm (N ^ (2 * a)) N]
  exact Nat.lt_of_lt_of_le (natExceptionalCount_and_pow_lt h1 h2)
    (Nat.le_of_lt (Nat.mul_lt_mul_of_pos_right hNbig (Nat.pow_pos hNpos)))

/-- **Closure Under `IsExpSparse` Exceptions:** `HasSubpolyExceptionalSet P` still permits
excluding any `IsExpSparse` set `E` without losing subpolynomial exceptional-set decay. -/
theorem hasSubpoly_and_expSparse {P E : Nat → Prop} (hP : HasSubpolyExceptionalSet P)
    (hE : IsExpSparse E) : HasSubpolyExceptionalSet (fun n => P n ∧ ¬ E n) := by
  intro a b ha hb
  rcases hP a (2 * b) ha (by omega) with ⟨N₁, hN₁⟩
  rcases isExpSparse_hasSubpoly hE a (2 * b) ha (by omega) with ⟨N₂, hN₂⟩
  refine ⟨max (max N₁ N₂) (2 ^ (2 * b)), fun N hN => ?_⟩
  have h1 := hN₁ N (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_left _ _) hN))
  have h2 := hN₂ N (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_left _ _) hN))
  have hNpos := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) (Nat.le_trans (Nat.le_max_right _ _) hN)
  have hN2b : 2 ^ (2 * b) ≤ N ^ a := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) hN)
    (Nat.le_trans (by simp) (Nat.pow_le_pow_right hNpos ha))
  have hsq : (natExceptionalCount (fun n => P n ∧ ¬ E n) N ^ b) ^ 2 < (N ^ a) ^ 2 := by
    rw [← Nat.pow_mul, Nat.mul_comm b 2]
    exact Nat.lt_of_lt_of_le (natExceptionalCount_and_pow_lt h1 h2)
      (by rw [Nat.pow_two]; exact Nat.mul_le_mul_right (N ^ a) hN2b)
  exact Nat.lt_of_not_ge (fun hge => Nat.not_lt_of_ge (Nat.pow_le_pow_left hge 2) hsq)

/-- **Quantitative Density-vs-Universality Gap (`PROVE-A1`):** even `HasSubpolyExceptionalSet`
(beating every `N^(a/b)`) does NOT imply `∀ n ≥ 1, P n` (e.g., powers of `2`). -/
theorem powerSaving_not_implies_forall :
    ∃ P : Nat → Prop, HasSubpolyExceptionalSet P ∧ ∀ M : Nat, ∃ n : Nat, M ≤ n ∧ ¬ P n := by
  have hexp : IsExpSparse (fun m => ∃ t : Nat, 2 ^ t = m) :=
    isExpSparse_of_doubling_seq (fun t => 2 ^ t) (fun _ => Nat.le_refl _)
  refine ⟨fun m => ¬ ∃ t : Nat, 2 ^ t = m, isExpSparse_hasSubpoly hexp, fun M => ⟨2 ^ M, ?_,
    fun h => h ⟨M, rfl⟩⟩⟩
  have hlt := lt_two_pow_self' M; omega

/-- **Cycle Obstruction (`Barrier 4`):** unconditional Terras power-saving `O(N^(237/238))`
decay (`HasPowerSavingDensityOne _ 237 238`) still permits excluding any cycle `cycleOrbitList`. -/
theorem terras_powerSaving_allows_cycle (n L : Nat) :
    HasPowerSavingDensityOne
      (fun m => HasFiniteStoppingTime m ∧ m ∉ cycleOrbitList n L) 475 476 :=
  hasPowerSaving_and_expSparse (by decide) (by decide)
    terras_power_saving_density (isExpSparse_cycleOrbitList n L)

/-- **Divergent-Orbit Obstruction (`Barrier 5`):** unconditional Terras power-saving decay
`O(N^(237/238))` still permits excluding any exponentially divergent orbit. -/
theorem terras_powerSaving_allows_expDivergent {n C : Nat} (hC : 1 ≤ C)
    (hexp : ∀ t : Nat, 2 ^ (t / C) ≤ collatzIter t n) :
    HasPowerSavingDensityOne
      (fun m => HasFiniteStoppingTime m ∧ ¬ ∃ t : Nat, collatzIter t n = m) 475 476 :=
  hasPowerSaving_and_expSparse (by decide) (by decide)
    terras_power_saving_density (isExpSparse_of_exp_seq (fun t => collatzIter t n) hC hexp)

/-- **Subpolynomial Cycle Obstruction (`Barriers 4 & 5`):** even a hypothetical proof of
`HasSubpolyExceptionalSet P` (beating every `N^(1-δ)`) still permits excluding any finite cycle
orbit `cycleOrbitList n L`. -/
theorem subpoly_allows_cycle {P : Nat → Prop} (hP : HasSubpolyExceptionalSet P) (n L : Nat) :
    HasSubpolyExceptionalSet (fun m => P m ∧ m ∉ cycleOrbitList n L) :=
  hasSubpoly_and_expSparse hP (isExpSparse_cycleOrbitList n L)

/-- **Subpolynomial Divergent-Orbit Obstruction (`Barriers 4 & 5`):** even a hypothetical proof
of `HasSubpolyExceptionalSet P` still permits excluding an entire exponentially divergent
Collatz orbit `{collatzIter t n | 2^(t/C) ≤ collatzIter t n}`. -/
theorem subpoly_allows_expDivergent {P : Nat → Prop} (hP : HasSubpolyExceptionalSet P)
    {n C : Nat} (hC : 1 ≤ C) (hexp : ∀ t : Nat, 2 ^ (t / C) ≤ collatzIter t n) :
    HasSubpolyExceptionalSet (fun m => P m ∧ ¬ ∃ t : Nat, collatzIter t n = m) :=
  hasSubpoly_and_expSparse hP (isExpSparse_of_exp_seq (fun t => collatzIter t n) hC hexp)

end SolveCollatz
