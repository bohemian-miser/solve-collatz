/-
Copyright (c) 2026 The solve-collatz contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Collatz.Known.CycleLengthBounds
public import Collatz.Prove.Automata.SieveObstruction

/-!
# Unconditional Eliahou Cycle-Length Lower Bound via Continued Fractions (`KNOWN-003` Phase 2)

Formalization in pure Lean 4 core (zero Mathlib, zero `sorry`, zero `native_decide`):
1. Unconditional kernel-verified finite stopping time for all `2 ≤ n < 32768`, lifting
   `SieveObstruction.mod4096_covered_finiteStoppingTime` (`3870 / 4096` covered) by checking only
   the `7 * 226 = 1582` uncovered residues in `[4096, 32768)` (`≤ 105` Terras steps).
2. Exact continued-fraction convergents & semiconvergents of `log₂(3)` in pure `Nat`, Farey
   adjacency determinant `p_{i+1} q_i - p_i q_{i+1} = ±1`, best rational approximation bounds,
   and an `O(1)` parametric Eliahou continued-fraction elimination theorem.
3. **Unconditional Flagship Bounds (ZERO external hypotheses):** every non-trivial positive
   `SyracuseCycle` satisfies `32768 ≤ n_min`, `306 ≤ C.k`, `485 ≤ C.totalVal`, and
   `791 ≤ C.collatzLen`, bridged directly to frozen `Challenge.HasNontrivialCycle`.
4. Sharp conditional CF lifting for `M = 10^6` (`K ≥ 2966`, `S ≥ 4701`, `L ≥ 7667`),
   `M = 10^7` (`K ≥ 10946`, `S ≥ 17349`, `L ≥ 28295`), and `M = 3 * 10^8` (`K ≥ 16266`),
   plus explicit Barrier 1–5 separations.
-/

@[expose] public section

namespace SolveCollatz

/-! ### 1. Unconditional Stopping Time up to `32768` via Mod-4096 Lifting -/

/-- Bounded Terras stopping-time checker over `4096 * q + r` for `1 ≤ q ≤ bound`. -/
def checkUncovSeven (r : Nat) : Nat → Bool
  | 0 => true
  | q + 1 => hasTerrasDrop 105 (4096 * (q + 1) + r) && checkUncovSeven r q

/-- Soundness of `checkUncovSeven`: any `1 ≤ q ≤ bound` inherits `HasFiniteStoppingTime`. -/
theorem checkUncovSeven_sound (r bound q : Nat) (hq1 : 1 ≤ q) (hq2 : q ≤ bound)
    (h : checkUncovSeven r bound = true) : HasFiniteStoppingTime (4096 * q + r) := by
  induction bound with
  | zero => omega
  | succ b ih =>
    simp only [checkUncovSeven, Bool.and_eq_true] at h
    by_cases heq : q = b + 1
    · subst heq; exact hasTerrasDrop_sound 105 _ h.1
    · exact ih (by omega) h.2

/-- Mod-4096 lifted kernel checker covering all `r < 4096` and `1 ≤ q ≤ 7`. -/
def sieve32768Check : Bool :=
  allPow2 (fun r => fastDropsWithin 12 r || checkUncovSeven r 7) 12 0

/-- Kernel certificate verifying all `1582` uncovered `[4096, 32768)` cases drop in `≤ 105`
steps. -/
theorem sieve32768Check_eq_true : sieve32768Check = true := by decide

/-- **Unconditional Small-`n` Completion (`2 ≤ n < 32768`):** every integer `2 ≤ n < 32768` has
finite Terras stopping time. -/
theorem small_lt_32768_finiteStoppingTime {n : Nat} (hn2 : 2 ≤ n) (hn32k : n < 32768) :
    HasFiniteStoppingTime n := by
  by_cases hlt : n < 4096
  · exact small_lt_4096_finiteStoppingTime hn2 hlt
  · have hq1 : 1 ≤ n / 4096 := by omega
    have hq7 : n / 4096 ≤ 7 := by omega
    have hr : n % 4096 < 4096 := Nat.mod_lt n (by decide)
    have himp := allPow2_sound _ 12 0 sieve32768Check_eq_true (n % 4096) (Nat.zero_le _)
      (by simpa using hr)
    simp only [Bool.or_eq_true] at himp
    rcases himp with hcov | huncov
    · rw [fastDropsWithin_eq_dropsWithin 12 (n % 4096)] at hcov
      exact mod4096_covered_finiteStoppingTime hn2 hcov
    · have hst := checkUncovSeven_sound (n % 4096) 7 (n / 4096) hq1 hq7 huncov
      rwa [Nat.div_add_mod] at hst

/-- **Unconditional Minimal-Element Lower Bound:** every non-trivial `SyracuseCycle` satisfies
`32768 ≤ C.n_min`. -/
theorem no_nontrivial_syracuseCycle_min_lt_32768 (C : SyracuseCycle) : 32768 ≤ C.n_min :=
  syracuseCycle_min_ge_of_stopping 32768
    (fun _ hn2 hlt => small_lt_32768_finiteStoppingTime hn2 hlt) C

/-- Strong-induction helper: any point on a non-trivial Collatz cycle is at least `M` whenever
all `2 ≤ m < M` have finite stopping time. -/
theorem collatz_cycle_elem_ge_of_stopping (M : Nat)
    (hstop : ∀ m : Nat, 2 ≤ m → m < M → HasFiniteStoppingTime m) :
    ∀ {n L : Nat}, 0 < n → 0 < L → collatzIter L n = n →
      (∀ j : Nat, j < L → collatzIter j n ≠ 1) → M ≤ n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro L hn hL hcyc hne
    by_cases hge : M ≤ n
    · exact hge
    · have hne1 : n ≠ 1 := hne 0 hL
      rcases hstop n (by omega) (Nat.lt_of_not_ge hge) with ⟨t, _, ht⟩
      have hpos : 0 < collatzIter t n := collatzIter_pos t hn
      have hcyc' : collatzIter L (collatzIter t n) = collatzIter t n := by
        rw [collatzIter_add, Nat.add_comm, ← collatzIter_add, hcyc]
      have hne' : ∀ j : Nat, j < L → collatzIter j (collatzIter t n) ≠ 1 := by
        intro j _
        rw [collatzIter_add, collatzIter_mod_of_cycle hL hcyc]
        exact hne _ (Nat.mod_lt _ hL)
      have hMle := ih (collatzIter t n) ht hpos hL hcyc' hne'
      omega

/-- **Unconditional Cycle-Element Lower Bound (`Challenge.lean`):** every element `n` on a
non-trivial positive Collatz cycle satisfies `32768 ≤ n`. -/
theorem no_nontrivial_collatzCycle_min_lt_32768 {n L : Nat} (hn : 0 < n) (hL : 0 < L)
    (hcyc : collatzIter L n = n) (hne : ∀ j : Nat, j < L → collatzIter j n ≠ 1) :
    32768 ≤ n :=
  collatz_cycle_elem_ge_of_stopping 32768
    (fun _ hn2 hlt => small_lt_32768_finiteStoppingTime hn2 hlt) hn hL hcyc hne

/-! ### 2. Continued Fraction Convergents of `log₂(3)` & Farey Separation -/

/-- Auxiliary continued-fraction evaluator tracking consecutive pairs `(prev, cur)`. -/
def cfConvergentPairAux : Nat × Nat → Nat × Nat → List Nat → (Nat × Nat) × (Nat × Nat)
  | prev, cur, [] => (prev, cur)
  | prev, cur, a :: rest =>
    cfConvergentPairAux cur (a * cur.1 + prev.1, a * cur.2 + prev.2) rest

/-- Pair of consecutive convergents `(p_{n-1}/q_{n-1}, p_n/q_n)` for partial quotients `cs`. -/
def cfConvergentPair (cs : List Nat) : (Nat × Nat) × (Nat × Nat) :=
  cfConvergentPairAux (0, 1) (1, 0) cs

/-- The final convergent `(p_n, q_n)` generated by partial quotients `cs`. -/
def cfConvergent (cs : List Nat) : Nat × Nat :=
  (cfConvergentPair cs).2

/-- Alternating Farey determinant invariant along `cfConvergentPairAux`. -/
private theorem cfConvergentPairAux_det (cs : List Nat) (prev cur : Nat × Nat) (b : Bool)
    (h : if b then cur.1 * prev.2 = prev.1 * cur.2 + 1
         else prev.1 * cur.2 = cur.1 * prev.2 + 1) :
    let res := cfConvergentPairAux prev cur cs
    let b' := cs.foldl (fun acc _ => !acc) b
    if b' then res.2.1 * res.1.2 = res.1.1 * res.2.2 + 1
    else res.1.1 * res.2.2 = res.2.1 * res.1.2 + 1 := by
  induction cs generalizing prev cur b with
  | nil => exact h
  | cons a rest ih =>
    apply ih cur (a * cur.1 + prev.1, a * cur.2 + prev.2) (!b)
    have hmul : (a * cur.1) * cur.2 = cur.1 * (a * cur.2) := by ac_rfl
    have hc1 : prev.1 * cur.2 = cur.2 * prev.1 := Nat.mul_comm _ _
    have hc2 : cur.1 * prev.2 = prev.2 * cur.1 := Nat.mul_comm _ _
    cases b <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    · rw [Nat.add_mul, Nat.mul_add, hmul, hc1]; omega
    · rw [Nat.mul_add, Nat.add_mul, hmul, hc2]; omega

/-- **Continued-Fraction Farey Determinant Theorem:** consecutive convergents `(prev, cur)` of
any partial-quotient list `cs` satisfy `cur.1 * prev.2 = prev.1 * cur.2 + 1` (odd length) or
`prev.1 * cur.2 = cur.1 * prev.2 + 1` (even length). -/
theorem cfConvergentPair_det (cs : List Nat) :
    let res := cfConvergentPair cs
    if cs.length % 2 = 0 then res.2.1 * res.1.2 = res.1.1 * res.2.2 + 1
    else res.1.1 * res.2.2 = res.2.1 * res.1.2 + 1 := by
  have hfold : ∀ (l : List Nat) (b : Bool),
      l.foldl (fun acc _ => !acc) b = if l.length % 2 = 0 then b else !b := by
    intro l b; induction l generalizing b with
    | nil => simp
    | cons _ t ih =>
      simp only [List.foldl_cons, List.length_cons, ih]
      rcases Nat.mod_two_eq_zero_or_one t.length with h | h <;> cases b <;> simp [Nat.add_mod, h]
  have hd := cfConvergentPairAux_det cs (0, 1) (1, 0) true (by decide)
  rw [hfold] at hd
  by_cases h : cs.length % 2 = 0 <;> simpa [cfConvergentPair, h] using hd

/-- Semiconvergent `(c * cur.1 + prev.1, c * cur.2 + prev.2)` inherits Farey adjacency with
`cur`. -/
theorem cf_semiconvergent_det {prev cur : Nat × Nat} (c : Nat)
    (h : prev.1 * cur.2 = cur.1 * prev.2 + 1) :
    (c * cur.1 + prev.1) * cur.2 = cur.1 * (c * cur.2 + prev.2) + 1 := by
  have hmul : (c * cur.1) * cur.2 = cur.1 * (c * cur.2) := by ac_rfl
  rw [Nat.add_mul, Nat.mul_add, hmul]; omega

/-- First `10` partial quotients `[1, 1, 1, 2, 2, 3, 1, 5, 2, 23]` of `log₂(3)`. -/
def log2ThreeCF : List Nat := [1, 1, 1, 2, 2, 3, 1, 5, 2, 23]

/-- Exact values of the first `10` convergents of `log₂(3)` (`1/1` through `24727/15601`). -/
theorem log2ThreeCF_convergents :
    cfConvergent (log2ThreeCF.take 1) = (1, 1) ∧
    cfConvergent (log2ThreeCF.take 2) = (2, 1) ∧
    cfConvergent (log2ThreeCF.take 3) = (3, 2) ∧
    cfConvergent (log2ThreeCF.take 4) = (8, 5) ∧
    cfConvergent (log2ThreeCF.take 5) = (19, 12) ∧
    cfConvergent (log2ThreeCF.take 6) = (65, 41) ∧
    cfConvergent (log2ThreeCF.take 7) = (84, 53) ∧
    cfConvergent (log2ThreeCF.take 8) = (485, 306) ∧
    cfConvergent (log2ThreeCF.take 9) = (1054, 665) ∧
    cfConvergent (log2ThreeCF.take 10) = (24727, 15601) := by
  decide

/-- Alternating exponential inequalities for even-indexed lower convergents of `log₂(3)`. -/
theorem log2ThreeCF_lower_exps :
    2 ^ 1 < 3 ^ 1 ∧ 2 ^ 3 < 3 ^ 2 ∧ 2 ^ 19 < 3 ^ 12 ∧
    2 ^ 84 < 3 ^ 53 ∧ 2 ^ 1054 < 3 ^ 665 := by
  have h : fastPow 2 1054 < fastPow 3 665 := by decide
  rw [fastPow_eq 2 1054 (by decide), fastPow_eq 3 665 (by decide)] at h
  exact ⟨by decide, by decide, by decide, by decide, h⟩

/-- Alternating exponential inequalities for odd-indexed upper convergents and key semiconvergents
of `log₂(3)`. -/
theorem log2ThreeCF_upper_exps :
    3 ^ 1 < 2 ^ 2 ∧ 3 ^ 5 < 2 ^ 8 ∧ 3 ^ 41 < 2 ^ 65 ∧
    3 ^ 253 < 2 ^ 401 ∧ 3 ^ 306 < 2 ^ 485 ∧ 3 ^ 2301 < 2 ^ 3647 ∧
    3 ^ 10281 < 2 ^ 16295 ∧ 3 ^ 15601 < 2 ^ 24727 := by
  have h1 : fastPow 3 253 < fastPow 2 401 ∧ fastPow 3 306 < fastPow 2 485 ∧
      fastPow 3 2301 < fastPow 2 3647 ∧ fastPow 3 10281 < fastPow 2 16295 ∧
      fastPow 3 15601 < fastPow 2 24727 := by decide
  rw [fastPow_eq 3 253 (by decide), fastPow_eq 2 401 (by decide),
    fastPow_eq 3 306 (by decide), fastPow_eq 2 485 (by decide),
    fastPow_eq 3 2301 (by decide), fastPow_eq 2 3647 (by decide),
    fastPow_eq 3 10281 (by decide), fastPow_eq 2 16295 (by decide),
    fastPow_eq 3 15601 (by decide), fastPow_eq 2 24727 (by decide)] at h1
  exact ⟨by decide, by decide, by decide, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2⟩

/-- Cross-multiplication from `2 ^ pL < 3 ^ qL` and `3 ^ k < 2 ^ s`: `pL * k < qL * s`. -/
theorem cf_bracket_lower_mul {pL qL k s : Nat}
    (hL : 2 ^ pL < 3 ^ qL) (hpow : 3 ^ k < 2 ^ s) : pL * k < qL * s := by
  have h2lt : 2 ^ (pL * k) < 2 ^ (qL * s) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have hs : 0 < s := by
        by_cases h0 : s = 0
        · subst h0; simp at hpow
        · omega
      have hqL : 0 < qL := by
        by_cases h0 : qL = 0
        · subst h0; simp at hL
        · omega
      simpa using Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.mp (Nat.mul_pos hqL hs))
    · calc 2 ^ (pL * k) = (2 ^ pL) ^ k := Nat.pow_mul _ _ _
        _ < (3 ^ qL) ^ k := Nat.pow_lt_pow_left hL (Nat.pos_iff_ne_zero.mp hk)
        _ = (3 ^ k) ^ qL := by rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm qL k]
        _ < (2 ^ s) ^ qL := by
            have hqL : 0 < qL := by
              by_cases h0 : qL = 0
              · subst h0; simp at hL
              · omega
            exact Nat.pow_lt_pow_left hpow (Nat.pos_iff_ne_zero.mp hqL)
        _ = 2 ^ (qL * s) := by rw [← Nat.pow_mul, Nat.mul_comm s qL]
  by_cases hlt : pL * k < qL * s
  · exact hlt
  · have := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_lt hlt); omega

/-- **Farey Upper-Semiconvergent Separation:** if `2 ^ pL < 3 ^ qL`, `pU * qL = pL * qU + 1`,
`3 ^ k < 2 ^ s`, and `k < qU + qL`, then `pU * k ≤ qU * s`. -/
theorem farey_upper_semiconvergent_bound {pL qL pU qU k s : Nat}
    (hL : 2 ^ pL < 3 ^ qL) (hdet : pU * qL = pL * qU + 1)
    (hk : k < qU + qL) (hpow : 3 ^ k < 2 ^ s) : pU * k ≤ qU * s := by
  have hmul := cf_bracket_lower_mul hL hpow
  by_cases hle : pU * k ≤ qU * s
  · exact hle
  · have h1 : qU * (pL * k + 1) ≤ qU * (qL * s) := Nat.mul_le_mul_left qU hmul
    have h2 : qL * (qU * s + 1) ≤ qL * (pU * k) := Nat.mul_le_mul_left qL (by omega)
    have hcomm1 : qU * (qL * s) = qL * (qU * s) := by ac_rfl
    have hcomm2 : qL * (pU * k) = qU * (pL * k) + k := by
      calc qL * (pU * k) = (pU * qL) * k := by ac_rfl
        _ = (pL * qU + 1) * k := by rw [hdet]
        _ = qU * (pL * k) + k := by rw [Nat.add_mul, Nat.one_mul]; ac_rfl
    rw [Nat.mul_add, Nat.mul_one] at h1 h2
    omega

/-- **Best Upper Rational Approximation Theorem:** for `0 < k < qU` with `3 ^ k < 2 ^ s`,
strict inequality `pU * k < qU * s` holds (in particular `485 * k < 306 * s` for `0 < k < 306`). -/
theorem farey_strict_upper_bound {pL qL pU qU k s : Nat}
    (hL : 2 ^ pL < 3 ^ qL) (hdet : pU * qL = pL * qU + 1)
    (hkpos : 0 < k) (hk : k < qU) (hpow : 3 ^ k < 2 ^ s) : pU * k < qU * s := by
  have hle := farey_upper_semiconvergent_bound hL hdet (by omega : k < qU + qL) hpow
  by_cases hlt : pU * k < qU * s
  · exact hlt
  · have heq : pU * k = qU * s := by omega
    have hmul := cf_bracket_lower_mul hL hpow
    rw [Nat.mul_comm qL s] at hmul
    have hfac : qU * (s * qL - pL * k) = k := by
      have h1 : qU * (s * qL) = pU * k * qL := by rw [heq]; ac_rfl
      have h2 : pU * k * qL = qU * (pL * k) + k := by
        calc pU * k * qL = (pU * qL) * k := by ac_rfl
          _ = (pL * qU + 1) * k := by rw [hdet]
          _ = qU * (pL * k) + k := by rw [Nat.add_mul, Nat.one_mul]; ac_rfl
      rw [Nat.mul_sub, h1, h2]; omega
    have hpos : 1 ≤ s * qL - pL * k := by omega
    have hqle : qU ≤ k := by simpa [hfac] using Nat.mul_le_mul_left qU hpos
    omega

/-- **Best Rational Approximation for `485 / 306`:** every `0 < k < 306` with `3 ^ k < 2 ^ s`
satisfies `485 * k < 306 * s`, and every `k < 306` satisfies `401 * k ≤ 253 * s`. -/
theorem log2Three_best_approx_lt_306 {k s : Nat} (hkpos : 0 < k) (hk : k < 306)
    (hpow : 3 ^ k < 2 ^ s) : 485 * k < 306 * s ∧ 401 * k ≤ 253 * s :=
  ⟨farey_strict_upper_bound log2ThreeCF_lower_exps.2.2.2.2 (by decide : 485 * 665 = 1054 * 306 + 1)
      hkpos hk hpow,
   farey_upper_semiconvergent_bound log2ThreeCF_lower_exps.2.2.2.1
      (by decide : 401 * 53 = 84 * 253 + 1) hk hpow⟩

/-- One-step inequality `(X + 1) ^ qU * B ≤ X ^ qU * A` from `qU * A ≤ X * (A - B)`. -/
private theorem cf_step_pow_ineq {X qU A B : Nat} (hqU : qU < X) (hBA : B ≤ A)
    (hgap : qU * A ≤ X * (A - B)) : (X + 1) ^ qU * B ≤ X ^ qU * A := by
  have hbern : (X + 1) ^ qU * (X - qU) ≤ X ^ (qU + 1) :=
    succ_pow_mul_sub_le X qU (by omega)
  have hXA : qU * A ≤ X * A := Nat.mul_le_mul_right A (by omega)
  have hXB : X * B ≤ X * A := Nat.mul_le_mul_left X hBA
  have hlin : X * B ≤ (X - qU) * A := by
    rw [Nat.mul_sub] at hgap; rw [Nat.sub_mul]; omega
  have hmul : ((X + 1) ^ qU * B) * (X - qU) ≤ (X ^ qU * A) * (X - qU) := by
    calc ((X + 1) ^ qU * B) * (X - qU)
        = ((X + 1) ^ qU * (X - qU)) * B := by ac_rfl
      _ ≤ X ^ (qU + 1) * B := Nat.mul_le_mul_right B hbern
      _ = X ^ qU * (X * B) := by rw [Nat.pow_succ, Nat.mul_assoc]
      _ ≤ X ^ qU * ((X - qU) * A) := Nat.mul_le_mul_left (X ^ qU) hlin
      _ = (X ^ qU * A) * (X - qU) := by ac_rfl
  exact Nat.le_of_mul_le_mul_right hmul (by omega)

/-- Inductive power inequality `N ^ qU * B ^ k ≤ (N - k) ^ qU * A ^ k` for `k ≤ Kmax`. -/
private theorem eliahou_cf_power_contradiction (N Kmax qU A B k : Nat)
    (hN : Kmax + qU < N) (hBA : B ≤ A) (hgap : qU * A ≤ (N - Kmax) * (A - B))
    (hk : k ≤ Kmax) : N ^ qU * B ^ k ≤ (N - k) ^ qU * A ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hprev := ih (by omega)
    let X := N - (k + 1)
    have hX1 : N - k = X + 1 := by simp only [X]; omega
    have hXqU : qU < X := by simp only [X]; omega
    have hXgap : qU * A ≤ X * (A - B) :=
      Nat.le_trans hgap (Nat.mul_le_mul_right _ (by simp only [X]; omega))
    have hstep := cf_step_pow_ineq hXqU hBA hXgap
    calc N ^ qU * B ^ (k + 1)
        = (N ^ qU * B ^ k) * B := by rw [Nat.pow_succ, Nat.mul_assoc]
      _ ≤ ((X + 1) ^ qU * A ^ k) * B := Nat.mul_le_mul_right B (by rwa [← hX1])
      _ = ((X + 1) ^ qU * B) * A ^ k := by ac_rfl
      _ ≤ (X ^ qU * A) * A ^ k := Nat.mul_le_mul_right (A ^ k) hstep
      _ = (N - (k + 1)) ^ qU * A ^ (k + 1) := by
          simp only [X, Nat.pow_succ]; rw [Nat.mul_comm (A ^ k) A, Nat.mul_assoc]

/-- **General Parametric Eliahou Continued-Fraction Elimination (`O(1)` Kernel Check):**
given Farey neighbors `pL/qL < log₂(3) < pU/qU` with `pU * qL = pL * qU + 1` and threshold `M`
satisfying `qU * 2 ^ pU ≤ (3 * M - (qU + qL)) * (2 ^ pU - 3 ^ qU)`, any `SyracuseCycle C` with
`M ≤ C.n_min` has odd length `qU + qL ≤ C.k`. -/
theorem eliahou_cf_elimination (M pL qL pU qU : Nat)
    (hMpos : 0 < M) (hqUpos : 0 < qU)
    (hL : 2 ^ pL < 3 ^ qL) (hU : 3 ^ qU < 2 ^ pU) (hdet : pU * qL = pL * qU + 1)
    (hN : qU + qL + qU < 3 * M)
    (hgap : qU * 2 ^ pU ≤ (3 * M - (qU + qL)) * (2 ^ pU - 3 ^ qU))
    (C : SyracuseCycle) (hM : M ≤ C.n_min) : qU + qL ≤ C.k := by
  by_cases hge : qU + qL ≤ C.k
  · exact hge
  · exfalso
    have hk_lt : C.k < qU + qL := Nat.lt_of_not_ge hge
    have hmul_le := farey_upper_semiconvergent_bound hL hdet hk_lt C.pow_lt
    have hel := eliahou_universal_gap_bound C hMpos hM
    have hlt1 : (3 * M - C.k) * 2 ^ C.totalVal < 3 * M * 3 ^ C.k := by
      have h3k : C.k ≤ 3 * M := by omega
      have hk2 : C.k * 2 ^ C.totalVal ≤ 3 * M * 2 ^ C.totalVal :=
        Nat.mul_le_mul_right (2 ^ C.totalVal) h3k
      have h3p : 3 * M * 3 ^ C.k ≤ 3 * M * 2 ^ C.totalVal :=
        Nat.mul_le_mul_left (3 * M) (Nat.le_of_lt C.pow_lt)
      rw [Nat.mul_sub] at hel
      rw [Nat.sub_mul]
      omega
    have hpow_lt : ((3 * M - C.k) * 2 ^ C.totalVal) ^ qU < (3 * M * 3 ^ C.k) ^ qU :=
      Nat.pow_lt_pow_left hlt1 (Nat.pos_iff_ne_zero.mp hqUpos)
    rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul,
      Nat.mul_comm C.totalVal qU, Nat.mul_comm C.k qU] at hpow_lt
    have h2le : (2 ^ pU) ^ C.k ≤ 2 ^ (qU * C.totalVal) := by
      rw [← Nat.pow_mul]; exact Nat.pow_le_pow_right (by decide) hmul_le
    have hLHS := Nat.lt_of_le_of_lt
      (Nat.mul_le_mul_left ((3 * M - C.k) ^ qU) h2le) hpow_lt
    have hRHS := eliahou_cf_power_contradiction (3 * M) (qU + qL) qU (2 ^ pU) (3 ^ qU) C.k
      hN (Nat.le_of_lt hU) hgap (Nat.le_of_lt hk_lt)
    rw [← Nat.pow_mul] at hRHS
    omega

/-- Helper extracting a lower bound `s₀ + 1 ≤ C.totalVal` from `k₀ ≤ C.k` and `2 ^ s₀ ≤ 3 ^ k₀`. -/
theorem totalVal_ge_of_k_ge (C : SyracuseCycle) (k₀ s₀ : Nat)
    (hk : k₀ ≤ C.k) (hpow : 2 ^ s₀ ≤ 3 ^ k₀) : s₀ + 1 ≤ C.totalVal := by
  have h3le : 3 ^ k₀ ≤ 3 ^ C.k := Nat.pow_le_pow_right (by decide) hk
  have hlt : 2 ^ s₀ < 2 ^ C.totalVal := Nat.lt_of_le_of_lt (Nat.le_trans hpow h3le) C.pow_lt
  by_cases hs : s₀ + 1 ≤ C.totalVal
  · exact hs
  · have := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : C.totalVal ≤ s₀)
    omega

/-! ### 3. Flagship Unconditional Eliahou Cycle-Length Bounds (`K ≥ 306`, `S ≥ 485`, `L ≥ 791`) -/

/-- Certified `fastPow` witness for `M = 32768`, `2 ^ 484 ≤ 3 ^ 306`, and Farey gap. -/
private theorem cf_witness_32768 :
    253 * 2 ^ 401 ≤ (3 * 32768 - (253 + 53)) * (2 ^ 401 - 3 ^ 253) ∧ 2 ^ 484 ≤ 3 ^ 306 := by
  have h : 253 * fastPow 2 401 ≤ (3 * 32768 - (253 + 53)) * (fastPow 2 401 - fastPow 3 253) ∧
      fastPow 2 484 ≤ fastPow 3 306 := by decide
  rwa [fastPow_eq 2 401 (by decide), fastPow_eq 3 253 (by decide),
    fastPow_eq 2 484 (by decide), fastPow_eq 3 306 (by decide)] at h

/-- **Flagship Unconditional Odd-Step Bound (`K ≥ 306`, ZERO hypotheses):**
every non-trivial positive `SyracuseCycle` has odd length `306 ≤ C.k`. -/
theorem unconditional_syracuseCycle_odd_length_ge_306 (C : SyracuseCycle) : 306 ≤ C.k :=
  eliahou_cf_elimination 32768 84 53 401 253 (by decide) (by decide)
    log2ThreeCF_lower_exps.2.2.2.1 log2ThreeCF_upper_exps.2.2.2.1 (by decide) (by decide)
    cf_witness_32768.1 C (no_nontrivial_syracuseCycle_min_lt_32768 C)

/-- **Flagship Unconditional Halving Bound (`S ≥ 485`, ZERO hypotheses):**
every non-trivial positive `SyracuseCycle` has total halvings `485 ≤ C.totalVal`. -/
theorem unconditional_syracuseCycle_halvings_ge_485 (C : SyracuseCycle) : 485 ≤ C.totalVal :=
  totalVal_ge_of_k_ge C 306 484 (unconditional_syracuseCycle_odd_length_ge_306 C)
    cf_witness_32768.2

/-- **Flagship Unconditional Total-Length Bound (`L ≥ 791`, ZERO hypotheses):**
every non-trivial positive `SyracuseCycle` has Collatz length `791 ≤ C.collatzLen`. -/
theorem unconditional_syracuseCycle_collatzLen_ge_791 (C : SyracuseCycle) : 791 ≤ C.collatzLen :=
  collatzLen_ge_of_k_ge C 306 484 (unconditional_syracuseCycle_odd_length_ge_306 C)
    cf_witness_32768.2

/-- **Flagship Unconditional Bridge to Frozen `Challenge.lean` (`L ≥ 791`):**
every non-trivial positive Collatz cycle `(n, L)` has total length `791 ≤ L`
(with `306 ≤ K`, `485 ≤ S`, `K + S = L`, and `32768 ≤ n`). -/
theorem unconditional_collatzCycle_length_ge_791 {n L : Nat} (hn : 0 < n) (hL : 0 < L)
    (hcyc : collatzIter L n = n) (hne : ∀ j : Nat, j < L → collatzIter j n ≠ 1) :
    791 ≤ L := by
  rcases exists_syracuseCycle_of_collatz_cycle hn hL hcyc hne with ⟨C, hlen⟩
  have h791 := unconditional_syracuseCycle_collatzLen_ge_791 C
  omega

/-- **Unconditional Decomposition Theorem for Frozen `HasNontrivialCycle`:**
any `HasNontrivialCycle` witness yields `(n, K, S)` with `32768 ≤ n`, `306 ≤ K`, `485 ≤ S`,
`791 ≤ K + S`, and `collatzIter (K + S) n = n` avoiding `1`. -/
theorem unconditional_hasNontrivialCycle_bounds (h : HasNontrivialCycle) :
    ∃ n K S : Nat, 32768 ≤ n ∧ 306 ≤ K ∧ 485 ≤ S ∧ 791 ≤ K + S ∧
      collatzIter (K + S) n = n ∧ ∀ j : Nat, j < K + S → collatzIter j n ≠ 1 := by
  rcases h with ⟨n, L, hn, hL, hcyc, hne⟩
  rcases exists_syracuseCycle_of_collatz_cycle hn hL hcyc hne with ⟨C, hlen⟩
  have h32k := no_nontrivial_collatzCycle_min_lt_32768 hn hL hcyc hne
  have hk := unconditional_syracuseCycle_odd_length_ge_306 C
  have hs := unconditional_syracuseCycle_halvings_ge_485 C
  have hsum : C.k + C.totalVal = L := by
    simpa [SyracuseCycle.collatzLen, Nat.add_comm] using hlen
  refine ⟨n, C.k, C.totalVal, h32k, hk, hs, by omega, ?_, ?_⟩
  · simpa [hsum] using hcyc
  · intro j hj; exact hne j (by omega)

/-! ### 4. Sharp Conditional Eliahou (1993) Lifting (`M = 10^6, 10^7, 3 * 10^8`) -/

/-- Certified `fastPow` witnesses for `M = 10^6` (`K ≥ 2966`) and `M = 10^7` (`K ≥ 10946`). -/
private theorem cf_witness_1e6_1e7 :
    (2301 * 2 ^ 3647 ≤ (3 * 1000000 - (2301 + 665)) * (2 ^ 3647 - 3 ^ 2301) ∧
      2 ^ 4700 ≤ 3 ^ 2966) ∧
    (10281 * 2 ^ 16295 ≤ (3 * 10000000 - (10281 + 665)) * (2 ^ 16295 - 3 ^ 10281) ∧
      2 ^ 17348 ≤ 3 ^ 10946) := by
  have h :
      (2301 * fastPow 2 3647 ≤
          (3 * 1000000 - (2301 + 665)) * (fastPow 2 3647 - fastPow 3 2301) ∧
        fastPow 2 4700 ≤ fastPow 3 2966) ∧
      (10281 * fastPow 2 16295 ≤
          (3 * 10000000 - (10281 + 665)) * (fastPow 2 16295 - fastPow 3 10281) ∧
        fastPow 2 17348 ≤ fastPow 3 10946) := by decide
  rwa [fastPow_eq 2 3647 (by decide), fastPow_eq 3 2301 (by decide),
    fastPow_eq 2 4700 (by decide), fastPow_eq 3 2966 (by decide),
    fastPow_eq 2 16295 (by decide), fastPow_eq 3 10281 (by decide),
    fastPow_eq 2 17348 (by decide), fastPow_eq 3 10946 (by decide)] at h

/-- Certified `fastPow` witness for `M = 3 * 10^8` (`K ≥ 16266`). -/
private theorem cf_witness_3e8 :
    15601 * 2 ^ 24727 ≤ (3 * 300000000 - (15601 + 665)) * (2 ^ 24727 - 3 ^ 15601) ∧
      2 ^ 25781 ≤ 3 ^ 16266 := by
  have h :
      15601 * fastPow 2 24727 ≤
          (3 * 300000000 - (15601 + 665)) * (fastPow 2 24727 - fastPow 3 15601) ∧
        fastPow 2 25781 ≤ fastPow 3 16266 := by decide
  rwa [fastPow_eq 2 24727 (by decide), fastPow_eq 3 15601 (by decide),
    fastPow_eq 2 25781 (by decide), fastPow_eq 3 16266 (by decide)] at h

/-- **Sharp Conditional Eliahou Bound (`M = 10^6`):** `10^6 ≤ C.n_min` forces `2966 ≤ C.k`,
`4701 ≤ C.totalVal`, and `7667 ≤ C.collatzLen` (strictly sharpening `1001` and `2588` in
`CycleLengthBounds.lean`). -/
theorem eliahou_cf_bounds_of_ge_1e6 (C : SyracuseCycle) (hM : 1000000 ≤ C.n_min) :
    2966 ≤ C.k ∧ 4701 ≤ C.totalVal ∧ 7667 ≤ C.collatzLen := by
  have hk := eliahou_cf_elimination 1000000 1054 665 3647 2301 (by decide) (by decide)
    log2ThreeCF_lower_exps.2.2.2.2 log2ThreeCF_upper_exps.2.2.2.2.2.1 (by decide) (by decide)
    cf_witness_1e6_1e7.1.1 C hM
  exact ⟨hk, totalVal_ge_of_k_ge C 2966 4700 hk cf_witness_1e6_1e7.1.2,
    collatzLen_ge_of_k_ge C 2966 4700 hk cf_witness_1e6_1e7.1.2⟩

/-- **Conditional Eliahou Lifting (`M = 10^6`):** stopping-time verification `< 10^6` forces
`2966 ≤ C.k`, `4701 ≤ C.totalVal`, and `7667 ≤ C.collatzLen`. -/
theorem eliahou_cf_bounds_of_stopping_1e6
    (hstop : ∀ n : Nat, 2 ≤ n → n < 1000000 → HasFiniteStoppingTime n)
    (C : SyracuseCycle) : 2966 ≤ C.k ∧ 4701 ≤ C.totalVal ∧ 7667 ≤ C.collatzLen :=
  eliahou_cf_bounds_of_ge_1e6 C
    (syracuseCycle_min_ge_of_stopping 1000000 (fun n h1 h2 => hstop n h1 h2) C)

/-- **Conditional Eliahou Lifting (`M = 10^7`):** stopping-time verification `< 10^7` forces
`10946 ≤ C.k`, `17349 ≤ C.totalVal`, and `28295 ≤ C.collatzLen`. -/
theorem eliahou_cf_bounds_of_stopping_1e7
    (hstop : ∀ n : Nat, 2 ≤ n → n < 10000000 → HasFiniteStoppingTime n)
    (C : SyracuseCycle) : 10946 ≤ C.k ∧ 17349 ≤ C.totalVal ∧ 28295 ≤ C.collatzLen := by
  have hM := syracuseCycle_min_ge_of_stopping 10000000 (fun n h1 h2 => hstop n h1 h2) C
  have hk := eliahou_cf_elimination 10000000 1054 665 16295 10281 (by decide) (by decide)
    log2ThreeCF_lower_exps.2.2.2.2 log2ThreeCF_upper_exps.2.2.2.2.2.2.1 (by decide) (by decide)
    cf_witness_1e6_1e7.2.1 C hM
  exact ⟨hk, totalVal_ge_of_k_ge C 10946 17348 hk cf_witness_1e6_1e7.2.2,
    collatzLen_ge_of_k_ge C 10946 17348 hk cf_witness_1e6_1e7.2.2⟩

/-- **Conditional Eliahou Lifting (`M = 3 * 10^8`):** stopping-time verification `< 3 * 10^8`
forces `16266 ≤ C.k`, `25782 ≤ C.totalVal`, and `42048 ≤ C.collatzLen`. -/
theorem eliahou_cf_bounds_of_stopping_3e8
    (hstop : ∀ n : Nat, 2 ≤ n → n < 300000000 → HasFiniteStoppingTime n)
    (C : SyracuseCycle) : 16266 ≤ C.k ∧ 25782 ≤ C.totalVal ∧ 42048 ≤ C.collatzLen := by
  have hM := syracuseCycle_min_ge_of_stopping 300000000 (fun n h1 h2 => hstop n h1 h2) C
  have hk := eliahou_cf_elimination 300000000 1054 665 24727 15601 (by decide) (by decide)
    log2ThreeCF_lower_exps.2.2.2.2 log2ThreeCF_upper_exps.2.2.2.2.2.2.2 (by decide) (by decide)
    cf_witness_3e8.1 C hM
  exact ⟨hk, totalVal_ge_of_k_ge C 16266 25781 hk cf_witness_3e8.2,
    collatzLen_ge_of_k_ge C 16266 25781 hk cf_witness_3e8.2⟩

/-- **Bridge to Frozen `Challenge.lean` (`M = 10^6` ⇒ `7667 ≤ L`):** sharpens `2588 ≤ L` in
`CycleLengthBounds.lean` without extra hypotheses. -/
theorem collatz_cycle_length_ge_7667_of_stopping_1e6
    (hstop : ∀ m : Nat, 2 ≤ m → m < 1000000 → HasFiniteStoppingTime m)
    {n L : Nat} (hn : 0 < n) (hL : 0 < L)
    (hcyc : collatzIter L n = n) (hne : ∀ j : Nat, j < L → collatzIter j n ≠ 1) :
    7667 ≤ L := by
  rcases exists_syracuseCycle_of_collatz_cycle hn hL hcyc hne with ⟨C, hlen⟩
  have hbd := eliahou_cf_bounds_of_stopping_1e6 hstop C
  omega

/-! ### 5. Explicit Barrier Separations (`Barriers 1–5`) -/

/-- **Barrier 1 Separation (`3n - 1` on `ℕ⁺`):** `n = 5` forms a non-trivial positive `3n - 1`
cycle of odd length `2 < 306`, halving count `3 < 485`, and Collatz length `5 < 791`, violating
`3 ^ K < 2 ^ S` (`¬ (3 ^ 2 < 2 ^ 3)`). -/
theorem barrier1_eliahou_three_n_minus_one :
    Barriers.genIter 3 (-1) 5 5 = 5 ∧
    (∀ j : Nat, j < 5 → Barriers.genIter 3 (-1) j 5 ≠ 1) ∧
    2 < 306 ∧ 3 < 485 ∧ 5 < 791 ∧ ¬ (3 ^ 2 < 2 ^ 3) :=
  ⟨Barriers.three_n_minus_one_cycle_5.1, Barriers.three_n_minus_one_cycle_5.2,
    by decide, by decide, by decide, by decide⟩

/-- **Barrier 2 Separation (`5n + 1` on `ℕ⁺`):** `n = 13` forms a non-trivial positive `5n + 1`
cycle of odd length `3 < 306`, halving count `7 < 485`, and Collatz length `10 < 791`, even
though `3 ^ 3 < 2 ^ 7` and `5 ^ 3 < 2 ^ 7` hold, because `5n + 1` violates `(3n + 1)` stopping
time (`13 < 32768`) and `(3 * M + 1) ^ K` drift. -/
theorem barrier2_eliahou_five_n_plus_one :
    Barriers.genIter 5 1 10 13 = 13 ∧
    (∀ j : Nat, j < 10 → Barriers.genIter 5 1 j 13 ≠ 1) ∧
    3 < 306 ∧ 7 < 485 ∧ 10 < 791 ∧ 5 ^ 3 < 2 ^ 7 ∧ 3 ^ 3 < 2 ^ 7 :=
  ⟨Barriers.five_n_plus_one_cycle_13.1, Barriers.five_n_plus_one_cycle_13.2,
    by decide, by decide, by decide, by decide, by decide⟩

/-- **Barrier 3 Separation (`3n + 1` on `ℤ_{<0}`):** `n = -5` forms a non-trivial negative cycle
of odd length `2 < 306`, halving count `3 < 485`, and Collatz length `5 < 791`, escaping
archimedean positivity `1 < n_min` and `3 ^ 2 < 2 ^ 3`. -/
theorem barrier3_eliahou_neg_int :
    Barriers.genIter 3 1 5 (-5) = -5 ∧
    (∀ j : Nat, j < 5 → Barriers.genIter 3 1 j (-5) ≠ 1) ∧
    2 < 306 ∧ 3 < 485 ∧ 5 < 791 ∧ ¬ (3 ^ 2 < 2 ^ 3) :=
  ⟨Barriers.neg_int_cycle_neg5.1, Barriers.neg_int_cycle_neg5.2,
    by decide, by decide, by decide, by decide⟩

/-- **Barrier 4 Separation (`ℤ₂` rational cycles):** `1927 / 295 ∈ ℤ_(2) \ ℤ` (`K = 6 < 306`,
`S = 10 < 485`, `L = 16 < 791`) and `211 / 13 ∈ ℤ_(2) \ ℤ` (`K = 5 < 306`, `S = 8 < 485`,
`L = 13 < 791`) are genuine positive `2`-adic periodic orbits satisfying `3 ^ K < 2 ^ S` yet
violating global integrality in `ℕ⁺`. -/
theorem barrier4_eliahou_twoAdic :
    let v := [2, 2, 1, 2, 1, 2]
    let x := periodicPoint v (by decide)
    (x = ⟨1927, 295, by decide⟩ ∧ OddDenomRat.syracuseIter 6 x = x ∧
      3 ^ 6 < 2 ^ 10 ∧ 6 < 306 ∧ 10 < 485 ∧ 16 < 791 ∧
      (¬ ∃ m : Int, x.Equiv (OddDenomRat.ofInt m))) ∧
    (periodicPoint [1, 1, 1, 1, 4] (by decide) = ⟨211, 13, by decide⟩ ∧
      OddDenomRat.syracuseIter 5 (periodicPoint [1, 1, 1, 1, 4] (by decide)) =
        periodicPoint [1, 1, 1, 1, 4] (by decide) ∧
      3 ^ 5 < 2 ^ 8 ∧ 5 < 306 ∧ 8 < 485 ∧ 13 < 791) := by
  have hv : IsValidParityVec [2, 2, 1, 2, 1, 2] := by simp [IsValidParityVec]
  rcases universal_twoAdic_periodicPoint hv with ⟨_, _, hcyc, _, _, _⟩
  have hx : periodicPoint [2, 2, 1, 2, 1, 2] (by decide) = ⟨1927, 295, by decide⟩ := by decide
  have hnotInt :
      ¬ ∃ m : Int, (periodicPoint [2, 2, 1, 2, 1, 2] (by decide)).Equiv (OddDenomRat.ofInt m) := by
    rintro ⟨m, hm⟩; rw [hx] at hm
    unfold OddDenomRat.Equiv OddDenomRat.ofInt at hm; simp only at hm; omega
  exact ⟨⟨hx, hcyc, by decide, by decide, by decide, by decide, hnotInt⟩,
    ⟨twoAdic_cycle_211_over_13.1, twoAdic_cycle_211_over_13.2.2.1,
      by decide, by decide, by decide, by decide⟩⟩

/-- **Barrier 5 Separation (Conway 1972 / Finite Verification Horizon):** finite stopping-time
verification up to `M` (`32768`, `10^6`, `10^7`, `3 * 10^8`) produces finite continued-fraction
lower bounds (`306`, `2966`, `10946`, `16266`) on `C.k`, never ruling out all cycles without
global Diophantine / Baker bounds. -/
theorem barrier5_eliahou_conway_finite_lifting :
    (∀ C : SyracuseCycle, 306 ≤ C.k ∧ 791 ≤ C.collatzLen) ∧
    ((∀ n : Nat, 2 ≤ n → n < 1000000 → HasFiniteStoppingTime n) →
      ∀ C : SyracuseCycle, 2966 ≤ C.k ∧ 7667 ≤ C.collatzLen) ∧
    ((∀ n : Nat, 2 ≤ n → n < 10000000 → HasFiniteStoppingTime n) →
      ∀ C : SyracuseCycle, 10946 ≤ C.k ∧ 28295 ≤ C.collatzLen) ∧
    ((∀ n : Nat, 2 ≤ n → n < 300000000 → HasFiniteStoppingTime n) →
      ∀ C : SyracuseCycle, 16266 ≤ C.k ∧ 42048 ≤ C.collatzLen) :=
  ⟨fun C => ⟨unconditional_syracuseCycle_odd_length_ge_306 C,
      unconditional_syracuseCycle_collatzLen_ge_791 C⟩,
    fun h C => ⟨(eliahou_cf_bounds_of_stopping_1e6 h C).1,
      (eliahou_cf_bounds_of_stopping_1e6 h C).2.2⟩,
    fun h C => ⟨(eliahou_cf_bounds_of_stopping_1e7 h C).1,
      (eliahou_cf_bounds_of_stopping_1e7 h C).2.2⟩,
    fun h C => ⟨(eliahou_cf_bounds_of_stopping_3e8 h C).1,
      (eliahou_cf_bounds_of_stopping_3e8 h C).2.2⟩⟩

end SolveCollatz
