/-
Copyright (c) 2026 The solve-collatz contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Collatz.Known.TerrasDensity

/-!
# Bridge to Terence Tao (2022) Almost-All Almost-Bounded Orbits (`KNOWN-004`)

Pure Lean 4 core formalization (zero Mathlib, zero reals) bridging frozen `Challenge.lean`,
`Collatz/Core/Syracuse.lean`, and `Collatz/Known/TerrasDensity.lean` to Tao's (2022)
logarithmic-density almost-boundedness framework (`Forum of Mathematics, Pi`, Vol. 10, e12):
- Orbit minimum `OrbitMinLe`, `EventuallyBelow`, and `CollatzReachesOne`, bridged to
  `CollatzConjecture`, `HasFiniteStoppingTime`, `syracuseIter`, and `terrasIter`.
- Exact `N!`-scaled harmonic weights `harmonicWeight N n = N! / n`, integer harmonic sum
  `harmonicSumNum`, logarithmic density `HasLogDensityOne`, pure-`Nat` Abel summation, and the
  Tauberian theorem `hasLogDensityOne_of_hasNaturalDensityOne`, yielding `terras_log_density_one`.
- Syracuse offset bound (`syracuseOffset_upper_bound`), drift contraction interface
  (`TaoSyracuseDriftHypothesis → TaoAlmostBoundedConjecture`), and corollaries including
  `tao_almost_bounded_implies_log_density_finite_stopping` and `bitLen` almost-boundedness.
- Exact Barrier 4 / zero-density separation (`notMersenne_hasLogDensityOne`,
  `hasLogDensityOne_not_implies_forall`, `terras_log_density_one_allows_cycle`), showing why
  logarithmic density 1 still leaves `{2^k - 1}` and putative cycles open for `PROVE-A1`.
-/

@[expose] public section

namespace SolveCollatz

private theorem dec_true {P : Prop} (h : P) : @decide P (Classical.propDecidable P) = true :=
  @decide_eq_true P (Classical.propDecidable P) h
private theorem dec_false {P : Prop} (h : ¬ P) : @decide P (Classical.propDecidable P) = false :=
  @decide_eq_false P (Classical.propDecidable P) h
private theorem of_dec_true {P : Prop} (h : @decide P (Classical.propDecidable P) = true) : P :=
  @of_decide_eq_true P (Classical.propDecidable P) h

/-! ### 1. Orbit Minimum, Almost-Boundedness, and Core Compatibility -/

/-- `OrbitMinLe n B` holds if the Collatz orbit of `n` attains a value `≤ B`. -/
def OrbitMinLe (n B : Nat) : Prop := ∃ t : Nat, collatzIter t n ≤ B
/-- `EventuallyBelow n B` holds if all Collatz iterates from some time `T` onward are `≤ B`. -/
def EventuallyBelow (n B : Nat) : Prop := ∃ T : Nat, ∀ t : Nat, T ≤ t → collatzIter t n ≤ B
/-- `CollatzReachesOne n` holds if the standard Collatz orbit of `n` hits `1`. -/
def CollatzReachesOne (n : Nat) : Prop := ∃ t : Nat, collatzIter t n = 1

/-- Frozen `CollatzConjecture` restated via `CollatzReachesOne`. -/
theorem collatzConjecture_iff_reachesOne :
    CollatzConjecture ↔ ∀ n : Nat, 0 < n → CollatzReachesOne n := Iff.rfl
/-- Every natural number satisfies `OrbitMinLe n n` at time `0`. -/
theorem orbitMinLe_self (n : Nat) : OrbitMinLe n n := ⟨0, Nat.le_refl n⟩
/-- Monotonicity of `OrbitMinLe` in the threshold `B`. -/
theorem orbitMinLe_mono {n B₁ B₂ : Nat} (hB : B₁ ≤ B₂) (h : OrbitMinLe n B₁) :
    OrbitMinLe n B₂ := by rcases h with ⟨t, ht⟩; exact ⟨t, Nat.le_trans ht hB⟩
/-- Pulling `OrbitMinLe` back along an iterate `collatzIter t₀ n`. -/
theorem orbitMinLe_of_iter {t₀ n B : Nat} (h : OrbitMinLe (collatzIter t₀ n) B) :
    OrbitMinLe n B := by rcases h with ⟨t, ht⟩; exact ⟨t₀ + t, by rw [← collatzIter_add]; exact ht⟩
/-- Transitivity of `OrbitMinLe` across an intermediate threshold `B₁`. -/
theorem orbitMinLe_trans {n B₁ B₂ : Nat} (hn : 0 < n) (h1 : OrbitMinLe n B₁)
    (h2 : ∀ m : Nat, 0 < m → m ≤ B₁ → OrbitMinLe m B₂) : OrbitMinLe n B₂ := by
  rcases h1 with ⟨t₁, ht₁⟩; exact orbitMinLe_of_iter (h2 _ (collatzIter_pos t₁ hn) ht₁)

/-- For `n > 0`, reaching `1` is equivalent to `OrbitMinLe n 1`. -/
theorem collatzReachesOne_iff_orbitMinLe_one {n : Nat} (hn : 0 < n) :
    CollatzReachesOne n ↔ OrbitMinLe n 1 :=
  ⟨fun ⟨t, ht⟩ => ⟨t, by omega⟩,
   fun ⟨t, ht⟩ => by have := collatzIter_pos t hn; exact ⟨t, by omega⟩⟩
/-- Equivalence between frozen `CollatzConjecture` and universal `OrbitMinLe n 1`. -/
theorem collatzConjecture_iff_orbitMinLe_one :
    CollatzConjecture ↔ ∀ n : Nat, 0 < n → OrbitMinLe n 1 :=
  ⟨fun h n hn => (collatzReachesOne_iff_orbitMinLe_one hn).mp (h n hn),
   fun h n hn => (collatzReachesOne_iff_orbitMinLe_one hn).mpr (h n hn)⟩
/-- Reaching `1` implies `EventuallyBelow n 4` via `1 → 4 → 2 → 1`. -/
theorem eventuallyBelow_four_of_reachesOne {n : Nat} (h : CollatzReachesOne n) :
    EventuallyBelow n 4 := by
  rcases h with ⟨t₀, ht₀⟩; refine ⟨t₀, fun t ht => ?_⟩
  rw [show collatzIter t n = collatzIter (t - t₀) 1 by
    rw [← ht₀, collatzIter_add, Nat.add_sub_of_le ht]]
  exact collatzIter_one_le_four (t - t₀)
/-- For `n > 0`, `CollatzReachesOne n` is equivalent to `EventuallyBelow n 4`. -/
theorem collatzReachesOne_iff_eventuallyBelow_four {n : Nat} (hn : 0 < n) :
    CollatzReachesOne n ↔ EventuallyBelow n 4 := by
  refine ⟨eventuallyBelow_four_of_reachesOne, fun ⟨T, hT⟩ => ?_⟩
  have hxpos := collatzIter_pos T hn; have hx1_4 := hT (T + 1) (Nat.le_succ T)
  have hstep : collatzIter (T + 1) n = collatzStep (collatzIter T n) := by
    rw [← collatzIter_add]; rfl
  match hval : collatzIter T n with
  | 0 => omega | 1 => exact ⟨T, hval⟩
  | 2 => exact ⟨T + 1, by rw [hstep, hval]; decide⟩
  | 3 => have h10 : collatzStep 3 = 10 := rfl; rw [hstep, hval, h10] at hx1_4; omega
  | 4 => refine ⟨T + 2, ?_⟩; rw [← collatzIter_add, hval]; decide
  | k + 5 => have := hT T (Nat.le_refl T); omega
/-- Dropping to `B < n` implies `HasFiniteStoppingTime n`. -/
theorem hasFiniteStoppingTime_of_orbitMinLe_lt {n B : Nat} (hBn : B < n)
    (h : OrbitMinLe n B) : HasFiniteStoppingTime n := by
  rcases h with ⟨t, ht⟩; cases t with
  | zero => simp [collatzIter] at ht; omega
  | succ t' => exact ⟨t' + 1, Nat.succ_pos t', Nat.lt_of_le_of_lt ht hBn⟩
/-- Strong-induction descent: if every `B < m ≤ n` has finite stopping time,
then `OrbitMinLe n B`. -/
theorem orbitMinLe_of_le_below {n B : Nat}
    (h : ∀ m : Nat, B < m → m ≤ n → HasFiniteStoppingTime m) : OrbitMinLe n B := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hle : n ≤ B
    · exact ⟨0, hle⟩
    · rcases h n (Nat.lt_of_not_ge hle) (Nat.le_refl n) with ⟨k, _, hk⟩
      exact orbitMinLe_of_iter
        (ih _ hk (fun m hm1 hm2 => h m hm1 (Nat.le_trans hm2 (Nat.le_of_lt hk))))

/-- Compatibility of `OrbitMinLe` with the accelerated Syracuse map `syracuseIter`. -/
theorem orbitMinLe_of_syracuse {k n B : Nat} (hn : 0 < n)
    (hsyr : syracuseIter k (oddPart n) ≤ B) : OrbitMinLe n B := by
  refine ⟨valuation2 n + (syracuseTotalVal k (oddPart n) + k), ?_⟩
  rw [← collatzIter_add, collatzIter_valuation2, collatzIter_eq_syracuseIter k (oddPart_odd hn)]
  exact hsyr

/-- Compatibility of `OrbitMinLe` with the compressed Terras map `terrasIter`. -/
theorem orbitMinLe_of_terras {k n B : Nat} (ht : terrasIter k n ≤ B) : OrbitMinLe n B := by
  refine ⟨k + countOnes (terrasParityVec k n), ?_⟩; rw [collatzIter_eq_terrasIter]; exact ht

/-! ### 2. Pure-`Nat` Harmonic Weights, Abel Summation & Tauberian Theorem -/

/-- Pure-`Nat` factorial `N!`. -/
def natFact : Nat → Nat | 0 => 1 | n + 1 => (n + 1) * natFact n
/-- `0 < natFact N` for every `N`. -/
theorem natFact_pos (N : Nat) : 0 < natFact N := by
  induction N with | zero => decide | succ N ih => exact Nat.mul_pos (Nat.succ_pos N) ih
/-- Every `1 ≤ n ≤ N` divides `natFact N`. -/
theorem dvd_natFact {n N : Nat} (hn1 : 1 ≤ n) (hnN : n ≤ N) : n ∣ natFact N := by
  induction N with | zero => omega | succ N ih =>
    by_cases heq : n = N + 1
    · subst heq; exact ⟨natFact N, rfl⟩
    · exact Nat.dvd_trans (ih (by omega)) ⟨N + 1, Nat.mul_comm _ _⟩
/-- Exact `N!`-scaled reciprocal weight `N! / n`. -/
def harmonicWeight (N n : Nat) : Nat := natFact N / n
/-- Clearing denominator identity `n * harmonicWeight N n = natFact N` for `1 ≤ n ≤ N`. -/
theorem mul_harmonicWeight {n N : Nat} (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    n * harmonicWeight N n = natFact N := Nat.mul_div_cancel' (dvd_natFact hn1 hnN)
/-- Antitonicity of `harmonicWeight N` on `1 ≤ n < N`. -/
theorem harmonicWeight_antitone {n N : Nat} (hn1 : 1 ≤ n) (hnN : n + 1 ≤ N) :
    harmonicWeight N (n + 1) ≤ harmonicWeight N n := by
  have h1 := mul_harmonicWeight hn1 (by omega : n ≤ N)
  have h2 := mul_harmonicWeight (by omega : 1 ≤ n + 1) hnN; rw [Nat.succ_mul] at h2
  exact Nat.le_of_mul_le_mul_left (by omega : n * harmonicWeight N (n + 1) ≤ _) hn1
/-- General antitonicity `harmonicWeight N b ≤ harmonicWeight N a` for `1 ≤ a ≤ b ≤ N`. -/
theorem harmonicWeight_antitone_le {a b N : Nat} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ N) :
    harmonicWeight N b ≤ harmonicWeight N a := by
  induction b with | zero => omega | succ b ih =>
    by_cases heq : a = b + 1
    · subst heq; exact Nat.le_refl _
    · exact Nat.le_trans (harmonicWeight_antitone (by omega) hb) (ih (by omega) (by omega))
/-- Exact Abel-weight difference `n * (w n - w (n + 1)) = w (n + 1)` for `1 ≤ n < N`. -/
theorem mul_harmonicWeight_diff {n N : Nat} (hn1 : 1 ≤ n) (hnN : n + 1 ≤ N) :
    n * (harmonicWeight N n - harmonicWeight N (n + 1)) = harmonicWeight N (n + 1) := by
  rw [Nat.mul_sub_left_distrib, mul_harmonicWeight hn1 (by omega : n ≤ N)]
  have h2 := mul_harmonicWeight (by omega : 1 ≤ n + 1) hnN; rw [Nat.succ_mul] at h2; omega

/-- Sum `f 1 + f 2 + ... + f N` over `[1, N]`. -/
def natSum1 : Nat → (Nat → Nat) → Nat | 0, _ => 0 | n + 1, f => natSum1 n f + f (n + 1)
/-- Pointwise monotonicity of `natSum1`. -/
theorem natSum1_le {N : Nat} {f g : Nat → Nat}
    (h : ∀ i : Nat, 1 ≤ i → i ≤ N → f i ≤ g i) : natSum1 N f ≤ natSum1 N g := by
  induction N with | zero => exact Nat.le_refl 0 | succ N ih =>
    simp only [natSum1]; have := ih (fun i h1 h2 => h i h1 (Nat.le_succ_of_le h2))
    have := h (N + 1) (Nat.succ_pos N) (Nat.le_refl _); omega
private theorem natSum1_congr {N : Nat} {f g : Nat → Nat}
    (h : ∀ i : Nat, 1 ≤ i → i ≤ N → f i = g i) : natSum1 N f = natSum1 N g :=
  Nat.le_antisymm (natSum1_le (fun i h1 h2 => Nat.le_of_eq (h i h1 h2)))
    (natSum1_le (fun i h1 h2 => Nat.le_of_eq (h i h1 h2).symm))
private theorem natSum1_mono_bound {a b : Nat} (hab : a ≤ b) (f : Nat → Nat) :
    natSum1 a f ≤ natSum1 b f := by
  induction b with | zero => rw [Nat.eq_zero_of_le_zero hab]; exact Nat.le_refl 0 | succ b ih =>
    by_cases hle : a ≤ b
    · exact Nat.le_trans (ih hle) (by simp [natSum1])
    · rw [show a = b + 1 by omega]; exact Nat.le_refl _
private theorem natSum1_mul_left (c N : Nat) (f : Nat → Nat) :
    natSum1 N (fun i => c * f i) = c * natSum1 N f := by
  induction N with | zero => simp [natSum1] | succ N ih => simp only [natSum1, ih, Nat.mul_add]
private theorem natSum1_add (N : Nat) (f g : Nat → Nat) :
    natSum1 N (fun i => f i + g i) = natSum1 N f + natSum1 N g := by
  induction N with | zero => simp [natSum1] | succ N ih => simp only [natSum1, ih]; omega
private theorem natSum1_add_split (a k : Nat) (f : Nat → Nat) :
    natSum1 (a + k) f = natSum1 a f + natSum1 k (fun j => f (a + j)) := by
  induction k with | zero => simp [natSum1] | succ k ih =>
    rw [← Nat.add_assoc, natSum1, ih, natSum1, show a + k + 1 = a + (k + 1) by omega]; omega
private theorem natSum1_const_le {k c : Nat} {f : Nat → Nat}
    (h : ∀ j : Nat, 1 ≤ j → j ≤ k → c ≤ f j) : k * c ≤ natSum1 k f := by
  induction k with | zero => simp [natSum1] | succ k ih =>
    rw [natSum1, Nat.succ_mul]; have := ih (fun j h1 h2 => h j h1 (Nat.le_succ_of_le h2))
    have := h (k + 1) (Nat.succ_pos k) (Nat.le_refl _); omega

/-- **Pure-`Nat` Abel Summation:** for `1 ≤ N` and antitone `w`,
`∑_{i=1}^N f i * w i = S N * w N + ∑_{i=1}^{N-1} S i * (w i - w (i + 1))`. -/
theorem abel_summation (f w : Nat → Nat) {N : Nat} (hN : 1 ≤ N)
    (hw : ∀ i : Nat, 1 ≤ i → i < N → w (i + 1) ≤ w i) :
    natSum1 N (fun i => f i * w i) =
      natSum1 N f * w N + natSum1 (N - 1) (fun i => natSum1 i f * (w i - w (i + 1))) := by
  induction N with | zero => omega | succ n ih => cases n with
    | zero => simp [natSum1]
    | succ m =>
      have hih := ih (by omega) (fun i hi1 hi2 => hw i hi1 (Nat.lt_succ_of_lt hi2))
      have hw_last : w (m + 2) ≤ w (m + 1) := hw (m + 1) (by omega) (Nat.lt_succ_self _)
      have hsplit : natSum1 (m + 1) f * w (m + 1) =
          natSum1 (m + 1) f * (w (m + 1) - w (m + 2)) + natSum1 (m + 1) f * w (m + 2) := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hw_last]
      rw [natSum1, hih, Nat.add_sub_cancel, hsplit]
      have hR1 : natSum1 (m + 1 + 1) f = natSum1 (m + 1) f + f (m + 2) := rfl
      have hR2 : natSum1 (m + 1 + 1 - 1) (fun i => natSum1 i f * (w i - w (i + 1))) =
          natSum1 m (fun i => natSum1 i f * (w i - w (i + 1))) +
          natSum1 (m + 1) f * (w (m + 1) - w (m + 2)) := rfl
      rw [hR1, hR2, Nat.add_mul, show m + 1 + 1 = m + 2 from rfl]; omega

/-- Exact telescoping identity for antitone `w`: `∑_{i=1}^m (w i - w (i + 1)) + w (m + 1) = w 1`.
-/
theorem telescope_harmonic_diff (w : Nat → Nat) (m : Nat)
    (hw : ∀ i : Nat, 1 ≤ i → i ≤ m → w (i + 1) ≤ w i) :
    natSum1 m (fun i => w i - w (i + 1)) + w (m + 1) = w 1 := by
  induction m with | zero => simp [natSum1] | succ m ih =>
    have := ih (fun i h1 h2 => hw i h1 (Nat.le_succ_of_le h2))
    have := hw (m + 1) (by omega) (Nat.le_refl _); rw [natSum1]; omega

/-- Exact `N!`-scaled harmonic sum `N! * ∑_{n=1}^N (1 / n)`. -/
def harmonicSumNum (N : Nat) : Nat := natSum1 N (harmonicWeight N)
/-- Exact `N!`-scaled harmonic sum over exceptional integers `1 ≤ n ≤ N` failing `P`. -/
noncomputable def logExceptionalNum (P : Nat → Prop) (N : Nat) : Nat :=
  natSum1 N (fun n => if @decide (¬ P n) (Classical.propDecidable _) then harmonicWeight N n else 0)
/-- Exact count of positive integers `1 ≤ n ≤ N` failing `P`. -/
noncomputable def natExceptionalCount (P : Nat → Prop) (N : Nat) : Nat :=
  countLt (fun n => @decide (1 ≤ n ∧ ¬ P n) (Classical.propDecidable _)) (N + 1)
/-- `natExceptionalCount P N` equals `natSum1 N` of the `0/1` failure indicator. -/
theorem natExceptionalCount_eq_natSum1 (P : Nat → Prop) (N : Nat) :
    natExceptionalCount P N =
      natSum1 N (fun n => if @decide (¬ P n) (Classical.propDecidable _) then 1 else 0) := by
  induction N with | zero => simp [natExceptionalCount, countLt, natSum1] | succ N ih =>
    unfold natExceptionalCount at ih ⊢; rw [countLt, ih, natSum1]
    by_cases hP : P (N + 1)
    · rw [dec_false (fun h => h.2 hP), dec_false (fun h => h hP)]
    · rw [dec_true ⟨Nat.succ_pos N, hP⟩, dec_true hP]

/-- Natural density `1` over `ℕ⁺`: for every `D > 0`, eventually `natExceptionalCount P N * D < N`.
-/
def HasNaturalDensityOne (P : Nat → Prop) : Prop :=
  ∀ D : Nat, 0 < D → ∃ N₀ : Nat, ∀ N : Nat, N₀ ≤ N → natExceptionalCount P N * D < N
/-- **Tao-style Logarithmic Density `1`:** for every `D > 0`, eventually
`logExceptionalNum P N * D < harmonicSumNum N`. -/
def HasLogDensityOne (P : Nat → Prop) : Prop :=
  ∀ D : Nat, 0 < D → ∃ N₀ : Nat, ∀ N : Nat, N₀ ≤ N → logExceptionalNum P N * D < harmonicSumNum N

/-- Dyadic block lower bound: `(m + 2) * natFact N ≤ 2 * harmonicSumNum N` for `2 ^ m ≤ N`. -/
theorem dyadic_harmonic_lower_bound {m N : Nat} (hm : 2 ^ m ≤ N) :
    (m + 2) * natFact N ≤ 2 * harmonicSumNum N := by
  have hsum : ∀ k : Nat, 2 ^ k ≤ N →
      (k + 2) * natFact N ≤ 2 * natSum1 (2 ^ k) (harmonicWeight N) := fun k hk => by
    induction k with
    | zero =>
      simp only [Nat.pow_zero, natSum1, Nat.zero_add]; rw [← mul_harmonicWeight (Nat.le_refl 1) hk]
      omega
    | succ k ih =>
      have hprev := ih (Nat.le_trans (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_succ k)) hk)
      have hblk := natSum1_const_le (k := 2 ^ k) (c := harmonicWeight N (2 ^ (k + 1)))
        (f := fun j => harmonicWeight N (2 ^ k + j))
        (fun j h1 h2 => harmonicWeight_antitone_le (by omega) (by omega) hk)
      have hmul : 2 * (2 ^ k * harmonicWeight N (2 ^ (k + 1))) = natFact N := by
        rw [← Nat.mul_assoc, Nat.mul_comm 2 (2 ^ k), ← Nat.pow_succ]
        exact mul_harmonicWeight (Nat.two_pow_pos (k + 1)) hk
      rw [show 2 ^ (k + 1) = 2 ^ k + 2 ^ k by rw [Nat.pow_succ]; omega, natSum1_add_split,
        show k + 1 + 2 = (k + 2) + 1 by omega, Nat.add_mul, Nat.one_mul]; omega
  exact Nat.le_trans (hsum m hm) (Nat.mul_le_mul_left 2 (natSum1_mono_bound hm (harmonicWeight N)))

private theorem abel_head_le (f : Nat → Nat) (N₀ N K : Nat) (hN₀ : 1 ≤ N₀) (hN : N₀ ≤ N)
    (hf : ∀ i : Nat, f i ≤ 1) : natSum1 (N₀ - 1) (fun i => K * (natSum1 i f *
      (harmonicWeight N i - harmonicWeight N (i + 1)))) ≤ K * N₀ * natFact N := by
  have hS : ∀ i : Nat, natSum1 i f ≤ i := fun i => by
    induction i with
    | zero => exact Nat.le_refl 0
    | succ i _ => have := hf (i + 1); simp [natSum1]; omega
  have h1 := natSum1_le (N := N₀ - 1)
    (f := fun i => K * (natSum1 i f * (harmonicWeight N i - harmonicWeight N (i + 1))))
    (g := fun i => (K * N₀) * (harmonicWeight N i - harmonicWeight N (i + 1))) (fun i _ hi2 => by
      rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _
        (Nat.mul_le_mul_left K (Nat.le_trans (hS i) (by omega))))
  rw [natSum1_mul_left (K * N₀) (N₀ - 1)
    (fun i => harmonicWeight N i - harmonicWeight N (i + 1))] at h1
  have htel := telescope_harmonic_diff (harmonicWeight N) (N₀ - 1)
    (fun i hi1 _ => harmonicWeight_antitone hi1 (by omega))
  have hw1 : harmonicWeight N 1 = natFact N := by
    simpa using mul_harmonicWeight (Nat.le_refl 1) (Nat.le_trans hN₀ hN)
  exact Nat.le_trans h1 (Nat.mul_le_mul_left (K * N₀) (by rw [← hw1]; omega))

private theorem abel_weighted_sum_bound (f : Nat → Nat) (N₀ N K : Nat)
    (hN₀ : 1 ≤ N₀) (hN : N₀ ≤ N) (hf : ∀ i : Nat, f i ≤ 1)
    (hbound : ∀ i : Nat, N₀ ≤ i → K * natSum1 i f ≤ i) :
    K * natSum1 N (fun i => f i * harmonicWeight N i) ≤
      (K * N₀ + 1) * natFact N + harmonicSumNum N := by
  rw [abel_summation f (harmonicWeight N) (Nat.le_trans hN₀ hN)
      (fun i hi1 hi2 => harmonicWeight_antitone hi1 hi2),
    Nat.mul_add, ← natSum1_mul_left, show N - 1 = (N₀ - 1) + (N - N₀) by omega, natSum1_add_split]
  have hhead := abel_head_le f N₀ N K hN₀ hN hf
  have hlast : K * (natSum1 N f * harmonicWeight N N) ≤ natFact N := by
    rw [← Nat.mul_assoc]; have h1 := Nat.mul_le_mul_right (harmonicWeight N N) (hbound N hN)
    rwa [mul_harmonicWeight (Nat.le_trans hN₀ hN) (Nat.le_refl N)] at h1
  have h1 := natSum1_le (N := N - N₀) (g := fun j => harmonicWeight N (N₀ + j))
    (f := fun j => K * (natSum1 (N₀ - 1 + j) f *
      (harmonicWeight N (N₀ - 1 + j) - harmonicWeight N (N₀ - 1 + j + 1)))) (fun j hj1 hj2 => by
      rw [← Nat.mul_assoc, show N₀ - 1 + j + 1 = N₀ + j by omega]
      have h2 := Nat.mul_le_mul_right (harmonicWeight N (N₀ - 1 + j) - harmonicWeight N (N₀ + j))
        (hbound (N₀ - 1 + j) (by omega))
      rw [show N₀ + j = (N₀ - 1 + j) + 1 by omega] at h2 ⊢
      rw [mul_harmonicWeight_diff (by omega : 1 ≤ N₀ - 1 + j) (by omega)] at h2; exact h2)
  have hsum : natSum1 N₀ (harmonicWeight N) +
      natSum1 (N - N₀) (fun j => harmonicWeight N (N₀ + j)) = harmonicSumNum N := by
    unfold harmonicSumNum; rw [← natSum1_add_split, show N₀ + (N - N₀) = N by omega]
  rw [Nat.add_mul, Nat.one_mul]; omega

/-- **Fundamental Tauberian Theorem (Abel Summation):** natural density `1` implies
logarithmic density `1`. -/
theorem hasLogDensityOne_of_hasNaturalDensityOne {P : Nat → Prop}
    (hnat : HasNaturalDensityOne P) : HasLogDensityOne P := by
  intro D hD; rcases hnat (2 * D) (by omega) with ⟨M₀, hM₀⟩
  let N₀ := max M₀ 1; let m := 2 * (2 * D * N₀ + 2)
  refine ⟨max N₀ (2 ^ m), fun N hN => ?_⟩
  let f : Nat → Nat := fun n => if @decide (¬ P n) (Classical.propDecidable _) then 1 else 0
  have hbound : ∀ i : Nat, N₀ ≤ i → 2 * D * natSum1 i f ≤ i := fun i hi => by
    rw [← natExceptionalCount_eq_natSum1 P i, Nat.mul_comm]
    exact Nat.le_of_lt (hM₀ i (Nat.le_trans (Nat.le_max_left _ _) hi))
  have hlog_eq : logExceptionalNum P N = natSum1 N (fun i => f i * harmonicWeight N i) :=
    natSum1_congr (fun i _ _ => by dsimp [f]; split <;> simp)
  have hab := abel_weighted_sum_bound f N₀ N (2 * D) (Nat.le_max_right _ _)
    (Nat.le_trans (Nat.le_max_left _ _) hN) (fun i => by dsimp [f]; split <;> omega) hbound
  have hdyad := dyadic_harmonic_lower_bound (Nat.le_trans (Nat.le_max_right _ _) hN : 2 ^ m ≤ N)
  have hlt_fact : 2 * ((2 * D * N₀ + 1) * natFact N) < (m + 2) * natFact N := by
    rw [← Nat.mul_assoc]; exact Nat.mul_lt_mul_of_pos_right (by dsimp [m]; omega) (natFact_pos N)
  have hmul : 2 * (logExceptionalNum P N * D) < 2 * harmonicSumNum N := by
    rw [show 2 * (logExceptionalNum P N * D) = 2 * D * logExceptionalNum P N by ac_rfl, hlog_eq]
    omega
  omega

/-- Terras-Everett natural density `1` of `HasFiniteStoppingTime` via `HasNaturalDensityOne`. -/
theorem terras_hasNaturalDensityOne : HasNaturalDensityOne HasFiniteStoppingTime :=
  terras_natural_density_one_pos
/-- **Terras (1976) / Everett (1977) Logarithmic Density 1 (`KNOWN-004`):** almost all positive
integers in logarithmic density have finite stopping time (via Abel summation). -/
theorem terras_log_density_one : HasLogDensityOne HasFiniteStoppingTime :=
  hasLogDensityOne_of_hasNaturalDensityOne terras_hasNaturalDensityOne

/-! ### 3. Tao (2022) Almost-Bounded Interface, Syracuse Contraction & Barrier 4 Separation -/

/-- Predicate asserting `f : Nat → Nat` grows without bound (`liminf f(n) = ∞`). -/
def UnboundedBelow (f : Nat → Nat) : Prop := ∀ B : Nat, ∃ N₀ : Nat, ∀ n : Nat, N₀ ≤ n → B ≤ f n
/-- **Terence Tao (2022) Almost-Bounded Orbits Statement:** for every `UnboundedBelow f`,
logarithmic density `1` of integers satisfy `OrbitMinLe n (f n)`. -/
def TaoAlmostBoundedConjecture : Prop :=
  ∀ f : Nat → Nat, UnboundedBelow f → HasLogDensityOne (fun n => OrbitMinLe n (f n))
/-- Syracuse contraction predicate: some Syracuse iterate of `oddPart n` drops `≤ B`. -/
def HasSyracuseContraction (n B : Nat) : Prop := ∃ k : Nat, syracuseIter k (oddPart n) ≤ B
/-- Syracuse contraction implies standard `OrbitMinLe` in `Challenge.lean`. -/
theorem orbitMinLe_of_hasSyracuseContraction {n B : Nat} (hn : 0 < n)
    (h : HasSyracuseContraction n B) : OrbitMinLe n B := by
  rcases h with ⟨k, hk⟩; exact orbitMinLe_of_syracuse hn hk

private theorem two_pow_le_three_pow_nat (k : Nat) : 2 ^ k ≤ 3 ^ k := by
  induction k with | zero => decide | succ k _ =>
    rw [Nat.pow_succ, Nat.pow_succ]; have := Nat.two_pow_pos k; omega

/-- **Exact Syracuse Offset Bound:** for odd `n`, `2 ^ k * C(v) ≤ (3 ^ k - 2 ^ k) * 2 ^ S`. -/
theorem syracuseOffset_upper_bound (k : Nat) {n : Nat} (hn : n % 2 = 1) :
    2 ^ k * syracuseOffset k n ≤ (3 ^ k - 2 ^ k) * 2 ^ syracuseTotalVal k n := by
  induction k generalizing n with | zero => simp [syracuseOffset] | succ k ih =>
    have he := syracuseVal_pos hn; have hS' := syracuseTotalVal_ge k (syracuseStep_odd n)
    have h1 : 2 ^ (k + 1) * 3 ^ k ≤ 3 ^ k * 2 ^ syracuseTotalVal (k + 1) n := by
      rw [Nat.mul_comm (2 ^ (k + 1)) (3 ^ k)]
      exact Nat.mul_le_mul_left (3 ^ k) (Nat.pow_le_pow_right (by decide : 0 < 2)
        (by simp only [syracuseTotalVal]; omega))
    have h2 : 2 ^ (k + 1) * (2 ^ syracuseVal n * syracuseOffset k (syracuseStep n)) ≤
        (2 * 3 ^ k - 2 ^ (k + 1)) * 2 ^ syracuseTotalVal (k + 1) n := by
      have hmul := Nat.mul_le_mul_left (2 * 2 ^ syracuseVal n) (ih (syracuseStep_odd n))
      have hsub : 2 * (3 ^ k - 2 ^ k) = 2 * 3 ^ k - 2 ^ (k + 1) := by
        rw [Nat.mul_sub_left_distrib,
          show 2 * 2 ^ k = 2 ^ (k + 1) by rw [Nat.pow_succ, Nat.mul_comm]]
      rwa [show 2 * 2 ^ syracuseVal n * (2 ^ k * syracuseOffset k (syracuseStep n)) =
          2 ^ (k + 1) * (2 ^ syracuseVal n * syracuseOffset k (syracuseStep n)) by
        rw [Nat.pow_succ]; ac_rfl, show 2 * 2 ^ syracuseVal n *
          ((3 ^ k - 2 ^ k) * 2 ^ syracuseTotalVal k (syracuseStep n)) =
        (2 * 3 ^ k - 2 ^ (k + 1)) * 2 ^ syracuseTotalVal (k + 1) n by
        rw [← hsub, syracuseTotalVal, Nat.pow_add]; ac_rfl] at hmul
    have h2le3 : 2 ^ (k + 1) ≤ 2 * 3 ^ k := by
      have := two_pow_le_three_pow_nat k; rw [Nat.pow_succ]; omega
    simp only [syracuseOffset, Nat.mul_add]
    rw [show 3 ^ (k + 1) = 3 ^ k + 2 * 3 ^ k by rw [Nat.pow_succ]; omega,
      Nat.add_sub_assoc h2le3, Nat.add_mul]; omega

/-- **Syracuse Drift Contraction Bound:** if `3 ^ k * n ≤ B * 2 ^ S` for odd `n`, then
`2 ^ k * syracuseIter k n ≤ B * 2 ^ k + (3 ^ k - 2 ^ k)`. -/
theorem syracuseIter_le_of_drift {k n B : Nat} (hn : n % 2 = 1)
    (hdrift : 3 ^ k * n ≤ B * 2 ^ syracuseTotalVal k n) :
    2 ^ k * syracuseIter k n ≤ B * 2 ^ k + (3 ^ k - 2 ^ k) := by
  have hmul : 2 ^ syracuseTotalVal k n * (2 ^ k * syracuseIter k n) ≤
      2 ^ syracuseTotalVal k n * (B * 2 ^ k + (3 ^ k - 2 ^ k)) := by
    calc 2 ^ syracuseTotalVal k n * (2 ^ k * syracuseIter k n)
        = 2 ^ k * (3 ^ k * n) + 2 ^ k * syracuseOffset k n := by
            rw [show 2 ^ syracuseTotalVal k n * (2 ^ k * syracuseIter k n) =
              2 ^ k * (2 ^ syracuseTotalVal k n * syracuseIter k n) by ac_rfl,
              syracuse_affine_eq k n, Nat.mul_add]
      _ ≤ 2 ^ k * (B * 2 ^ syracuseTotalVal k n) + (3 ^ k - 2 ^ k) * 2 ^ syracuseTotalVal k n :=
          Nat.add_le_add (Nat.mul_le_mul_left _ hdrift) (syracuseOffset_upper_bound k hn)
      _ = 2 ^ syracuseTotalVal k n * (B * 2 ^ k + (3 ^ k - 2 ^ k)) := by rw [Nat.mul_add]; ac_rfl
  exact Nat.le_of_mul_le_mul_left hmul (Nat.two_pow_pos _)

/-- Exact affine drift condition yielding `HasSyracuseContraction n B`. -/
theorem hasSyracuseContraction_of_drift {k n B : Nat}
    (hdrift : 3 ^ k * oddPart n + syracuseOffset k (oddPart n) ≤
      B * 2 ^ syracuseTotalVal k (oddPart n)) : HasSyracuseContraction n B := by
  refine ⟨k, Nat.le_of_mul_le_mul_left ?_ (Nat.two_pow_pos (syracuseTotalVal k (oddPart n)))⟩
  rw [syracuse_affine_eq, Nat.mul_comm (2 ^ syracuseTotalVal k (oddPart n)) B]; exact hdrift

/-- Tao (2022) Syracuse random-walk contraction interface: every diverging target `f` is beaten
by `HasSyracuseContraction n (f n)` on a set of logarithmic density `1`. -/
def TaoSyracuseDriftHypothesis : Prop :=
  ∀ f : Nat → Nat, UnboundedBelow f → HasLogDensityOne (fun n => HasSyracuseContraction n (f n))

/-- Monotonicity of `HasLogDensityOne` for predicates holding from `1` onward. -/
theorem hasLogDensityOne_mono {P Q : Nat → Prop} (hPQ : ∀ n : Nat, 1 ≤ n → P n → Q n)
    (hP : HasLogDensityOne P) : HasLogDensityOne Q := by
  intro D hD; rcases hP D hD with ⟨N₀, hN₀⟩
  refine ⟨N₀, fun N hN => Nat.lt_of_le_of_lt (Nat.mul_le_mul_right D ?_) (hN₀ N hN)⟩
  refine natSum1_le (fun i hi1 _ => ?_)
  by_cases hQi : Q i
  · rw [dec_false (fun h => h hQi)]; simp
  · rw [dec_true hQi, dec_true (fun hPi => hQi (hPQ i hi1 hPi))]; simp

/-- `TaoSyracuseDriftHypothesis` implies `TaoAlmostBoundedConjecture`. -/
theorem taoAlmostBounded_of_syracuseDrift (h : TaoSyracuseDriftHypothesis) :
    TaoAlmostBoundedConjecture := fun f hf =>
  hasLogDensityOne_mono (fun _ hn hc => orbitMinLe_of_hasSyracuseContraction hn hc) (h f hf)

/-- Conjunction of two `HasLogDensityOne` properties still has `HasLogDensityOne`. -/
theorem hasLogDensityOne_and {P Q : Nat → Prop}
    (hP : HasLogDensityOne P) (hQ : HasLogDensityOne Q) :
    HasLogDensityOne (fun n => P n ∧ Q n) := by
  intro D hD; rcases hP (2 * D) (by omega) with ⟨N₁, hN₁⟩
  rcases hQ (2 * D) (by omega) with ⟨N₂, hN₂⟩; refine ⟨max N₁ N₂, fun N hN => ?_⟩
  have hle : logExceptionalNum (fun n => P n ∧ Q n) N ≤
      logExceptionalNum P N + logExceptionalNum Q N := by
    unfold logExceptionalNum; rw [← natSum1_add]; refine natSum1_le (fun i _ _ => ?_)
    by_cases hPi : P i <;> by_cases hQi : Q i
    · rw [dec_false (fun h => h ⟨hPi, hQi⟩)]; simp
    · rw [dec_true (fun h => hQi h.2), dec_false (fun h => h hPi), dec_true hQi]; simp
    · rw [dec_true (fun h => hPi h.1), dec_true hPi]; simp
    · rw [dec_true (fun h => hPi h.1), dec_true hPi, dec_true hQi]; exact Nat.le_add_right _ _
  have h1 : 2 * (logExceptionalNum P N * D) < harmonicSumNum N := by
    rw [show 2 * (logExceptionalNum P N * D) = logExceptionalNum P N * (2 * D) by ac_rfl]
    exact hN₁ N (Nat.le_trans (Nat.le_max_left _ _) hN)
  have h2 : 2 * (logExceptionalNum Q N * D) < harmonicSumNum N := by
    rw [show 2 * (logExceptionalNum Q N * D) = logExceptionalNum Q N * (2 * D) by ac_rfl]
    exact hN₂ N (Nat.le_trans (Nat.le_max_right _ _) hN)
  have hmul := Nat.le_trans (Nat.mul_le_mul_right D hle)
    (Nat.le_of_eq (Nat.add_mul (logExceptionalNum P N) (logExceptionalNum Q N) D))
  omega

/-- Any predicate true from `M` onward has logarithmic density `1`. -/
theorem hasLogDensityOne_of_cofinite (M : Nat) {P : Nat → Prop} (h : ∀ n : Nat, M ≤ n → P n) :
    HasLogDensityOne P := by
  intro D hD; refine ⟨2 ^ (2 * (M * D + 2)), fun N hN => ?_⟩
  have h1 : logExceptionalNum P N ≤ natSum1 N (fun i => if i < M then natFact N else 0) := by
    unfold logExceptionalNum; refine natSum1_le (fun i _ _ => ?_)
    by_cases hiM : i < M
    · simp only [hiM, ↓reduceIte]; split; exact Nat.div_le_self _ _; exact Nat.zero_le _
    · rw [dec_false (fun hn => hn (h i (Nat.le_of_not_lt hiM)))]; simp
  have h2 : ∀ k : Nat, natSum1 k (fun i => if i < M then natFact N else 0) ≤ min k M * natFact N :=
    fun k => by induction k with | zero => simp [natSum1] | succ j ih =>
      rw [natSum1]; by_cases hj : j + 1 < M
      · rw [ite_eq_left hj]; rw [show min j M = j by omega] at ih
        rw [show min (j + 1) M = j + 1 by omega, Nat.succ_mul]; omega
      · rw [ite_eq_right hj, Nat.add_zero]
        exact Nat.le_trans ih (Nat.mul_le_mul_right _ (by omega))
  have hle := Nat.le_trans h1 (Nat.le_trans (h2 N) (Nat.mul_le_mul_right _ (Nat.min_le_right _ _)))
  have hdyad := dyadic_harmonic_lower_bound hN
  have hlt : (2 * (M * D)) * natFact N < (2 * (M * D + 2) + 2) * natFact N :=
    Nat.mul_lt_mul_of_pos_right (by omega) (natFact_pos N)
  have hmul : 2 * (logExceptionalNum P N * D) ≤ (2 * (M * D)) * natFact N :=
    Nat.le_trans (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right D hle)) (Nat.le_of_eq (by ac_rfl))
  omega

/-- Eventual monotonicity of `HasLogDensityOne` (invariant under finitely many exceptions). -/
theorem hasLogDensityOne_eventually_mono {P Q : Nat → Prop} (M : Nat)
    (hPQ : ∀ n : Nat, M ≤ n → P n → Q n) (hP : HasLogDensityOne P) : HasLogDensityOne Q :=
  hasLogDensityOne_mono (fun n _ ⟨hp, hge⟩ => hPQ n hge hp)
    (hasLogDensityOne_and hP (hasLogDensityOne_of_cofinite M (fun _ h => h)))

private theorem mem_le_foldr_max {n : Nat} {S : List Nat} (hmem : n ∈ S) : n ≤ S.foldr max 0 := by
  induction S with | nil => cases hmem | cons x xs ih =>
    simp only [List.foldr_cons]
    exact (List.mem_cons.mp hmem).elim (fun h => h ▸ Nat.le_max_left _ _)
      (fun h => Nat.le_trans (ih h) (Nat.le_max_right _ _))
/-- Excluding any finite list `S` preserves `HasLogDensityOne`. -/
theorem hasLogDensityOne_avoiding_list {P : Nat → Prop} (hP : HasLogDensityOne P)
    (S : List Nat) : HasLogDensityOne (fun n => P n ∧ n ∉ S) :=
  hasLogDensityOne_eventually_mono (S.foldr max 0 + 1) (fun _ _ hPn =>
    ⟨hPn, fun hmem => by have := mem_le_foldr_max hmem; omega⟩) hP
/-- **Bridge Corollary:** `TaoAlmostBoundedConjecture` implies logarithmic density `1` for
`HasFiniteStoppingTime` (choosing `f n = n / 2`). -/
theorem tao_almost_bounded_implies_log_density_finite_stopping
    (hTao : TaoAlmostBoundedConjecture) : HasLogDensityOne HasFiniteStoppingTime := by
  have hub : UnboundedBelow (fun n => n / 2) := fun B => ⟨2 * B, fun n hn => by dsimp; omega⟩
  refine hasLogDensityOne_eventually_mono 2 (fun n hn h => ?_) (hTao (fun n => n / 2) hub)
  exact hasFiniteStoppingTime_of_orbitMinLe_lt (by omega : n / 2 < n) h
/-- Pure-`Nat` binary bit-length `bitLen n = ⌊log₂ n⌋ + 1` (with `bitLen 0 = 0`). -/
def bitLen : Nat → Nat | 0 => 0 | n + 1 => bitLen ((n + 1) / 2) + 1
termination_by n => n
decreasing_by omega
/-- Upper bound `n < 2 ^ bitLen n` for all `n`. -/
theorem lt_two_pow_bitLen (n : Nat) : n < 2 ^ bitLen n := by
  induction n using Nat.strongRecOn with | ind n ih => cases n with
    | zero => rw [bitLen]; decide
    | succ m => have := ih ((m + 1) / 2) (by omega); rw [bitLen, Nat.pow_succ]; omega
/-- Lower bound `2 ^ (bitLen n - 1) ≤ n` for all `1 ≤ n`. -/
theorem two_pow_pred_bitLen_le {n : Nat} (hn : 1 ≤ n) : 2 ^ (bitLen n - 1) ≤ n := by
  induction n using Nat.strongRecOn with | ind n ih => cases n with
    | zero => omega
    | succ m =>
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [bitLen, show (1 : Nat) / 2 = 0 by decide, bitLen]; decide
      · have hsub := ih ((m + 1) / 2) (by omega) (by omega)
        have hlen : 1 ≤ bitLen ((m + 1) / 2) := by
          cases h : (m + 1) / 2 with | zero => omega | succ k => rw [bitLen]; exact Nat.succ_pos _
        rw [bitLen, Nat.add_sub_cancel, show bitLen ((m + 1) / 2) =
          (bitLen ((m + 1) / 2) - 1) + 1 by omega, Nat.pow_succ]; omega
/-- `bitLen n` grows without bound (`UnboundedBelow bitLen`). -/
theorem bitLen_unbounded : UnboundedBelow bitLen := fun B => ⟨2 ^ B, fun n hn => by
  have hlt := lt_two_pow_bitLen n
  exact Nat.le_of_not_lt fun h =>
    absurd (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_lt h)) (by omega)⟩
/-- **Stronger Tao (2022) Corollary:** `TaoAlmostBoundedConjecture` implies logarithmic density `1`
for dropping below `bitLen n ≈ log₂ n` (strictly beyond Terras `1976`). -/
theorem tao_almost_bounded_implies_log_density_bitLen
    (hTao : TaoAlmostBoundedConjecture) : HasLogDensityOne (fun n => OrbitMinLe n (bitLen n)) :=
  hTao bitLen bitLen_unbounded
/-- Mersenne-family exceptions `2 ^ k - 1` (`k ≥ 2`), rising for `k` compressed steps
under Terras (`TerrasParity.terras_all_odd_rising`). -/
def IsMersenneException (n : Nat) : Prop := ∃ k : Nat, 2 ≤ k ∧ n = 2 ^ k - 1
private theorem countLt_mersenne_lt_le (M L : Nat) :
    countLt (fun n => @decide (∃ k : Nat, k < M ∧ n = 2 ^ k - 1)
      (Classical.propDecidable _)) L ≤ M := by
  have hconst : ∀ a L', countLt (fun n => decide (n = a)) L' ≤ 1 := fun a L' => by
    have hz : ∀ m, m ≤ a → countLt (fun n => decide (n = a)) m = 0 := fun m hm => by
      induction m with | zero => rfl | succ k ih =>
        rw [countLt, ih (by omega), decide_eq_false (by omega)]; rfl
    induction L' with | zero => exact Nat.zero_le 1 | succ L' ih =>
      rw [countLt]; by_cases h : L' = a
      · subst h; rw [hz L' (Nat.le_refl L')]; simp
      · rw [decide_eq_false h]; exact ih
  induction M with
  | zero =>
    have h0 := countLt_mono_pred L (q := fun _ => false)
      (p := fun n => @decide (∃ k : Nat, k < 0 ∧ n = 2 ^ k - 1) (Classical.propDecidable _))
      (fun i _ hi => by rcases of_dec_true hi with ⟨k, hk, _⟩; omega)
    have hz : countLt (fun _ => false) L = 0 := by
      clear h0; induction L with | zero => rfl | succ m ihm => simp [countLt, ihm]
    omega
  | succ M ih =>
    have hor := countLt_or_le
      (fun n => @decide (∃ k : Nat, k < M ∧ n = 2 ^ k - 1) (Classical.propDecidable _))
      (fun n => decide (n = 2 ^ M - 1)) L
    have hmono : countLt (fun n => @decide (∃ k : Nat, k < M + 1 ∧ n = 2 ^ k - 1)
        (Classical.propDecidable _)) L ≤ countLt (fun n => @decide (∃ k : Nat, k < M ∧
          n = 2 ^ k - 1) (Classical.propDecidable _) || decide (n = 2 ^ M - 1)) L := by
      refine countLt_mono_pred L (fun i _ hi => ?_); rcases of_dec_true hi with ⟨k, hk, rfl⟩
      by_cases hkM : k < M
      · rw [Bool.or_eq_true, dec_true ⟨k, hkM, rfl⟩]; exact Or.inl rfl
      · have heq : k = M := by omega
        subst heq; simp
    have hc := hconst (2 ^ M - 1) L; omega
/-- Number of `1 ≤ n ≤ N` in `{2^k - 1 | k ≥ 2}` is at most `bitLen (N + 1)`. -/
theorem natExceptionalCount_mersenne_le (N : Nat) :
    natExceptionalCount (fun n => ¬ IsMersenneException n) N ≤ bitLen (N + 1) := by
  have hmono : natExceptionalCount (fun n => ¬ IsMersenneException n) N ≤
      countLt (fun n => @decide (∃ k : Nat, k < bitLen (N + 1) ∧ n = 2 ^ k - 1)
        (Classical.propDecidable _)) (N + 1) := by
    unfold natExceptionalCount; refine countLt_mono_pred (N + 1) (fun n _ hdec => ?_)
    rcases of_dec_true hdec with ⟨_, hne⟩
    rcases Classical.byContradiction (fun hnot => hne hnot) with ⟨k, _, rfl⟩
    have hpow : 2 ^ k < 2 ^ bitLen (N + 1) := by
      have := lt_two_pow_bitLen (N + 1); have := Nat.two_pow_pos k; omega
    have hk_lt : k < bitLen (N + 1) :=
      Nat.lt_of_not_ge (fun h => absurd (Nat.pow_le_pow_right (by decide : 0 < 2) h) (by omega))
    exact dec_true ⟨k, hk_lt, rfl⟩
  exact Nat.le_trans hmono (countLt_mersenne_lt_le (bitLen (N + 1)) (N + 1))
private theorem linear_lt_two_pow_ge (x r : Nat) (hr : x + 4 ≤ r) : r * x < 2 ^ r := by
  have hbase : (x + 4) * x < 2 ^ (x + 4) := by
    have h2x : ∀ k : Nat, 2 * k + 5 ≤ 2 ^ (k + 4) := fun k => by
      induction k with | zero => decide | succ k ih => rw [Nat.pow_succ]; omega
    induction x with | zero => decide | succ x ih =>
      have hL : (x + 1 + 4) * (x + 1) = (x + 4) * x + (2 * x + 5) := by
        calc (x + 1 + 4) * (x + 1) = (x + 4) * x + (x + 4) + (x + 1) := by
              rw [show x + 1 + 4 = (x + 4) + 1 by omega, Nat.mul_add, Nat.add_mul,
                Nat.one_mul, Nat.mul_one]; omega
          _ = (x + 4) * x + (2 * x + 5) := by omega
      have hR : 2 ^ (x + 1 + 4) = 2 * 2 ^ (x + 4) := by
        rw [show x + 1 + 4 = (x + 4) + 1 by omega, Nat.pow_succ]; omega
      have h2 := h2x x; omega
  induction hr with | refl => exact hbase | @step k hk ih =>
    have hle : x + 4 ≤ k := hk
    have h1 := Nat.le_mul_of_pos_left x (Nat.le_trans (by omega : 1 ≤ x + 4) hle)
    calc (k + 1) * x = k * x + x := Nat.succ_mul k x
      _ < 2 ^ k + 2 ^ k := Nat.add_lt_add ih (Nat.lt_of_le_of_lt h1 ih)
      _ = 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
/-- The Mersenne rising family `{2 ^ k - 1 | k ≥ 2}` has natural density `0`. -/
theorem notMersenne_hasNaturalDensityOne :
    HasNaturalDensityOne (fun n => ¬ IsMersenneException n) := by
  intro D hD; let x := 4 * D; let m := x + 4; refine ⟨2 ^ (m + 1), fun N hN => ?_⟩
  let b := bitLen (N + 1)
  have hbit_ge : m + 1 ≤ b := by
    have hlt : N + 1 < 2 ^ b := lt_two_pow_bitLen (N + 1)
    exact Nat.le_of_not_lt fun h =>
      absurd (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_lt h)) (by omega)
  have h2pred : 2 ^ (b - 1) ≤ N + 1 := two_pow_pred_bitLen_le (Nat.succ_pos N)
  have hlin := linear_lt_two_pow_ge x (b - 1) (by dsimp [m] at hbit_ge; omega)
  have hbd : b + 1 ≤ (b - 1) * 4 := by dsimp [m, x] at hbit_ge; omega
  have hmul_bd : b * D + D ≤ (b - 1) * x := by
    calc b * D + D = (b + 1) * D := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ ((b - 1) * 4) * D := Nat.mul_le_mul_right D hbd
      _ = (b - 1) * x := by dsimp [x]; ac_rfl
  have hcnt : natExceptionalCount (fun n => ¬ IsMersenneException n) N ≤ b :=
    natExceptionalCount_mersenne_le N
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right D hcnt) (by omega)
/-- **Barrier 4 / Sparse Infinite Exception:** `{2 ^ k - 1 | k ≥ 2}` has logarithmic density `0`,
so its complement has logarithmic density `1` despite missing infinitely many integers. -/
theorem notMersenne_hasLogDensityOne :
    HasLogDensityOne (fun n => ¬ IsMersenneException n) :=
  hasLogDensityOne_of_hasNaturalDensityOne notMersenne_hasNaturalDensityOne
/-- **Zero-Density Separation (`PROVE-A1` Gap):** `HasLogDensityOne P` does not imply
`∀ n ≥ 1, P n`; infinitely many integers (`2 ^ k - 1`) can still fail `P`. -/
theorem hasLogDensityOne_not_implies_forall :
    ∃ P : Nat → Prop, HasLogDensityOne P ∧ ∀ M : Nat, ∃ n : Nat, M ≤ n ∧ ¬ P n := by
  refine ⟨fun n => ¬ IsMersenneException n, notMersenne_hasLogDensityOne, fun M => ?_⟩
  refine ⟨2 ^ (M + 2) - 1, ?_, fun h => h ⟨M + 2, by omega, rfl⟩⟩
  have hgt : M + 2 ≤ 2 ^ (M + 2) := by
    induction M with | zero => decide | succ M ih => rw [Nat.pow_succ]; omega
  omega
/-- Finite list of orbit states `{collatzIter j n | j < L}` of a cycle. -/
def cycleOrbitList (n L : Nat) : List Nat := (List.range L).map (fun j => collatzIter j n)
/-- **Cycle Compatibility Separation (`KNOWN-004` vs `PROVE-A1`):** `HasLogDensityOne` of finite
stopping times still permits avoiding any finite list `S` (including any putative cycle orbit). -/
theorem terras_log_density_one_allows_cycle (n L : Nat) :
    HasLogDensityOne (fun m => HasFiniteStoppingTime m ∧ m ∉ cycleOrbitList n L) :=
  hasLogDensityOne_avoiding_list terras_log_density_one (cycleOrbitList n L)

end SolveCollatz
