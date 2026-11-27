/-
Copyright (c) 2026 The solve-collatz contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Collatz.Prove.Ergodic.SharperChernoff
public import Collatz.Core.GeneralMaps

/-!
# Korec (1994) Polynomial Descent & Optimal Chernoff Ceilings (`PROVE-A1`, Phase 3)
Pure Lean 4 core formalization (zero Mathlib, zero reals, zero `native_decide`):
`HasPolynomialDrop a b n := ∃ t, (collatzIter t n)^b < n^a`; 1-bit shell criterion; constructive
Korec theorem (`korec_general_power_saving`: `3^b < 4^a` -> power-saving density `1`, instantiated
at `4/5`, `5/6`, `9/10`); and `log_4(3)` / `H_2(log_3 2)` ceilings + Barriers 1–5.
-/

@[expose] public section

namespace SolveCollatz

private theorem kd_dec_true {P : Prop} (h : P) : @decide P (Classical.propDecidable P) = true :=
  @decide_eq_true P (Classical.propDecidable P) h
private theorem kd_of_dec_true {P : Prop} (h : @decide P (Classical.propDecidable P) = true) : P :=
  @of_decide_eq_true P (Classical.propDecidable P) h
private theorem kd_pow_lt_of_ge {x y D M₀ M : Nat} (hy : 0 < y) (hxy : x ≤ y)
    (hbase : x ^ M₀ * D < y ^ M₀) (hM : M₀ ≤ M) : x ^ M * D < y ^ M := by
  by_cases hx : x = 0
  · subst hx; cases M₀ with
    | zero => simp at hbase; cases M with
      | zero => simpa using hbase | succ k => simp [hbase, Nat.pow_pos hy]
    | succ k => rw [Nat.zero_pow (by omega), Nat.zero_mul]; exact Nat.pow_pos hy
  · rw [(Nat.add_sub_of_le hM).symm, Nat.pow_add, Nat.pow_add, Nat.mul_right_comm _ (x ^ (M - M₀))]
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hbase
      (Nat.pow_pos (Nat.pos_of_ne_zero hx))) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hxy _))
private theorem nat_lt_of_pow_lt {x y k : Nat} (_hk : 0 < k) (h : x ^ k < y ^ k) : x < y :=
  Nat.lt_of_not_ge (fun hge => Nat.not_lt_of_ge (Nat.pow_le_pow_left hge k) h)
private theorem nat_le_of_pow_le {x y k : Nat} (hk : 0 < k) (h : x ^ k ≤ y ^ k) : x ≤ y :=
  Nat.le_of_not_lt (fun hlt => Nat.not_le_of_gt (Nat.pow_lt_pow_left hlt (Nat.ne_of_gt hk)) h)

/-! ### 1. Polynomial-Contraction Predicate & Core Bridges -/

/-- Pure-`Nat` polynomial contraction predicate: `collatzIter t n < n^(a/b)`. -/
def HasPolynomialDrop (a b n : Nat) : Prop := ∃ t : Nat, (collatzIter t n) ^ b < n ^ a

/-- Bounded-step variant of `HasPolynomialDrop` within `K` standard Collatz steps. -/
def HasBoundedPolynomialDrop (a b K n : Nat) : Prop :=
  ∃ t : Nat, t ≤ K ∧ (collatzIter t n) ^ b < n ^ a

/-- Any bounded polynomial drop yields `HasPolynomialDrop`. -/
theorem hasPolynomialDrop_of_bounded {a b K n : Nat} (h : HasBoundedPolynomialDrop a b K n) :
    HasPolynomialDrop a b n := let ⟨t, _, ht⟩ := h; ⟨t, ht⟩

/-- `0` never has a polynomial drop for `a > 0`. -/
theorem not_hasPolynomialDrop_zero {a b : Nat} (ha : 0 < a) : ¬ HasPolynomialDrop a b 0 := by
  rintro ⟨_, hlt⟩; rw [Nat.zero_pow ha] at hlt; omega

/-- `1` never has a polynomial drop (`collatzIter t 1 ≥ 1`). -/
theorem not_hasPolynomialDrop_one (a b : Nat) : ¬ HasPolynomialDrop a b 1 := by
  rintro ⟨t, hlt⟩
  have : 1 ≤ (collatzIter t 1) ^ b := Nat.pow_pos (collatzIter_pos t (by decide : 0 < 1))
  rw [Nat.one_pow] at hlt; omega
/-- Any `HasPolynomialDrop a b n` with `a ≤ b` and `1 ≤ n` forces `t > 0`. -/
theorem hasPolynomialDrop_iff_pos {a b n : Nat} (hab : a ≤ b) (hn : 1 ≤ n) :
    HasPolynomialDrop a b n ↔ ∃ t : Nat, 0 < t ∧ (collatzIter t n) ^ b < n ^ a := by
  refine ⟨fun ⟨t, hlt⟩ => ?_, fun ⟨t, _, hlt⟩ => ⟨t, hlt⟩⟩
  cases t with
  | zero => simp only [collatzIter] at hlt; have := Nat.pow_le_pow_right hn hab; omega
  | succ t' => exact ⟨t' + 1, Nat.succ_pos t', hlt⟩
/-- **Direct Bridge to `HasFiniteStoppingTime`:** polynomial contraction (`a ≤ b`) implies
finite stopping time for every `n ≥ 1`. -/
theorem korec_drop_implies_finite_stopping {a b n : Nat} (hb : 0 < b) (hab : a ≤ b) (hn : 1 ≤ n)
    (h : HasPolynomialDrop a b n) : HasFiniteStoppingTime n := by
  rcases (hasPolynomialDrop_iff_pos hab hn).mp h with ⟨t, ht0, hlt⟩
  exact ⟨t, ht0, nat_lt_of_pow_lt hb (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right hn hab))⟩
/-- Monotonicity of `HasPolynomialDrop a b n` in the rational exponent `a / b`. -/
theorem hasPolynomialDrop_mono_exp {a b c d n : Nat} (hb : 0 < b) (hd : 0 < d) (hn : 1 ≤ n)
    (hfrac : a * d ≤ c * b) (h : HasPolynomialDrop a b n) : HasPolynomialDrop c d n := by
  rcases h with ⟨t, hlt⟩; refine ⟨t, nat_lt_of_pow_lt hb ?_⟩
  have h1 : ((collatzIter t n) ^ d) ^ b < (n ^ a) ^ d := by
    rw [← Nat.pow_mul, Nat.mul_comm d b, Nat.pow_mul]
    exact Nat.pow_lt_pow_left hlt (Nat.ne_of_gt hd)
  rw [← Nat.pow_mul, ← Nat.pow_mul]
  exact Nat.lt_of_lt_of_le (by rwa [← Nat.pow_mul, ← Nat.pow_mul] at h1)
    (Nat.pow_le_pow_right hn hfrac)
/-- Any `terrasIter k n` drop below `n^(a/b)` gives `HasBoundedPolynomialDrop a b (2 * k) n`. -/
theorem hasBoundedPolynomialDrop_of_terras {a b k n : Nat} (hlt : (terrasIter k n) ^ b < n ^ a) :
    HasBoundedPolynomialDrop a b (2 * k) n := by
  refine ⟨k + countOnes (terrasParityVec k n), ?_, by rw [collatzIter_eq_terrasIter]; exact hlt⟩
  have hlen := countOnes_le_length (terrasParityVec k n); rw [terrasParityVec_length] at hlen; omega
/-- Any `terrasIter k n` drop below `n^(a/b)` gives `HasPolynomialDrop a b n`. -/
theorem hasPolynomialDrop_of_terras {a b k n : Nat} (hlt : (terrasIter k n) ^ b < n ^ a) :
    HasPolynomialDrop a b n := hasPolynomialDrop_of_bounded (hasBoundedPolynomialDrop_of_terras hlt)
/-- If `b ≤ a`, `HasFiniteStoppingTime n` yields `HasPolynomialDrop a b n` for `n ≥ 1`. -/
theorem hasPolynomialDrop_of_finiteStopping {a b n : Nat} (hb : 0 < b) (hba : b ≤ a) (hn : 1 ≤ n)
    (h : HasFiniteStoppingTime n) : HasPolynomialDrop a b n := by
  rcases h with ⟨t, _, hlt⟩
  exact ⟨t, Nat.lt_of_lt_of_le (Nat.pow_lt_pow_left hlt (Nat.ne_of_gt hb))
    (Nat.pow_le_pow_right hn hba)⟩

/-! ### 2. Sharp 1-Bit Dyadic Shell Criterion & Korec Bad Residues -/

/-- Korec bad-residue indicator: `2^(k*a) < 2^b * 3^(b * countOnes (terrasParityVec k r))`. -/
def badKorecResidue (a b k r : Nat) : Bool :=
  decide (2 ^ (k * a) < 2 ^ b * 3 ^ (b * countOnes (terrasParityVec k r)))

/-- Count of Korec-bad residues `r < 2^k` modulo `2^k`. -/
def badKorecCount (a b k : Nat) : Nat := countLt (badKorecResidue a b k) (2 ^ k)

/-- Combinatorial expression for `badKorecCount a b k` via `allBitVecs k`. -/
theorem badKorecCount_eq_filter_allBitVecs (a b k : Nat) :
    badKorecCount a b k = ((allBitVecs k).filter
      (fun v => decide (2 ^ (k * a) < 2 ^ b * 3 ^ (b * countOnes v)))).length := by
  let p : List Bool → Bool := fun v => decide (2 ^ (k * a) < 2 ^ b * 3 ^ (b * countOnes v))
  have hlen := ((map_terrasParityVec_perm_allBitVecs k).filter p).length_eq
  rw [List.filter_map, List.length_map] at hlen
  have hcomp : p ∘ terrasParityVec k = badKorecResidue a b k := rfl
  rw [badKorecCount, countLt_eq_filter_range, ← hcomp, hlen]

/-- **Sharp 1-Bit Shell Dropping Criterion:** for `n ∈ [2^k, 2^(k+1))`, if
`2^b * 3^(b*c) ≤ 2^(k*a)`, then `(terrasIter k n)^b < n^a`, hence `HasPolynomialDrop a b n`. -/
theorem terras_korec_drop_on_shell {a b k n : Nat} (hb : 0 < b)
    (hlo : 2 ^ k ≤ n) (hhi : n < 2 ^ (k + 1))
    (hgood : 2 ^ b * 3 ^ (b * countOnes (terrasParityVec k (n % 2 ^ k))) ≤ 2 ^ (k * a)) :
    (terrasIter k n) ^ b < n ^ a ∧ HasBoundedPolynomialDrop a b (2 * k) n ∧
      HasPolynomialDrop a b n := by
  let r := n % 2 ^ k; let c := countOnes (terrasParityVec k r)
  have hkpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hq : n / 2 ^ k = 1 := by
    have hge : 1 ≤ n / 2 ^ k := (Nat.le_div_iff_mul_le hkpos).mpr (by rw [Nat.one_mul]; exact hlo)
    have hlt : n / 2 ^ k < 2 :=
      (Nat.div_lt_iff_lt_mul hkpos).mpr (by rw [Nat.mul_comm, ← Nat.pow_succ]; exact hhi)
    omega
  have hmod := terrasIter_mod_eq k n; rw [← terrasParityVec_mod_eq k n, hq, Nat.mul_one] at hmod
  have hrem := terrasIter_lt_three_pow_countOnes k r (Nat.mod_lt n hkpos)
  have hlt2 : terrasIter k n < 2 * 3 ^ c := by
    change terrasIter k r < 3 ^ c at hrem
    change terrasIter k n = terrasIter k r + 3 ^ c at hmod; omega
  have hpow_b : (terrasIter k n) ^ b < 2 ^ b * 3 ^ (b * c) := by
    have h1 := Nat.pow_lt_pow_left hlt2 (Nat.ne_of_gt hb)
    rwa [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm c b] at h1
  have hna : 2 ^ (k * a) ≤ n ^ a := by rw [Nat.pow_mul]; exact Nat.pow_le_pow_left hlo a
  have hdrop := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hpow_b hgood) hna
  exact ⟨hdrop, hasBoundedPolynomialDrop_of_terras hdrop, hasPolynomialDrop_of_terras hdrop⟩

/-- Cumulative `badKorecCount` over 1-bit dyadic shells `[2^m, 2^(m+1))` for `m < M`. -/
def korecShellSum (a b : Nat) : Nat → Nat
  | 0 => 0
  | M + 1 => korecShellSum a b M + badKorecCount a b M

private theorem korec_shell_step_le (a b M : Nat) (hb : 0 < b) :
    countLt (fun i => @decide (¬ HasPolynomialDrop a b (2 ^ M + i))
      (Classical.propDecidable _)) (2 ^ M) ≤ badKorecCount a b M := by
  unfold badKorecCount; refine countLt_mono_pred (2 ^ M) (fun i hi hdec => ?_)
  by_cases hbad : badKorecResidue a b M i = true
  · exact hbad
  · exfalso
    have hgood : 2 ^ b * 3 ^ (b * countOnes (terrasParityVec M ((2 ^ M + i) % 2 ^ M))) ≤
        2 ^ (M * a) := by
      rw [show (2 ^ M + i) % 2 ^ M = i by rw [Nat.add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt hi]]
      exact Nat.le_of_not_lt (fun hlt => absurd (decide_eq_true hlt) hbad)
    exact (kd_of_dec_true hdec)
      (terras_korec_drop_on_shell hb (by omega) (by rw [Nat.pow_succ]; omega) hgood).2.2
/-- **1-Bit Dyadic Shell Counting Bound:** on `[0, 2^M)`, failures of `HasPolynomialDrop a b`
are bounded by `1 + korecShellSum a b M`. -/
theorem korec_dyadic_shell_bound {a b : Nat} (hb : 0 < b) (M : Nat) :
    countLt (fun n => @decide (¬ HasPolynomialDrop a b n) (Classical.propDecidable _)) (2 ^ M) ≤
      1 + korecShellSum a b M := by
  induction M with | zero => exact countLt_le _ 1 | succ M ih =>
    rw [show 2 ^ (M + 1) = 2 ^ M + 2 ^ M by rw [Nat.pow_succ]; omega, countLt_add]
    have hstep := korec_shell_step_le a b M hb; simp only [korecShellSum]; omega

/-! ### 3. General Pure-`Nat` Tilted Chernoff Engine & Shell Power-Saving Lift -/

private theorem kd_listSum_mul_left {α : Type} (c : Nat) (f : α → Nat) (l : List α) :
    listSum (fun x => c * f x) l = c * listSum f l := by
  induction l with | nil => simp [listSum] | cons x xs ih => simp [listSum, ih, Nat.mul_add]
private theorem kd_listSum_markov {α : Type} (p : α → Bool) (f : α → Nat) (T : Nat) (l : List α)
    (hle : ∀ x : α, x ∈ l → p x = true → T ≤ f x) : (l.filter p).length * T ≤ listSum f l := by
  induction l with | nil => simp [listSum] | cons x xs ih =>
    have hih := ih (fun y hy => hle y (List.mem_cons_of_mem x hy))
    cases hp : p x
    · simp only [List.filter, hp, listSum]; omega
    · have hx := hle x List.mem_cons_self hp
      simp only [List.filter, hp, listSum, List.length_cons, Nat.succ_mul]; omega
private theorem cherWeight_tilted_pow_le {u w n d b k : Nat} {v : List Bool}
    (h3 : 3 ^ n * u ^ d ≤ w ^ d) (hc : countOnes v ≤ k) :
    3 ^ (b * countOnes v * n) * u ^ (k * b * d) ≤ (cherWeight u w k v) ^ (b * d) := by
  let c := countOnes v; have hpow := Nat.pow_le_pow_left h3 (b * c)
  rw [Nat.mul_pow, ← Nat.pow_mul 3 n (b * c), Nat.mul_comm n (b * c),
    ← Nat.pow_mul u d (b * c), ← Nat.pow_mul w d (b * c)] at hpow
  have hexp : b * d * (k - c) + d * (b * c) = k * b * d := by
    rw [show d * (b * c) = b * d * c by ac_rfl, ← Nat.mul_add, Nat.sub_add_cancel hc]; ac_rfl
  have hw : (cherWeight u w k v) ^ (b * d) = u ^ (b * d * (k - c)) * w ^ (d * (b * c)) := by
    simp only [cherWeight, Nat.mul_pow, ← Nat.pow_mul]
    rw [Nat.mul_comm (k - c) (b * d), show c * (b * d) = d * (b * c) by ac_rfl]
  rw [hw,
    show u ^ (k * b * d) = u ^ (b * d * (k - c)) * u ^ (d * (b * c)) by rw [← Nat.pow_add, hexp],
    show 3 ^ (b * c * n) * (u ^ (b * d * (k - c)) * u ^ (d * (b * c))) =
      u ^ (b * d * (k - c)) * (3 ^ (b * c * n) * u ^ (d * (b * c))) by ac_rfl]
  exact Nat.mul_le_mul_left _ hpow
private theorem cherWeight_korec_pointwise {a b u w p_num p_den n d k : Nat}
    (hb : 0 < b) (hu : 0 < u) (hpden : 0 < p_den) (hn1 : 1 ≤ n) (hnd : n ≤ d)
    (h3 : 3 ^ n * u ^ d ≤ w ^ d) (h2 : p_num ^ (b * d) ≤ p_den ^ (b * d) * 2 ^ (a * n))
    {v : List Bool} (hv : v ∈ allBitVecs k) (hbad : 2 ^ (k * a) < 2 ^ b * 3 ^ (b * countOnes v)) :
    (p_num * u) ^ k ≤ 2 * p_den ^ k * cherWeight u w k v := by
  let c := countOnes v; have hc : c ≤ k := (mem_allBitVecs_iff k v).mp hv ▸ countOnes_le_length v
  have hbad_n : 2 ^ (k * a * n) < 2 ^ (b * n) * 3 ^ (b * c * n) := by
    have hpow := Nat.pow_lt_pow_left hbad (Nat.ne_of_gt hn1)
    rwa [← Nat.pow_mul, Nat.mul_pow, ← Nat.pow_mul 2 b n, ← Nat.pow_mul 3 (b * c) n] at hpow
  have h2pow : p_num ^ (k * b * d) ≤ p_den ^ (k * b * d) * 2 ^ (k * a * n) := by
    have hpow := Nat.pow_le_pow_left h2 k
    rwa [← Nat.pow_mul, Nat.mul_pow, ← Nat.pow_mul p_den (b * d) k, ← Nat.pow_mul 2 (a * n) k,
      Nat.mul_comm (b * d) k, ← Nat.mul_assoc k b d, Nat.mul_comm (a * n) k,
      ← Nat.mul_assoc k a n] at hpow
  have h3pow := cherWeight_tilted_pow_le (k := k) (b := b) (v := v) h3 hc
  have h2bd : 2 ^ (b * n) ≤ 2 ^ (b * d) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.mul_le_mul_left b hnd)
  have hlhs : ((p_num * u) ^ k) ^ (b * d) = p_num ^ (k * b * d) * u ^ (k * b * d) := by
    rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul]; ac_rfl
  have hrhs : (2 * p_den ^ k * cherWeight u w k v) ^ (b * d) =
      p_den ^ (k * b * d) * (2 ^ (b * d) * (cherWeight u w k v) ^ (b * d)) := by
    rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul p_den k (b * d), ← Nat.mul_assoc k b d]; ac_rfl
  have hcomb : ((p_num * u) ^ k) ^ (b * d) < (2 * p_den ^ k * cherWeight u w k v) ^ (b * d) := by
    rw [hlhs, hrhs]
    calc _ ≤ (p_den ^ (k * b * d) * 2 ^ (k * a * n)) * u ^ (k * b * d) :=
          Nat.mul_le_mul_right _ h2pow
      _ = (p_den ^ (k * b * d) * u ^ (k * b * d)) * 2 ^ (k * a * n) := by ac_rfl
      _ < (p_den ^ (k * b * d) * u ^ (k * b * d)) * (2 ^ (b * n) * 3 ^ (b * c * n)) :=
          Nat.mul_lt_mul_of_pos_left hbad_n (Nat.mul_pos (Nat.pow_pos hpden) (Nat.pow_pos hu))
      _ = p_den ^ (k * b * d) * (2 ^ (b * n) * (3 ^ (b * c * n) * u ^ (k * b * d))) := by ac_rfl
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul h2bd h3pow)
  exact Nat.le_of_lt (nat_lt_of_pow_lt (Nat.mul_pos hb (by omega)) hcomb)

/-- **General Pure-`Nat` Tilted Chernoff Decay:** for any rational tilt
`3^n * u^d ≤ w^d` (`1 ≤ n ≤ d`) and `p_num^(b*d) ≤ p_den^(b*d) * 2^(a*n)`,
`badKorecCount a b k * (2 * p_num * u)^k ≤ 2 * (2 * (p_den * (u + w)))^k`. -/
theorem badKorecCount_chernoff {a b u w p_num p_den n d : Nat}
    (hb : 0 < b) (hu : 0 < u) (hpden : 0 < p_den) (hn1 : 1 ≤ n) (hnd : n ≤ d)
    (h3 : 3 ^ n * u ^ d ≤ w ^ d) (h2 : p_num ^ (b * d) ≤ p_den ^ (b * d) * 2 ^ (a * n))
    (k : Nat) : badKorecCount a b k * (2 * p_num * u) ^ k ≤ 2 * (2 * (p_den * (u + w))) ^ k := by
  rw [badKorecCount_eq_filter_allBitVecs]
  have hmarkov := kd_listSum_markov
    (fun v => decide (2 ^ (k * a) < 2 ^ b * 3 ^ (b * countOnes v)))
    (fun v => 2 * p_den ^ k * cherWeight u w k v) ((p_num * u) ^ k) (allBitVecs k)
    (fun v hv hp => cherWeight_korec_pointwise hb hu hpden hn1 hnd h3 h2 hv (of_decide_eq_true hp))
  rw [kd_listSum_mul_left, cherWeight_allBitVecs_sum] at hmarkov
  have hmul := Nat.mul_le_mul_right (2 ^ k) hmarkov
  have hl : (p_num * u) ^ k * 2 ^ k = (2 * p_num * u) ^ k := by rw [← Nat.mul_pow]; congr 1; ac_rfl
  have hr : 2 * p_den ^ k * (u + w) ^ k * 2 ^ k = 2 * (2 * (p_den * (u + w))) ^ k := by
    rw [Nat.mul_assoc 2 (p_den ^ k) ((u + w) ^ k), ← Nat.mul_pow p_den (u + w) k,
      Nat.mul_assoc 2 _ (2 ^ k), ← Nat.mul_pow (p_den * (u + w)) 2 k, Nat.mul_comm _ 2]
  rwa [Nat.mul_assoc, hl, hr] at hmul

/-- Geometric shell-sum recurrence for 1-bit dyadic shells. -/
def korecGeomSum (X Y : Nat) : Nat → Nat
  | 0 => 0
  | M + 1 => Y * korecGeomSum X Y M + X ^ M * Y

private theorem korecGeomSum_bound {X Y : Nat} (hXY : Y < X) (M : Nat) :
    (X - Y) * korecGeomSum X Y M ≤ Y * X ^ M := by
  induction M with
  | zero => simp [korecGeomSum]
  | succ M ih =>
    simp only [korecGeomSum, Nat.mul_add, Nat.pow_succ]
    have h1 : (X - Y) * (Y * korecGeomSum X Y M) ≤ Y * (Y * X ^ M) := by
      rw [Nat.mul_left_comm (X - Y) Y]; exact Nat.mul_le_mul_left Y ih
    have h2 : Y * (Y * X ^ M) + (X - Y) * (X ^ M * Y) = Y * (X ^ M * X) := by
      rw [show Y * (Y * X ^ M) + (X - Y) * (X ^ M * Y) = Y * X ^ M * (Y + (X - Y)) by
        rw [Nat.mul_add]; ac_rfl, Nat.add_sub_of_le (Nat.le_of_lt hXY)]; ac_rfl
    exact Nat.le_trans (Nat.add_le_add_right h1 _) (Nat.le_of_eq h2)
private theorem korecShellSum_chernoff_bound {a b u w p_num p_den n d : Nat}
    (hb : 0 < b) (hu : 0 < u) (hpden : 0 < p_den) (hn1 : 1 ≤ n) (hnd : n ≤ d)
    (h3 : 3 ^ n * u ^ d ≤ w ^ d) (h2 : p_num ^ (b * d) ≤ p_den ^ (b * d) * 2 ^ (a * n)) (M : Nat) :
    korecShellSum a b M * (2 * p_num * u) ^ M ≤
      2 * korecGeomSum (2 * (p_den * (u + w))) (2 * p_num * u) M := by
  induction M with
  | zero => simp [korecShellSum, korecGeomSum]
  | succ M ih =>
    simp only [korecShellSum, korecGeomSum, Nat.add_mul]
    have h1 : korecShellSum a b M * (2 * p_num * u) ^ (M + 1) ≤
        2 * ((2 * p_num * u) * korecGeomSum (2 * (p_den * (u + w))) (2 * p_num * u) M) := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]
      calc _ ≤ (2 * korecGeomSum (2 * (p_den * (u + w))) (2 * p_num * u) M) * (2 * p_num * u) :=
              Nat.mul_le_mul_right _ ih
        _ = _ := by rw [Nat.mul_assoc, Nat.mul_comm _ (2 * p_num * u)]
    have h2' : badKorecCount a b M * (2 * p_num * u) ^ (M + 1) ≤
        2 * ((2 * (p_den * (u + w))) ^ M * (2 * p_num * u)) := by
      have hc := badKorecCount_chernoff hb hu hpden hn1 hnd h3 h2 M
      rw [Nat.pow_succ, ← Nat.mul_assoc]
      exact Nat.le_trans (Nat.mul_le_mul_right _ hc) (Nat.le_of_eq (Nat.mul_assoc 2 _ _))
    rw [Nat.mul_add]; exact Nat.add_le_add h1 h2'
private theorem witness_B_lt_two_A {a b u w p_num p_den n d : Nat}
    (hb : 0 < b) (hab : a ≤ b) (hu : 0 < u) (hpden : 0 < p_den) (hn1 : 1 ≤ n) (hnd : n ≤ d)
    (h3 : 3 ^ n * u ^ d ≤ w ^ d) (h2 : p_num ^ (b * d) ≤ p_den ^ (b * d) * 2 ^ (a * n)) :
    2 * p_num * u < 2 * (p_den * (u + w)) := by
  have hd_pos : 0 < d := by omega
  have hu_lt_w : u < w := by
    have h3ge : 3 ≤ 3 ^ n := Nat.le_self_pow (Nat.ne_of_gt hn1) 3
    have hlt := Nat.mul_lt_mul_of_pos_right (by omega : 1 < 3 ^ n) (Nat.pow_pos hu : 0 < u ^ d)
    rw [Nat.one_mul] at hlt; exact nat_lt_of_pow_lt hd_pos (Nat.lt_of_lt_of_le hlt h3)
  have hp_le : p_num ≤ 2 * p_den := by
    have h2le : 2 ^ (a * n) ≤ 2 ^ (b * d) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.mul_le_mul hab hnd)
    have hpow : p_num ^ (b * d) ≤ (2 * p_den) ^ (b * d) := by
      rw [Nat.mul_pow, Nat.mul_comm (2 ^ (b * d))]
      exact Nat.le_trans h2 (Nat.mul_le_mul_left _ h2le)
    exact nat_le_of_pow_le (Nat.mul_pos hb hd_pos) hpow
  have hpu : p_num * u ≤ p_den * (2 * u) := by
    rw [show p_den * (2 * u) = 2 * p_den * u by ac_rfl]; exact Nat.mul_le_mul_right u hp_le
  have hlt := Nat.mul_lt_mul_of_pos_left (by omega : 2 * u < u + w) hpden
  calc 2 * p_num * u = 2 * (p_num * u) := Nat.mul_assoc _ _ _
    _ ≤ 2 * (p_den * (2 * u)) := Nat.mul_le_mul_left 2 hpu
    _ < 2 * (p_den * (u + w)) := Nat.mul_lt_mul_of_pos_left hlt (by decide)

/-- **Master 1-Bit Shell Bound:** on `[0, 2^M)`, failures of `HasPolynomialDrop a b` satisfy
`count * (2*A - B) * B^M ≤ (2*A + B) * (2*A)^M` for `A = p_den*(u+w)` and `B = 2*p_num*u`. -/
theorem korec_shell_master_bound {a b u w p_num p_den n d : Nat}
    (hb : 0 < b) (hab : a ≤ b) (hu : 0 < u) (hpden : 0 < p_den) (hn1 : 1 ≤ n) (hnd : n ≤ d)
    (h3 : 3 ^ n * u ^ d ≤ w ^ d) (h2 : p_num ^ (b * d) ≤ p_den ^ (b * d) * 2 ^ (a * n)) (M : Nat) :
    let A := p_den * (u + w); let B := 2 * p_num * u
    countLt (fun n => @decide (¬ HasPolynomialDrop a b n) (Classical.propDecidable _)) (2 ^ M) *
        (2 * A - B) * B ^ M ≤ (2 * A + B) * (2 * A) ^ M := by
  intro A B; have hBA := witness_B_lt_two_A hb hab hu hpden hn1 hnd h3 h2
  have hsh := Nat.mul_le_mul_right ((2 * A - B) * B ^ M) (korec_dyadic_shell_bound (a := a) hb M)
  rw [Nat.add_mul, Nat.one_mul] at hsh
  have h1 := Nat.mul_le_mul_left (2 * A - B) (Nat.pow_le_pow_left (Nat.le_of_lt hBA) M)
  have h2' : korecShellSum a b M * ((2 * A - B) * B ^ M) ≤ 2 * B * (2 * A) ^ M := calc
    _ = (2 * A - B) * (korecShellSum a b M * B ^ M) := by ac_rfl
    _ ≤ (2 * A - B) * (2 * korecGeomSum (2 * A) B M) :=
        Nat.mul_le_mul_left _ (korecShellSum_chernoff_bound hb hu hpden hn1 hnd h3 h2 M)
    _ = 2 * ((2 * A - B) * korecGeomSum (2 * A) B M) := by ac_rfl
    _ ≤ 2 * (B * (2 * A) ^ M) := Nat.mul_le_mul_left 2 (korecGeomSum_bound hBA M)
    _ = 2 * B * (2 * A) ^ M := (Nat.mul_assoc 2 B _).symm
  have hcomb := Nat.le_trans hsh (Nat.add_le_add h1 h2')
  rw [← Nat.add_mul, show (2 * A - B) + 2 * B = 2 * A + B by omega] at hcomb; rwa [Nat.mul_assoc]

private theorem korec_prefix_pow_split {c A B C D p q M N : Nat} (hpq : p ≤ q)
    (h2M : 2 ^ M ≤ 2 * N) (hpref : c * D * B ^ M ≤ C * (2 * A) ^ M) :
    c ^ q * (D ^ q * B ^ (q * M)) ≤ C ^ q * (2 ^ p * N ^ p * (2 ^ (q - p) * A ^ q) ^ M) := by
  have hgec : c ^ q * (D ^ q * B ^ (q * M)) = (c * D * B ^ M) ^ q := by
    rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul B M q, Nat.mul_comm M q, Nat.mul_assoc]
  have h2p : (2 ^ M) ^ p ≤ 2 ^ p * N ^ p := by rw [← Nat.mul_pow]; exact Nat.pow_le_pow_left h2M p
  have hR : (C * (2 * A) ^ M) ^ q = C ^ q * ((2 ^ M) ^ p * ((2 ^ (q - p) * A ^ q) ^ M)) := by
    rw [Nat.mul_pow, Nat.mul_pow 2 A M, Nat.mul_pow (2 ^ M) (A ^ M) q, show (2 ^ M) ^ q =
        (2 ^ M) ^ p * (2 ^ M) ^ (q - p) by rw [← Nat.pow_add, Nat.add_sub_of_le hpq],
      Nat.mul_pow (2 ^ (q - p)) (A ^ q) M, ← Nat.pow_mul 2 M (q - p), ← Nat.pow_mul 2 (q - p) M,
      Nat.mul_comm M (q - p), ← Nat.pow_mul A M q, ← Nat.pow_mul A q M, Nat.mul_comm M q,
      Nat.mul_assoc ((2 ^ M) ^ p)]
  calc _ = (c * D * B ^ M) ^ q := hgec
    _ ≤ (C * (2 * A) ^ M) ^ q := Nat.pow_le_pow_left hpref q
    _ ≤ _ := by rw [hR]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h2p)
private theorem korec_bitLen_two_mul {N : Nat} (hN : 1 ≤ N) : 2 ^ bitLen N ≤ 2 * N := by
  have hM1 : 1 ≤ bitLen N := Nat.pos_of_ne_zero (fun h0 => by
    have hlt := lt_two_pow_bitLen N; simp [h0] at hlt; omega)
  rw [show bitLen N = (bitLen N - 1) + 1 from (Nat.sub_add_cancel hM1).symm, Nat.pow_succ,
    Nat.mul_comm]; exact Nat.mul_le_mul_left 2 (two_pow_pred_bitLen_le hN)

/-- **General Witness-to-PowerSaving Lift:** any pure-`Nat` Chernoff witness `(u, w, p_num,
p_den, n, d)` with `2^(q - p) * (p_den * (u + w))^q < (2 * p_num * u)^q` gives unconditional
`HasPowerSavingDensityOne (HasPolynomialDrop a b) p q`. -/
theorem korec_powerSaving_of_witness {a b u w p_num p_den n d p q : Nat}
    (hb : 0 < b) (hab : a ≤ b) (hu : 0 < u) (hpden : 0 < p_den) (hn1 : 1 ≤ n) (hnd : n ≤ d)
    (h3 : 3 ^ n * u ^ d ≤ w ^ d) (h2 : p_num ^ (b * d) ≤ p_den ^ (b * d) * 2 ^ (a * n))
    (hpq : p < q) (hratio : 2 ^ (q - p) * (p_den * (u + w)) ^ q < (2 * p_num * u) ^ q) :
    HasPowerSavingDensityOne (HasPolynomialDrop a b) p q := by
  let A := p_den * (u + w); let B := 2 * p_num * u; let D := 2 * A - B; let C := 2 * A + B
  have hBA := witness_B_lt_two_A hb hab hu hpden hn1 hnd h3 h2
  have hBpos : 0 < B := Nat.pos_of_ne_zero (fun h0 => by
    have hlt : 0 < B ^ q := Nat.lt_of_le_of_lt (Nat.zero_le _) hratio
    rw [h0, Nat.zero_pow (by omega : 0 < q)] at hlt; omega)
  rcases pow_mul_lt_pow_of_lt (Nat.mul_pos (Nat.two_pow_pos _) (Nat.pow_pos
    (Nat.mul_pos hpden (by omega)))) hratio
    (Nat.mul_pos (Nat.pow_pos (by omega : 0 < 2 * A + B)) (Nat.two_pow_pos p)) with ⟨M₀, _, hdom⟩
  refine ⟨2 ^ M₀, fun N hN => ?_⟩; let M := bitLen N
  have hM : M₀ ≤ M := Nat.le_of_not_lt (fun hltM => Nat.not_lt_of_ge hN
    (Nat.lt_trans (lt_two_pow_bitLen N) (Nat.pow_lt_pow_right (by decide : 1 < 2) hltM)))
  have hNpos : 1 ≤ N := Nat.le_trans (Nat.two_pow_pos _) hN
  have hcnt_le : natExceptionalCount (HasPolynomialDrop a b) N ≤ countLt
      (fun n => @decide (¬ HasPolynomialDrop a b n) (Classical.propDecidable _)) (2 ^ M) := by
    unfold natExceptionalCount
    exact Nat.le_trans (countLt_mono_pred (N + 1) (fun _ _ hn => kd_dec_true (kd_of_dec_true hn).2))
      (countLt_mono_bound _ (lt_two_pow_bitLen N))
  have hpref := Nat.le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hcnt_le))
    (korec_shell_master_bound hb hab hu hpden hn1 hnd h3 h2 M)
  have hpowq := korec_prefix_pow_split (Nat.le_of_lt hpq) (korec_bitLen_two_mul hNpos) hpref
  have hdrop : natExceptionalCount (HasPolynomialDrop a b) N ^ q * B ^ (q * M) ≤
      natExceptionalCount (HasPolynomialDrop a b) N ^ q * (D ^ q * B ^ (q * M)) :=
    Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by dsimp [D]; omega)))
  have hdomM := kd_pow_lt_of_ge (Nat.pow_pos hBpos) (Nat.le_of_lt hratio) hdom hM
  rw [← Nat.pow_mul B q M] at hdomM
  have hfin : natExceptionalCount (HasPolynomialDrop a b) N ^ q * B ^ (q * M) <
      N ^ p * B ^ (q * M) := calc
    _ ≤ C ^ q * (2 ^ p * N ^ p * (2 ^ (q - p) * A ^ q) ^ M) := Nat.le_trans hdrop hpowq
    _ = N ^ p * ((2 ^ (q - p) * A ^ q) ^ M * (C ^ q * 2 ^ p)) := by ac_rfl
    _ < N ^ p * B ^ (q * M) := Nat.mul_lt_mul_of_pos_left hdomM (Nat.pow_pos hNpos)
  exact Nat.lt_of_mul_lt_mul_right hfin

/-! ### 4. General Korec Theorem (`3^b < 4^a`) & Concrete Flagship Bounds -/

private theorem bernoulli_lower (t x k : Nat) : t ^ k + k * t ^ (k - 1) * x ≤ (t + x) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.pow_succ (t + x), Nat.mul_add]
    cases k with
    | zero => simp
    | succ k' =>
      have h1 : t ^ (k' + 2) + (k' + 1) * t ^ (k' + 1) * x ≤ (t + x) ^ (k' + 1) * t := by
        have hm := Nat.mul_le_mul_right t ih
        rw [Nat.add_mul, ← Nat.pow_succ t (k' + 1), show (k' + 1) * t ^ (k' + 1 - 1) * x * t =
          (k' + 1) * t ^ (k' + 1) * x by
            rw [show k' + 1 - 1 = k' by omega, Nat.mul_right_comm ((k' + 1) * t ^ k') x t,
              Nat.mul_assoc (k' + 1) (t ^ k') t, ← Nat.pow_succ t k']] at hm; exact hm
      have h2 := Nat.mul_le_mul_right x (Nat.pow_le_pow_left (by omega : t ≤ t + x) (k' + 1))
      rw [show k' + 1 + 1 - 1 = k' + 1 by omega, Nat.add_mul (k' + 1) 1, Nat.one_mul,
        Nat.add_mul, show k' + 1 + 1 = k' + 2 by omega]; omega
private theorem bernoulli_upper_step {M x k : Nat} (hkx : (k + 1) * x ≤ M) :
    (M + x) * (M - (k + 1) * x) ≤ M * (M - k * x) := by
  let r := M - (k + 1) * x; have hM : M = (k + 1) * x + r := (Nat.add_sub_of_le hkx).symm
  have hMk : M - k * x = x + r := by have := Nat.add_mul k 1 x; omega
  rw [hMk]; conv => lhs; rw [hM]
  conv => rhs; rw [hM]
  have hL : ((k + 1) * x + r + x) * ((k + 1) * x + r - (k + 1) * x) =
      (k + 1) * x * r + r * r + x * r := by rw [Nat.add_sub_cancel_left, Nat.add_mul, Nat.add_mul]
  have hR : ((k + 1) * x + r) * (x + r) = (k + 1) * x * x + (k + 1) * x * r + r * x + r * r := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
  rw [hL, hR, Nat.mul_comm r x]; omega
private theorem bernoulli_upper (M x k : Nat) (hkx : k * x ≤ M) :
    (M + x) ^ k * (M - k * x) ≤ M ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ih' := ih (Nat.le_trans (Nat.mul_le_mul_right x (Nat.le_succ k)) hkx)
    calc _ = (M + x) ^ k * ((M + x) * (M - (k + 1) * x)) := by rw [Nat.pow_succ]; ac_rfl
      _ ≤ (M + x) ^ k * (M * (M - k * x)) := Nat.mul_le_mul_left _ (bernoulli_upper_step hkx)
      _ = M * ((M + x) ^ k * (M - k * x)) := by ac_rfl
      _ ≤ M * M ^ (k + 1) := Nat.mul_le_mul_left M ih'
      _ = M ^ (k + 2) := by rw [Nat.pow_succ M (k + 1), Nat.mul_comm]
private def findMinGe (f : Nat → Nat) (target : Nat) : Nat → Nat
  | 0 => 0
  | fuel + 1 => let z := findMinGe f target fuel; if target ≤ f z then z else fuel + 1
private theorem findMinGe_aux (f : Nat → Nat) (target : Nat) (hf0 : f 0 < target) :
    ∀ fuel : Nat, (target ≤ f (findMinGe f target fuel) ∧ 0 < findMinGe f target fuel ∧
        f (findMinGe f target fuel - 1) < target) ∨
      (findMinGe f target fuel = fuel ∧ f fuel < target)
  | 0 => Or.inr ⟨rfl, hf0⟩
  | fuel + 1 => by
    simp only [findMinGe]; by_cases hle : target ≤ f (findMinGe f target fuel)
    · rw [ite_eq_left hle]; rcases findMinGe_aux f target hf0 fuel with hL | hR
      · exact Or.inl hL
      · exfalso; rw [hR.1] at hle; omega
    · rw [ite_eq_right hle]; rcases findMinGe_aux f target hf0 fuel with hL | hR
      · exact absurd hL.1 hle
      · by_cases hnext : target ≤ f (fuel + 1)
        · exact Or.inl ⟨hnext, Nat.succ_pos fuel, by simpa using hR.2⟩
        · exact Or.inr ⟨rfl, Nat.lt_of_not_le hnext⟩
private theorem korec_shell_findMin_spec (d t : Nat) (hd : 0 < d) (ht : 0 < t) :
    let z := findMinGe (fun x => (t + x) ^ d) (3 * t ^ d) (2 * t)
    3 * t ^ d ≤ (t + z) ^ d ∧ 0 < z ∧ (t + (z - 1)) ^ d < 3 * t ^ d := by
  have hf0 : (t + 0) ^ d < 3 * t ^ d := by
    rw [Nat.add_zero]; have := (Nat.pow_pos ht : 0 < t ^ d); omega
  have hfN : 3 * t ^ d ≤ (t + 2 * t) ^ d := by
    rw [show t + 2 * t = 3 * t by omega, Nat.mul_pow]
    exact Nat.mul_le_mul_right _ (Nat.le_self_pow (Nat.ne_of_gt hd) 3)
  exact (findMinGe_aux (fun x => (t + x) ^ d) (3 * t ^ d) hf0 (2 * t)).elim id fun hR =>
    absurd hR.2 (Nat.not_lt_of_ge hfN)
private theorem expand_sq_add (u v : Nat) : (u + v) ^ 2 = u * u + 2 * v * u + v ^ 2 := by
  rw [Nat.pow_two, Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_assoc 2 v u,
    Nat.two_mul (v * u), Nat.mul_comm u v]; omega
private theorem korec_quad_bound {a b : Nat} (hb : 0 < b) :
    let d := 8 * b * 4 ^ a; let t := d * d
    let z := findMinGe (fun x => (t + x) ^ d) (3 * t ^ d) (2 * t); let y := (z + 1) / 2
    (t + y + 1) ^ 2 * d ^ 2 ≤ t * (t + (z - 1)) * (d ^ 2 + 6) := by
  intro d t z y
  have hd8 : 8 ≤ d := Nat.le_trans (by decide : 8 ≤ 8 * 1 * 1)
    (Nat.mul_le_mul (Nat.mul_le_mul_left 8 hb) (Nat.pow_pos (by decide : 0 < 4) : 1 ≤ 4 ^ a))
  have htpos : 0 < t := Nat.mul_pos (by omega) (by omega)
  have hspec := korec_shell_findMin_spec d t (by omega) htpos
  have hdz : d * (z - 1) < 2 * t := by
    have hlt := Nat.lt_of_le_of_lt (bernoulli_lower t (z - 1) d) hspec.2.2
    have htd : t ^ (d - 1) * t = t ^ d := by
      conv => rhs; rw [show d = (d - 1) + 1 by omega, Nat.pow_succ]
    have hlt2 : d * (z - 1) * t ^ (d - 1) < 2 * t * t ^ (d - 1) := by
      rw [show d * (z - 1) * t ^ (d - 1) = d * t ^ (d - 1) * (z - 1) by ac_rfl,
        show 2 * t * t ^ (d - 1) = 2 * t ^ d by rw [Nat.mul_assoc, Nat.mul_comm t, htd]]
      omega
    exact Nat.lt_of_mul_lt_mul_right hlt2
  have hz_lt : z - 1 < 2 * d := Nat.lt_of_mul_lt_mul_left
    (show d * (z - 1) < d * (2 * d) from (show 2 * t = d * (2 * d) by dsimp [t]; ac_rfl) ▸ hdz)
  have hy_sq : (y + 1) ^ 2 ≤ 2 * t := by
    have h1 := Nat.pow_le_pow_left (by dsimp [y]; omega : y + 1 ≤ d + 2) 2
    have h2 : (d + 2) ^ 2 = d * d + 4 * d + 4 := by
      rw [expand_sq_add d 2, show 2 * 2 * d = 4 * d by omega, show 2 ^ 2 = 4 by decide]
    have h8d : 8 * d ≤ d * d := Nat.mul_le_mul_right d hd8
    exact Nat.le_trans h1 (by rw [h2]; omega : (d + 2) ^ 2 ≤ 2 * (d * d))
  have hm : 2 * (y + 1) * t ≤ t * (z - 1) + 4 * t := by
    rw [Nat.mul_comm t (z - 1), ← Nat.add_mul]; exact Nat.mul_le_mul_right t (by dsimp [y]; omega)
  have hLHS : (t + y + 1) ^ 2 ≤ t * (t + (z - 1)) + 6 * t := by
    rw [Nat.add_assoc t y 1, expand_sq_add t (y + 1), Nat.mul_add t t (z - 1)]; omega
  have hmul := Nat.mul_le_mul_right (d ^ 2) hLHS
  have h6 : 6 * t * d ^ 2 ≤ 6 * (t * (t + (z - 1))) := by
    rw [Nat.pow_two d, show 6 * t * (t) = 6 * (t * t) by ac_rfl]
    exact Nat.mul_le_mul_left 6 (Nat.mul_le_mul_left t (Nat.le_add_right t _))
  rw [Nat.add_mul] at hmul; rw [Nat.mul_add _ (d ^ 2) 6, Nat.mul_comm (t * (t + (z - 1))) 6]; omega
private theorem korec_34_d_gap {a b : Nat} (hb : 0 < b) (h34 : 3 ^ b < 4 ^ a) :
    let d := 8 * b * 4 ^ a; 3 ^ b * d ^ 2 < 4 ^ a * (d ^ 2 - 6 * b * d) := by
  intro d; have h4a : 1 ≤ 4 ^ a := Nat.pow_pos (by decide)
  have hd_pos : 0 < d := by dsimp [d]; exact Nat.mul_pos (Nat.mul_pos (by decide) hb) h4a
  have h1 : 3 ^ b * d ≤ (4 ^ a - 1) * d := Nat.mul_le_mul_right d (by omega)
  have h2 : (4 ^ a - 1) * d = 4 ^ a * d - d := by rw [Nat.sub_mul, Nat.one_mul]
  have h68 : 4 ^ a * (6 * b) < d := by
    rw [show d = 4 ^ a * (8 * b) by dsimp [d]; ac_rfl]
    exact Nat.mul_lt_mul_of_pos_left (by omega) h4a
  have h3' : 4 ^ a * d - d < 4 ^ a * (d - 6 * b) := by
    rw [Nat.mul_sub_left_distrib]; have := Nat.le_mul_of_pos_left d h4a; omega
  have hm := Nat.mul_lt_mul_of_pos_right (Nat.lt_of_le_of_lt (h2 ▸ h1) h3') hd_pos
  rw [Nat.mul_assoc (3 ^ b) d d, ← Nat.pow_two, Nat.mul_assoc (4 ^ a) (d - 6 * b) d,
    Nat.mul_sub_right_distrib, ← Nat.pow_two] at hm; exact hm
private theorem korec_witness_hmul_lt {a b d t z y : Nat} (hb : 0 < b) (h34 : 3 ^ b < 4 ^ a)
    (hd_def : d = 8 * b * 4 ^ a) (hd_pos : 0 < d) (htpos : 0 < t)
    (hquad : (t + y + 1) ^ 2 * d ^ 2 ≤ t * (t + (z - 1)) * (d ^ 2 + 6))
    (hlt3 : (t + (z - 1)) ^ d < 3 * t ^ d) :
    (t + y + 1) ^ (2 * (b * d)) * ((d ^ 2) ^ (b * d) * (d ^ 2 - 6 * b * d)) <
      (2 ^ a * t ^ (b * d)) ^ 2 * ((d ^ 2) ^ (b * d) * (d ^ 2 - 6 * b * d)) := by
  have h4a : 1 ≤ 4 ^ a := Nat.pow_pos (by decide); have hd2_pos : 0 < d ^ 2 := Nat.pow_pos hd_pos
  have hquad_pow : (t + y + 1) ^ (2 * (b * d)) * (d ^ 2) ^ (b * d) ≤
      t ^ (b * d) * (t + (z - 1)) ^ (b * d) * (d ^ 2 + 6) ^ (b * d) := by
    have hq := Nat.pow_le_pow_left hquad (b * d)
    rwa [Nat.mul_pow, ← Nat.pow_mul (t + y + 1) 2 (b * d),
      Nat.mul_pow (t * (t + (z - 1))) (d ^ 2 + 6), Nat.mul_pow t (t + (z - 1)) (b * d)] at hq
  have h6bd : 6 * b < d := by
    rw [hd_def]
    exact Nat.lt_of_lt_of_le (by omega : 6 * b < 8 * b * 1) (Nat.mul_le_mul_left (8 * b) h4a)
  have hup := bernoulli_upper (d ^ 2) 6 (b * d) (by
    rw [Nat.pow_two, show b * d * 6 = 6 * b * d by ac_rfl]; exact Nat.mul_le_mul_right d (by omega))
  have hsub_pos : 0 < d ^ 2 - 6 * b * d := by
    have := Nat.mul_lt_mul_of_pos_right h6bd hd_pos; rw [Nat.pow_two]; omega
  have hpow3 : (t + (z - 1)) ^ (b * d) < 3 ^ b * t ^ (b * d) := by
    have hlt := Nat.pow_lt_pow_left hlt3 (Nat.ne_of_gt hb)
    rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm d b] at hlt; exact hlt
  have hrhs_eq : 4 ^ a * (d ^ 2 - 6 * b * d) * (t ^ (2 * (b * d)) * (d ^ 2) ^ (b * d)) =
      (2 ^ a * t ^ (b * d)) ^ 2 * ((d ^ 2) ^ (b * d) * (d ^ 2 - 6 * b * d)) := by
    have h42 : 4 ^ a = (2 ^ a) ^ 2 := by
      rw [show (4 : Nat) = 2 ^ 2 by decide, ← Nat.pow_mul, Nat.mul_comm 2 a, Nat.pow_mul]
    rw [h42, Nat.mul_pow (2 ^ a) (t ^ (b * d)) 2, ← Nat.pow_mul t (b * d) 2,
      Nat.mul_comm (b * d) 2]; ac_rfl
  calc _ = ((t + y + 1) ^ (2 * (b * d)) * (d ^ 2) ^ (b * d)) * (d ^ 2 - 6 * b * d) := by ac_rfl
    _ ≤ (t ^ (b * d) * (t + (z - 1)) ^ (b * d) * (d ^ 2 + 6) ^ (b * d)) * (d ^ 2 - 6 * b * d) :=
        Nat.mul_le_mul_right _ hquad_pow
    _ = (t ^ (b * d) * (t + (z - 1)) ^ (b * d)) *
          ((d ^ 2 + 6) ^ (b * d) * (d ^ 2 - 6 * b * d)) := by ac_rfl
    _ ≤ (t ^ (b * d) * (t + (z - 1)) ^ (b * d)) * (d ^ 2) ^ (b * d + 1) :=
        Nat.mul_le_mul_left _ (by rw [show b * d * 6 = 6 * b * d by ac_rfl] at hup; exact hup)
    _ < (t ^ (b * d) * (3 ^ b * t ^ (b * d))) * (d ^ 2) ^ (b * d + 1) :=
        Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_left hpow3 (Nat.pow_pos htpos))
          (Nat.pow_pos hd2_pos)
    _ = (3 ^ b * d ^ 2) * (t ^ (2 * (b * d)) * (d ^ 2) ^ (b * d)) := by
        rw [Nat.pow_succ (d ^ 2), show 2 * (b * d) = b * d + b * d by omega, Nat.pow_add]; ac_rfl
    _ < (4 ^ a * (d ^ 2 - 6 * b * d)) * (t ^ (2 * (b * d)) * (d ^ 2) ^ (b * d)) :=
        Nat.mul_lt_mul_of_pos_right (hd_def ▸ korec_34_d_gap hb h34)
          (Nat.mul_pos (Nat.pow_pos htpos) (Nat.pow_pos hd2_pos))
    _ = _ := hrhs_eq
private theorem korec_witness_exists_of_lt {a b : Nat} (hb : 0 < b) (h34 : 3 ^ b < 4 ^ a) :
    ∃ u w p_num p_den d : Nat, 0 < u ∧ 0 < p_den ∧ 1 ≤ d ∧ 3 ^ 1 * u ^ d ≤ w ^ d ∧
      p_num ^ (b * d) ≤ p_den ^ (b * d) * 2 ^ (a * 1) ∧ p_den * (u + w) < 2 * p_num * u := by
  let d := 8 * b * 4 ^ a; let t := d * d
  let z := findMinGe (fun x => (t + x) ^ d) (3 * t ^ d) (2 * t); let y := (z + 1) / 2
  have hd_pos : 0 < d := by
    dsimp [d]; exact Nat.mul_pos (Nat.mul_pos (by decide) hb) (Nat.pow_pos (by decide))
  have htpos : 0 < t := Nat.mul_pos hd_pos hd_pos
  have hspec := korec_shell_findMin_spec d t hd_pos htpos
  have h3_u : 3 ^ 1 * t ^ d ≤ (t + 2 * y) ^ d := by
    rw [Nat.pow_one]; exact Nat.le_trans hspec.1 (Nat.pow_le_pow_left (by dsimp [y]; omega) d)
  have hsq_lt : ((t + y + 1) ^ (b * d)) ^ 2 < (2 ^ a * t ^ (b * d)) ^ 2 := by
    rw [← Nat.pow_mul, Nat.mul_comm (b * d) 2]
    exact Nat.lt_of_mul_lt_mul_right (korec_witness_hmul_lt hb h34 rfl hd_pos htpos
      (korec_quad_bound (a := a) hb) hspec.2.2)
  have h2_p : (t + y + 1) ^ (b * d) ≤ t ^ (b * d) * 2 ^ (a * 1) := by
    rw [Nat.mul_one, Nat.mul_comm (t ^ (b * d)) (2 ^ a)]
    exact Nat.le_of_lt (nat_lt_of_pow_lt (by decide) hsq_lt)
  have h3_gap : t * (t + (t + 2 * y)) < 2 * (t + y + 1) * t := by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_left_comm t 2 y]
    have hR : 2 * (t + y + 1) * t = t * t + t * t + 2 * (t * y) + 2 * t := by
      simp only [Nat.mul_add, Nat.add_mul, Nat.two_mul]; ac_rfl
    omega
  exact ⟨t, t + 2 * y, t + y + 1, t, d, htpos, htpos, hd_pos, h3_u, h2_p, h3_gap⟩
private theorem bernoulli_gap_mul_power {A D q C : Nat} (hA : 0 < A) (hC : 0 < C)
    (hq : A < q * D) : 2 * (A * C) ^ q < ((A + D) * C) ^ q := by
  have h1 : 2 * A ^ q < (A + D) ^ q := by
    have hb := bernoulli_lower A D q; cases q with
    | zero => simp at hq
    | succ k =>
      have hmul : 2 * A ^ (k + 1) = A ^ (k + 1) + A * A ^ k := by
        rw [Nat.pow_succ A k, Nat.mul_comm (A ^ k) A]; omega
      have hlt : A * A ^ k < (k + 1) * A ^ k * D := by
        rw [Nat.mul_comm A (A ^ k), Nat.mul_right_comm (k + 1) (A ^ k) D,
          Nat.mul_comm ((k + 1) * D)]
        exact Nat.mul_lt_mul_of_pos_left hq (Nat.pow_pos hA)
      simp only [Nat.add_sub_cancel] at hb; omega
  have hm := Nat.mul_lt_mul_of_pos_right h1 (Nat.pow_pos hC : 0 < C ^ q)
  rwa [Nat.mul_assoc 2, ← Nat.mul_pow A C q, ← Nat.mul_pow (A + D) C q] at hm

/-- **Korec's General Theorem (1994, Pure Lean 4 Core):**
For EVERY positive `a, b` with `3^b < 4^a` (`a/b > log_4(3) ≈ 0.792481`),
`HasPolynomialDrop a b` (`∃ t, (collatzIter t n)^b < n^a`) holds with unconditional
power-saving density `1` (`HasPowerSavingDensityOne (HasPolynomialDrop a b) p q`). -/
theorem korec_general_power_saving {a b : Nat} (_ha : 0 < a) (hb : 0 < b) (h34 : 3 ^ b < 4 ^ a) :
    ∃ p q : Nat, 0 < p ∧ p < q ∧ HasPowerSavingDensityOne (HasPolynomialDrop a b) p q := by
  by_cases hab : a < b
  · rcases korec_witness_exists_of_lt hb h34 with
      ⟨u, w, p_num, p_den, d, hu, hpden, hd1, h3, h2, hgap⟩
    let A := p_den * (u + w); have hApos : 0 < A := Nat.mul_pos hpden (by omega)
    have hratio : 2 ^ ((A + 1) - A) * A ^ (A + 1) < (2 * p_num * u) ^ (A + 1) := by
      have hm := bernoulli_gap_mul_power hApos (by decide : 0 < 1) (by omega : A < (A + 1) * 1)
      simp only [Nat.mul_one] at hm; rw [show (A + 1) - A = 1 by omega, Nat.pow_one]
      exact Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_left hgap (A + 1))
    refine ⟨A, A + 1, hApos, Nat.lt_succ_self A, korec_powerSaving_of_witness hb (Nat.le_of_lt hab)
      hu hpden (by decide) hd1 h3 h2 (Nat.lt_succ_self A) hratio⟩
  · have hba : b ≤ a := Nat.le_of_not_lt hab
    rcases sharper_power_saving_density_19_20 with ⟨N₀, hN₀⟩
    refine ⟨19, 20, by decide, by decide, N₀, fun N hN => ?_⟩
    have hle : natExceptionalCount (HasPolynomialDrop a b) N ≤
        natExceptionalCount HasFiniteStoppingTime N := by
      unfold natExceptionalCount; exact countLt_mono_pred (N + 1) (fun n _ hn =>
        let h1 := kd_of_dec_true hn
        kd_dec_true ⟨h1.1, fun hs => h1.2 (hasPolynomialDrop_of_finiteStopping hb hba h1.1 hs)⟩)
    exact Nat.lt_of_le_of_lt (Nat.pow_le_pow_left hle 20) (hN₀ N hN)

/-- Every Korec exponent `a / b > log_4(3)` (`3^b < 4^a`) has natural and log density `1`. -/
theorem korec_general_density_one {a b : Nat} (ha : 0 < a) (hb : 0 < b) (h34 : 3 ^ b < 4 ^ a) :
    HasNaturalDensityOne (HasPolynomialDrop a b) ∧ HasLogDensityOne (HasPolynomialDrop a b) := by
  rcases korec_general_power_saving ha hb h34 with ⟨p, q, hp, hpq, hpow⟩
  exact ⟨hasNaturalDensityOne_of_powerSaving hp hpq hpow,
    hasLogDensityOne_of_powerSaving hp hpq hpow⟩

private theorem pow_49_3_4_5 : 3 * 50000 ^ 49 ≤ 51134 ^ 49 := by decide
private theorem pow_245_2_4_5 : 50569 ^ (5 * 49) ≤ 50000 ^ (5 * 49) * 2 ^ (4 * 1) := by decide

/-- **Flagship Korec Bound (`n^(4/5) = n^0.80`):** almost all `n` drop below `n^(4/5)` with
explicit unconditional power saving `O(N^(25283/25284))` (within `0.0075` of `log_4(3)`!). -/
theorem korec_drop_4_5 : HasPowerSavingDensityOne (HasPolynomialDrop 4 5) 25283 25284 := by
  have hratio : 2 ^ (25284 - 25283) * (50000 * (50000 + 51134)) ^ 25284 <
      (2 * 50569 * 50000) ^ 25284 := by
    have hm := bernoulli_gap_mul_power (A := 50567) (D := 2) (q := 25284) (C := 100000)
      (by decide) (by decide) (by decide)
    rw [show 50567 * 100000 = 50000 * (50000 + 51134) by decide,
      show (50567 + 2) * 100000 = 2 * 50569 * 50000 by decide] at hm
    rwa [show (25284 - 25283 : Nat) = 1 by decide, Nat.pow_one]
  exact korec_powerSaving_of_witness (n := 1) (d := 49) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) pow_49_3_4_5 pow_245_2_4_5 (by decide) hratio

private theorem pow_11_3_5_6 : 3 * 10000 ^ 11 ≤ 11051 ^ 11 := by decide
private theorem pow_66_2_5_6 : 10539 ^ (6 * 11) ≤ 10000 ^ (6 * 11) * 2 ^ (5 * 1) := by decide

/-- **Concrete Korec Bound (`n^(5/6) ≈ n^0.8333`):** unconditional power saving `O(N^(779/780))`. -/
theorem korec_drop_5_6 : HasPowerSavingDensityOne (HasPolynomialDrop 5 6) 779 780 := by
  have hratio : 2 ^ (780 - 779) * (10000 * (10000 + 11051)) ^ 780 <
      (2 * 10539 * 10000) ^ 780 := by
    have hm := bernoulli_gap_mul_power (A := 2339) (D := 3) (q := 780) (C := 90000)
      (by decide) (by decide) (by decide)
    rw [show 2339 * 90000 = 10000 * (10000 + 11051) by decide,
      show (2339 + 3) * 90000 = 2 * 10539 * 10000 by decide] at hm
    rwa [show (780 - 779 : Nat) = 1 by decide, Nat.pow_one]
  exact korec_powerSaving_of_witness (n := 1) (d := 11) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) pow_11_3_5_6 pow_66_2_5_6 (by decide) hratio

private theorem pow_4_3_9_10 : 3 * 1000 ^ 4 ≤ 1317 ^ 4 := by decide
private theorem pow_40_2_9_10 : 1168 ^ (10 * 4) ≤ 1000 ^ (10 * 4) * 2 ^ (9 * 1) := by decide
private theorem pow_86_9_10 : 2 * 2317 ^ 86 < 2336 ^ 86 := by decide

/-- **Concrete Korec Bound (`n^(9/10) = n^0.90`):** unconditional power saving `O(N^(85/86))`. -/
theorem korec_drop_9_10 : HasPowerSavingDensityOne (HasPolynomialDrop 9 10) 85 86 := by
  have hratio : 2 ^ (86 - 85) * (1000 * (1000 + 1317)) ^ 86 < (2 * 1168 * 1000) ^ 86 := by
    have hm := Nat.mul_lt_mul_of_pos_right pow_86_9_10 (Nat.pow_pos (by decide) : 0 < 1000 ^ 86)
    rw [Nat.mul_assoc 2, ← Nat.mul_pow 2317 1000, ← Nat.mul_pow 2336 1000,
      show 2317 * 1000 = 1000 * (1000 + 1317) by decide,
      show 2336 * 1000 = 2 * 1168 * 1000 by decide] at hm
    rwa [show (86 - 85 : Nat) = 1 by decide, Nat.pow_one]
  exact korec_powerSaving_of_witness (n := 1) (d := 4) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) pow_4_3_9_10 pow_40_2_9_10 (by decide) hratio

/-! ### 5. Exact Information-Theoretic Ceilings & Barriers 1–5 -/

private theorem countOnes_map_not (v : List Bool) :
    countOnes (v.map not) + countOnes v = v.length := by
  induction v with | nil => rfl | cons b bs ih => cases b <;> simp [countOnes] <;> omega
private theorem filter_length_add_not {α : Type} (p : α → Bool) (l : List α) :
    (l.filter p).length + (l.filter (fun x => !p x)).length = l.length := by
  induction l with
  | nil => rfl | cons x xs ih => cases hp : p x <;> simp [List.filter, hp] <;> omega
private theorem allBitVecs_length (k : Nat) : (allBitVecs k).length = 2 ^ k := by
  induction k with | zero => rfl | succ k ih =>
    rw [allBitVecs, List.length_append, List.length_map, List.length_map, ih, Nat.pow_succ]; omega
private theorem nodup_length_le_of_inj {α : Type} [BEq α] [LawfulBEq α]
    (g : α → α) (hinv : ∀ x : α, g (g x) = x) :
    ∀ l₁ l₂ : List α, l₁.Nodup → (∀ x : α, x ∈ l₁ → g x ∈ l₂) → l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, l₂, hnd, hmem => by
    rw [List.nodup_cons] at hnd; have hgx : g x ∈ l₂ := hmem x List.mem_cons_self
    have hsub := nodup_length_le_of_inj g hinv xs (l₂.erase (g x)) hnd.2 (fun y hy => by
      have hne : g y ≠ g x := fun heq => hnd.1 (by
        have := congrArg g heq; rw [hinv, hinv] at this; exact this ▸ hy)
      exact (List.mem_erase_of_ne hne).mpr (hmem y (List.mem_cons_of_mem x hy)))
    have her := List.length_erase_of_mem hgx; have hl2 := List.length_pos_of_mem hgx
    simp only [List.length_cons]; omega

/-- At least half of all `k`-bit parity vectors have `k ≤ 2 * countOnes v`. -/
theorem half_bitVecs_heavy (k : Nat) :
    2 ^ k ≤ 2 * ((allBitVecs k).filter (fun v => decide (k ≤ 2 * countOnes v))).length := by
  let p : List Bool → Bool := fun v => decide (k ≤ 2 * countOnes v)
  have hsum := filter_length_add_not p (allBitVecs k); rw [allBitVecs_length] at hsum
  have hle : ((allBitVecs k).filter (fun v => !p v)).length ≤ ((allBitVecs k).filter p).length := by
    refine nodup_length_le_of_inj (List.map not) (fun v => by induction v <;> simp [*]) _ _
      ((allBitVecs_nodup k).filter _) (fun v hv => ?_)
    rw [List.mem_filter] at hv ⊢
    have hlen : v.length = k := (mem_allBitVecs_iff k v).mp hv.1
    have hnot : 2 * countOnes v < k := by
      have hpv : p v = false := by revert hv; cases p v <;> simp
      exact Nat.lt_of_not_ge (fun hge => by simp [p, hge] at hpv)
    have hc := countOnes_map_not v
    exact ⟨(mem_allBitVecs_iff k _).mpr (by simpa using hlen), decide_eq_true (by omega)⟩
  dsimp only [p] at hsum hle; omega

/-- **Korec `log_4(3)` Barrier (`4^a ≤ 3^b`):** whenever `a/b ≤ log_4(3)`, at least half of all
`2^(2m)` residues mod `2^(2m)` violate Korec's contraction threshold `2^b * 3^(b*c) ≤ 2^(2m*a)`. -/
theorem korec_log4_3_barrier {a b : Nat} (hb : 0 < b) (h43 : 4 ^ a ≤ 3 ^ b) (m : Nat) :
    2 ^ (2 * m) ≤ 2 * badKorecCount a b (2 * m) := by
  rw [badKorecCount_eq_filter_allBitVecs]; have hhalf := half_bitVecs_heavy (2 * m)
  have hmono : ((allBitVecs (2 * m)).filter (fun v => decide (2 * m ≤ 2 * countOnes v))).length ≤
      ((allBitVecs (2 * m)).filter
        (fun v => decide (2 ^ (2 * m * a) < 2 ^ b * 3 ^ (b * countOnes v)))).length := by
    refine nodup_length_le_of_inj id (fun _ => rfl) _ _ ((allBitVecs_nodup (2 * m)).filter _)
      (fun v hv => ?_)
    rw [List.mem_filter] at hv ⊢; refine ⟨hv.1, decide_eq_true ?_⟩
    have hm : m ≤ countOnes v := by have := of_decide_eq_true hv.2; omega
    have h4a : 2 ^ (2 * m * a) ≤ 3 ^ (b * countOnes v) := calc
      2 ^ (2 * m * a) = (4 ^ a) ^ m := by
          rw [show 2 * m * a = 2 * a * m by ac_rfl, Nat.pow_mul, Nat.pow_mul 2 2 a,
            show 2 ^ 2 = 4 by decide]
      _ ≤ (3 ^ b) ^ m := Nat.pow_le_pow_left h43 m
      _ = 3 ^ (b * m) := (Nat.pow_mul 3 b m).symm
      _ ≤ 3 ^ (b * countOnes v) :=
          Nat.pow_le_pow_right (by decide : 0 < 3) (Nat.mul_le_mul_left b hm)
    have h2b : 2 ≤ 2 ^ b := Nat.le_self_pow (Nat.ne_of_gt hb) 2
    have hmul := Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right (by omega : 1 < 2 ^ b)
      (Nat.two_pow_pos _)) (Nat.mul_le_mul_left _ h4a)
    rwa [Nat.one_mul] at hmul
  omega

/-- Pure-`Nat` binomial coefficient `C(n, k)`. -/
def nChoose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => nChoose n k + nChoose n (k + 1)

private theorem nChoose_eq_zero {n k : Nat} (h : n < k) : nChoose n k = 0 := by
  induction n generalizing k with
  | zero => cases k with | zero => omega | succ k => rfl
  | succ n ih => cases k with
    | zero => omega | succ k => simp [nChoose, ih (by omega : n < k), ih (by omega : n < k + 1)]
private theorem countOnes_filter_length (k c : Nat) :
    ((allBitVecs k).filter (fun v => decide (countOnes v = c))).length = nChoose k c := by
  induction k generalizing c with
  | zero => cases c <;> simp [allBitVecs, countOnes, nChoose]
  | succ k ih =>
    simp only [allBitVecs, List.filter_append, List.length_append]
    have hf : ∀ m, (((allBitVecs k).map (false :: ·)).filter
        (fun v => decide (countOnes v = m))).length = nChoose k m := fun m => by
      rw [List.filter_map, List.length_map, show (fun x => decide (countOnes x = m)) ∘
        (false :: ·) = (fun x => decide (countOnes x = m)) by funext v; simp [countOnes]]
      exact ih m
    cases c with
    | zero =>
      have h2 : (((allBitVecs k).map (true :: ·)).filter
          (fun v => decide (countOnes v = 0))).length = 0 := by
        rw [List.filter_map, List.length_map, List.filter_eq_nil_iff.mpr]
        · rfl
        · intro v _; simp [countOnes]
      rw [hf 0, h2, Nat.add_zero]; cases k <;> rfl
    | succ c =>
      have h2 : (((allBitVecs k).map (true :: ·)).filter
          (fun v => decide (countOnes v = c + 1))).length = nChoose k c := by
        rw [List.filter_map, List.length_map, show (fun x => decide (countOnes x = c + 1)) ∘
          (true :: ·) = (fun x => decide (countOnes x = c)) by
            funext v; dsimp [Function.comp, countOnes]; exact decide_eq_decide.mpr (by omega)]
        exact ih c
      rw [nChoose, hf (c + 1), h2, Nat.add_comm]
private theorem nChoose_succ_mul (k i : Nat) (hi : i < k) :
    nChoose k (i + 1) * (i + 1) = nChoose k i * (k - i) := by
  induction k generalizing i with
  | zero => omega
  | succ k ih => cases i with
    | zero =>
      have h2 : ∀ m : Nat, nChoose m 1 = m := fun m => by
        induction m with | zero => rfl | succ m ihm =>
          rw [nChoose, show nChoose m 0 = 1 by cases m <;> rfl, ihm]; omega
      rw [h2 (k + 1), show nChoose (k + 1) 0 = 1 from rfl]; omega
    | succ i =>
      simp only [nChoose, Nat.add_mul]
      have h1 : nChoose k (i + 1) * (i + 1 + 1) = nChoose k i * (k - i) + nChoose k (i + 1) := by
        rw [Nat.mul_add _ (i + 1) 1, Nat.mul_one, ih i (by omega)]
      by_cases hi1 : i + 1 < k
      · have hsplit : nChoose k (i + 1) * (k - i) =
            nChoose k (i + 1) + nChoose k (i + 1) * (k - (i + 1)) := by
          rw [show k - i = 1 + (k - (i + 1)) by omega, Nat.mul_add, Nat.mul_one]
        rw [h1, ih (i + 1) hi1, show k + 1 - (i + 1) = k - i by omega, hsplit]; omega
      · have hk_eq : k = i + 1 := by omega
        subst hk_eq; rw [h1, nChoose_eq_zero (by omega : i + 1 < i + 2), Nat.zero_mul, Nat.add_zero,
          show i + 1 + 1 - (i + 1) = 1 by omega, show i + 1 - i = 1 by omega,
          Nat.mul_one, Nat.mul_one]
private theorem binTerm_adj {k c i : Nat} (hi : i < k) :
    (i < c → nChoose k i * c ^ i * (k - c) ^ (k - i) ≤
      nChoose k (i + 1) * c ^ (i + 1) * (k - c) ^ (k - (i + 1))) ∧
    (c ≤ i → nChoose k (i + 1) * c ^ (i + 1) * (k - c) ^ (k - (i + 1)) ≤
      nChoose k i * c ^ i * (k - c) ^ (k - i)) := by
  have hmul := nChoose_succ_mul k i hi; have hexp : k - i = (k - (i + 1)) + 1 := by omega
  constructor <;> intro hci
  · have h1 : (nChoose k i * c ^ i * (k - c) ^ (k - i)) * (i + 1) ≤
        (nChoose k (i + 1) * c ^ (i + 1) * (k - c) ^ (k - (i + 1))) * (i + 1) := calc
      _ = nChoose k i * c ^ i * (k - c) ^ (k - (i + 1)) * ((i + 1) * (k - c)) := by
          rw [hexp, Nat.pow_succ]; ac_rfl
      _ ≤ nChoose k i * c ^ i * (k - c) ^ (k - (i + 1)) * (c * (k - i)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
      _ = (nChoose k i * (k - i)) * (c ^ i * c) * (k - c) ^ (k - (i + 1)) := by ac_rfl
      _ = _ := by rw [← hmul, ← Nat.pow_succ c i]; ac_rfl
    exact Nat.le_of_mul_le_mul_right h1 (Nat.succ_pos i)
  · have h1 : (nChoose k (i + 1) * c ^ (i + 1) * (k - c) ^ (k - (i + 1))) * (i + 1) ≤
        (nChoose k i * c ^ i * (k - c) ^ (k - i)) * (i + 1) := calc
      _ = (nChoose k (i + 1) * (i + 1)) * (c ^ i * c) * (k - c) ^ (k - (i + 1)) := by
          rw [Nat.pow_succ c i]; ac_rfl
      _ = nChoose k i * c ^ i * (k - c) ^ (k - (i + 1)) * ((k - i) * c) := by rw [hmul]; ac_rfl
      _ ≤ nChoose k i * c ^ i * (k - c) ^ (k - (i + 1)) * ((k - c) * (i + 1)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
      _ = _ := by rw [hexp, Nat.pow_succ]; ac_rfl
    exact Nat.le_of_mul_le_mul_right h1 (Nat.succ_pos i)
private theorem binTerm_mode_le {k c : Nat} (hc : c ≤ k) : ∀ i : Nat, i ≤ k →
    nChoose k i * c ^ i * (k - c) ^ (k - i) ≤ nChoose k c * c ^ c * (k - c) ^ (k - c) := by
  intro i hik; by_cases hle : i ≤ c
  · have hup : ∀ d : Nat, i + d ≤ c → nChoose k i * c ^ i * (k - c) ^ (k - i) ≤
        nChoose k (i + d) * c ^ (i + d) * (k - c) ^ (k - (i + d)) := fun d hd => by
      induction d with | zero => simp | succ d ihd =>
        exact Nat.le_trans (ihd (by omega)) ((binTerm_adj (by omega : i + d < k)).1 (by omega))
    simpa [Nat.add_sub_of_le hle] using hup (c - i) (by omega)
  · have hge : c ≤ i := Nat.le_of_not_ge hle
    have hdn : ∀ d : Nat, c + d ≤ k →
        nChoose k (c + d) * c ^ (c + d) * (k - c) ^ (k - (c + d)) ≤
          nChoose k c * c ^ c * (k - c) ^ (k - c) := fun d hd => by
      induction d with | zero => simp | succ d ihd =>
        exact Nat.le_trans ((binTerm_adj (by omega : c + d < k)).2 (by omega)) (ihd (by omega))
    simpa [Nat.add_sub_of_le hge] using hdn (i - c) (by omega)
private theorem kd_listSum_const {α : Type} (c : Nat) (l : List α) :
    listSum (fun _ => c) l = l.length * c := by
  induction l with | nil => simp [listSum] | cons x xs ih => simp [listSum, ih, Nat.succ_mul]; omega
private theorem listSum_filter_split {α : Type} (f : α → Nat) (p : α → Bool) (l : List α) :
    listSum f l = listSum f (l.filter p) + listSum f (l.filter (fun x => !p x)) := by
  induction l with | nil => simp [listSum] | cons x xs ih =>
    cases hp : p x <;> simp [List.filter, hp, listSum, ih] <;> omega
private theorem listSum_filter_eq_const {k c m : Nat} :
    listSum (cherWeight (k - c) c k) ((allBitVecs k).filter (fun v => decide (countOnes v = m))) =
      nChoose k m * c ^ m * (k - c) ^ (k - m) := by
  have hmem : ∀ l : List (List Bool), (∀ v ∈ l, countOnes v = m) →
      listSum (cherWeight (k - c) c k) l = listSum (fun _ => c ^ m * (k - c) ^ (k - m)) l := by
    intro l hl; induction l with | nil => rfl | cons v vs ih =>
      have hvc := hl v List.mem_cons_self; simp only [listSum, cherWeight, hvc]
      rw [Nat.mul_comm ((k - c) ^ (k - m)) (c ^ m),
        ih (fun u hu => hl u (List.mem_cons_of_mem v hu))]
  rw [hmem _ (fun v hv => of_decide_eq_true (List.mem_filter.mp hv).2),
    kd_listSum_const, countOnes_filter_length, Nat.mul_assoc]

/-- **Pure-`Nat` Binomial Mode Lower Bound:** for all `c ≤ k`,
`k^k ≤ (k + 1) * C(k, c) * c^c * (k - c)^(k - c)`. -/
theorem nChoose_mode_lower_bound {k c : Nat} (hc : c ≤ k) :
    k ^ k ≤ (k + 1) * nChoose k c * c ^ c * (k - c) ^ (k - c) := by
  let M := nChoose k c * c ^ c * (k - c) ^ (k - c)
  have hlt_bound : ∀ m : Nat, m ≤ k + 1 →
      listSum (cherWeight (k - c) c k)
        ((allBitVecs k).filter (fun v => decide (countOnes v < m))) ≤ m * M := by
    intro m hm; induction m with
    | zero => rw [List.filter_eq_nil_iff.mpr (fun v _ => by simp)]; simp [listSum]
    | succ m ih =>
      have hsplit := listSum_filter_split (cherWeight (k - c) c k)
        (fun v => decide (countOnes v = m))
        ((allBitVecs k).filter (fun v => decide (countOnes v < m + 1)))
      have hf1 : ((allBitVecs k).filter (fun v => decide (countOnes v < m + 1))).filter
          (fun v => decide (countOnes v = m)) =
          (allBitVecs k).filter (fun v => decide (countOnes v = m)) := by
        rw [List.filter_filter]; congr 1; funext v; by_cases h1 : countOnes v = m <;> simp [h1]
      have hf2 : ((allBitVecs k).filter (fun v => decide (countOnes v < m + 1))).filter
          (fun v => !decide (countOnes v = m)) =
          (allBitVecs k).filter (fun v => decide (countOnes v < m)) := by
        rw [List.filter_filter]; congr 1; funext v
        by_cases h1 : countOnes v < m <;> by_cases h2 : countOnes v = m <;> simp [h1, h2] <;> omega
      rw [hf1, hf2, listSum_filter_eq_const] at hsplit
      have hterm := binTerm_mode_le hc m (by omega); have ih' := ih (by omega)
      rw [hsplit, Nat.succ_mul]; omega
  have hall : (allBitVecs k).filter (fun v => decide (countOnes v < k + 1)) = allBitVecs k := by
    rw [List.filter_eq_self]; intro v hv
    have := (mem_allBitVecs_iff k v).mp hv ▸ countOnes_le_length v; exact decide_eq_true (by omega)
  have hres := hlt_bound (k + 1) (Nat.le_refl _)
  rw [hall, cherWeight_allBitVecs_sum, show (k - c) + c = k by omega] at hres
  calc k ^ k ≤ (k + 1) * M := hres
    _ = (k + 1) * nChoose k c * c ^ c * (k - c) ^ (k - c) := by dsimp [M]; ac_rfl

/-- General lower bound on `badCount k` from any `(c, k)` with `c ≤ k` and `2^k ≤ 3^c`. -/
theorem terras_badCount_lower_general {k c : Nat} (hc : c ≤ k) (h23 : 2 ^ k ≤ 3 ^ c) :
    k ^ k ≤ (k + 1) * badCount k * c ^ c * (k - c) ^ (k - c) := by
  have hle : nChoose k c ≤ badCount k := by
    rw [← countOnes_filter_length k c, badCount_eq_filter_allBitVecs]
    refine nodup_length_le_of_inj id (fun _ => rfl) _ _ ((allBitVecs_nodup k).filter _) ?_
    intro v hv; rw [List.mem_filter] at hv ⊢
    exact ⟨hv.1, decide_eq_true ((of_decide_eq_true hv.2) ▸ h23)⟩
  exact Nat.le_trans (nChoose_mode_lower_bound hc) (Nat.mul_le_mul_right _
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left (k + 1) hle)))

private theorem pow_84_53_23 : 2 ^ 84 ≤ 3 ^ 53 := by decide
private theorem pow_84_17_tight : (53 ^ 53 * 31 ^ 31) ^ 17 * (2 ^ 113) ^ 12 ≤ (84 ^ 84) ^ 17 := by
  decide

/-- **Terras-Chernoff Tightness Ceiling (`H_2(log_3 2) ≈ 0.94992`):**
for all `m : Nat`, `badCount (84 * m)` satisfies
`2^(113 * 12 * m) ≤ (84 * m + 1)^17 * (badCount (84 * m))^17` (`113/119 = 0.94958`), proving
`SharperChernoff`'s `19/20 = 0.95` sits within `0.0005` of the single-horizon ceiling. -/
theorem terras_chernoff_tightness (m : Nat) :
    2 ^ (113 * 12 * m) ≤ (84 * m + 1) ^ 17 * (badCount (84 * m)) ^ 17 := by
  cases m with
  | zero => decide
  | succ m' =>
    let k := m' + 1
    have h23 : 2 ^ (84 * k) ≤ 3 ^ (53 * k) := by
      rw [Nat.pow_mul, Nat.pow_mul]; exact Nat.pow_le_pow_left pow_84_53_23 k
    have hgen := terras_badCount_lower_general (k := 84 * k) (c := 53 * k) (by omega) h23
    rw [show 84 * k - 53 * k = 31 * k by omega] at hgen
    have hpow17 := Nat.pow_le_pow_left hgen 17
    have hL : (84 * k) ^ (84 * k) = 84 ^ (84 * k) * k ^ (84 * k) := Nat.mul_pow 84 k (84 * k)
    have hR : (84 * k + 1) * badCount (84 * k) * (53 * k) ^ (53 * k) * (31 * k) ^ (31 * k) =
        ((84 * k + 1) * badCount (84 * k)) * (53 ^ (53 * k) * 31 ^ (31 * k)) * k ^ (84 * k) := by
      rw [Nat.mul_pow 53 k (53 * k), Nat.mul_pow 31 k (31 * k)]
      have hm : k ^ (53 * k) * k ^ (31 * k) = k ^ (84 * k) := by
        rw [← Nat.pow_add, show 53 * k + 31 * k = 84 * k by omega]
      calc _ = ((84 * k + 1) * badCount (84 * k)) * (53 ^ (53 * k) * 31 ^ (31 * k)) *
            (k ^ (53 * k) * k ^ (31 * k)) := by ac_rfl
        _ = _ := by rw [hm]
    rw [hL, hR, Nat.mul_pow _ (k ^ (84 * k)), Nat.mul_pow _ (k ^ (84 * k))] at hpow17
    have hcancel := Nat.le_of_mul_le_mul_right hpow17 (Nat.pow_pos (Nat.pow_pos (Nat.succ_pos m')))
    have h53_31 : (53 ^ (53 * k) * 31 ^ (31 * k)) ^ 17 = ((53 ^ 53 * 31 ^ 31) ^ 17) ^ k := by
      rw [Nat.pow_mul 53 53 k, Nat.pow_mul 31 31 k, ← Nat.mul_pow (53 ^ 53) (31 ^ 31) k,
        ← Nat.pow_mul, Nat.mul_comm k 17, Nat.pow_mul]
    have h84 : (84 ^ (84 * k)) ^ 17 = ((84 ^ 84) ^ 17) ^ k := by
      rw [Nat.pow_mul 84 84 k, ← Nat.pow_mul, Nat.mul_comm k 17, Nat.pow_mul]
    have ht := Nat.pow_le_pow_left pow_84_17_tight k
    rw [Nat.mul_pow, ← Nat.pow_mul (2 ^ 113) 12 k, ← Nat.pow_mul 2 113 (12 * k),
      ← Nat.mul_assoc 113 12 k, ← h53_31, ← h84] at ht
    rw [Nat.mul_pow _ (53 ^ (53 * k) * 31 ^ (31 * k)) 17] at hcancel
    have hcomb := Nat.le_trans ht hcancel
    rw [Nat.mul_comm (((84 * k + 1) * badCount (84 * k)) ^ 17) _,
      Nat.mul_pow (84 * k + 1) (badCount (84 * k)) 17] at hcomb
    exact Nat.le_of_mul_le_mul_left hcomb
      (Nat.pow_pos (Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))))

/-- **Barriers 1–3 Separation:** `HasPolynomialDrop` (`a ≤ b`) implies `HasFiniteStoppingTime`,
whereas `3n-1`, `5n+1` (where even `a = b = 1` violates `4^a > 5^b` since `4 < 5`), and
`ℤ_{<0}` all admit non-trivial cycles avoiding `1`. -/
theorem korec_barriers_1_to_3 :
    (∀ a b n : Nat, 0 < b → a ≤ b → 1 ≤ n → HasPolynomialDrop a b n → HasFiniteStoppingTime n) ∧
    (4 ^ 1 < 5 ^ 1) ∧
    (Barriers.genIter 3 (-1) 5 5 = 5 ∧ ∀ j < 5, Barriers.genIter 3 (-1) j 5 ≠ 1) ∧
    (Barriers.genIter 5 1 10 13 = 13 ∧ ∀ j < 10, Barriers.genIter 5 1 j 13 ≠ 1) ∧
    (Barriers.genIter 3 1 5 (-5) = -5 ∧ ∀ j < 5, Barriers.genIter 3 1 j (-5) ≠ 1) :=
  ⟨fun _ _ _ hb hab hn h => korec_drop_implies_finite_stopping hb hab hn h, by decide,
   Barriers.three_n_minus_one_cycle_5, Barriers.five_n_plus_one_cycle_13,
   Barriers.neg_int_cycle_neg5⟩

/-- **Barrier 4 Separation (`ℤ_2` / Cycles):** even `korec_drop_4_5` (`O(N^(25283/25284))`)
still permits excluding any finite cycle orbit `cycleOrbitList n L`. -/
theorem korec_allows_cycle (n L : Nat) :
    HasPowerSavingDensityOne
      (fun m => HasPolynomialDrop 4 5 m ∧ m ∉ cycleOrbitList n L) 50567 50568 :=
  hasPowerSaving_and_expSparse (by decide) (by decide)
    korec_drop_4_5 (isExpSparse_cycleOrbitList n L)

/-- **Barrier 4 Separation (`n^(9/10)`):** `korec_drop_9_10` still permits excluding any cycle
orbit `cycleOrbitList n L` at exponent `171 / 172`. -/
theorem korec_drop_9_10_allows_cycle (n L : Nat) :
    HasPowerSavingDensityOne
      (fun m => HasPolynomialDrop 9 10 m ∧ m ∉ cycleOrbitList n L) 171 172 :=
  hasPowerSaving_and_expSparse (by decide) (by decide)
    korec_drop_9_10 (isExpSparse_cycleOrbitList n L)

/-- **Barrier 5 Separation (`Conway` / Exponentially Divergent Orbits):** even `korec_drop_4_5`
still permits excluding any exponentially divergent Collatz orbit. -/
theorem korec_allows_expDivergent {n C : Nat} (hC : 1 ≤ C)
    (hexp : ∀ t : Nat, 2 ^ (t / C) ≤ collatzIter t n) :
    HasPowerSavingDensityOne
      (fun m => HasPolynomialDrop 4 5 m ∧ ¬ ∃ t : Nat, collatzIter t n = m) 50567 50568 :=
  hasPowerSaving_and_expSparse (by decide) (by decide)
    korec_drop_4_5 (isExpSparse_of_exp_seq (fun t => collatzIter t n) hC hexp)

end SolveCollatz
