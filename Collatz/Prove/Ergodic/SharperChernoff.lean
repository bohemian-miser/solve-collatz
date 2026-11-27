/-
Copyright (c) 2026 The solve-collatz contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Collatz.Prove.Ergodic.ExceptionalDensity

/-!
# Sharper `s = 1/2` Pure-`Nat` Chernoff & Dyadic Shell Bounds (`PROVE-A1`)

Pure Lean 4 core formalization (zero Mathlib, zero reals, zero `sorry`) sharpening the
unconditional Track A power-saving exceptional-set bound for `HasFiniteStoppingTime` from
`N^(237/238)` (`0.9958`) down to `N^(19/20)` (`0.9500`, strictly beating `N^(20/21)` and
`N^(39/41)`):

1. **Sharp Residue Bound (`n ≥ 2^k` Threshold):** proves `terrasIter k r < 3 ^ countOnes v`
   for every `r < 2^k`, cutting the Terras dropping threshold from `n ≥ 2^(3k)` down to
   `n ≥ 2^k` whenever `2 * 3^c ≤ 2^k`.
2. **Exact `s = 1/2` Pure-`Nat` Chernoff Bound:** using the Pell-optimal rational square-root
   approximation `3 * 780^2 = 1825200 < 1825201 = 1351^2` (as well as `3 * 56^2 < 97^2`),
   proves `badCount (2*m) * 4867200^m ≤ 4541161^m * 2^(2*m)` (`23409/25088` for `(56, 97)`)
   and the strict-threshold odd-length bound `badStrictCount (2*m+1)` with `2 * 4541161^10 <
   4867200^10` (`< 2^(-1/20)` decay per bit!).
3. **Dyadic Shell Decomposition:** partitions `[0, 2^(2M+1))` into `[0, 2)` and 2-bit shells
   `[2^(2m+1), 2^(2m+3))`, yielding unconditional `HasPowerSavingDensityOne HasFiniteStoppingTime
   19 20` (plus `39 41` and explicit `2 ^ 2002 ≤ N → count^21 < N^20`), plus a 6x tighter
   constructive natural-density modulus `sharperDensityThreshold D = 2^(20 * bitLen D + 100)`.
4. **Barrier 2 (`5n + 1`) Contrast:** proves in pure `Nat` that for `5n + 1`, the analogous
   `s = 1/2` moment lower bound (`cherWeight 100 223 (2*m)`) grows exponentially as
   `(104329 / 80000)^m`, strictly separating `3n + 1` from `5n + 1`.
-/

@[expose] public section

namespace SolveCollatz

private theorem sc_dec_true {P : Prop} (h : P) : @decide P (Classical.propDecidable P) = true :=
  @decide_eq_true P (Classical.propDecidable P) h
private theorem sc_of_dec_true {P : Prop} (h : @decide P (Classical.propDecidable P) = true) : P :=
  @of_decide_eq_true P (Classical.propDecidable P) h

/-! ### 1. Sharp Remainder Bound & `2^k ≤ n` Dropping Criterion -/

private theorem terrasStep_lt_three_mul {x c : Nat} (hx : x < 2 * 3 ^ c) :
    terrasStep x < 3 ^ (c + if x % 2 == 1 then 1 else 0) := by
  by_cases hodd : x % 2 = 1
  · have hb : (x % 2 == 1) = true := beq_iff_eq.mpr hodd
    rw [terrasStep_odd hodd, hb, ite_eq_left rfl, Nat.pow_succ]
    omega
  · have hev : x % 2 = 0 := by omega
    have hb : (x % 2 == 1) = false := by
      cases h : (x % 2 == 1)
      · rfl
      · exfalso; have := beq_iff_eq.mp h; omega
    simp only [terrasStep_even hev, hb, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    omega

/-- **Sharp Residue Iterate Bound:** every residue `r < 2^k` satisfies
`terrasIter k r < 3 ^ countOnes (terrasParityVec k r)`. -/
theorem terrasIter_lt_three_pow_countOnes (k r : Nat) (hr : r < 2 ^ k) :
    terrasIter k r < 3 ^ countOnes (terrasParityVec k r) := by
  induction k generalizing r with
  | zero =>
    have hr0 : r = 0 := by simp at hr; exact hr
    subst hr0; decide
  | succ k ih =>
    have hkpos : 0 < 2 ^ k := Nat.two_pow_pos k
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hq_lt : r / 2 ^ k < 2 := by
      rw [hpow, Nat.mul_comm 2 (2 ^ k)] at hr; exact Nat.div_lt_of_lt_mul hr
    have hq : r / 2 ^ k ≤ 1 := by omega
    have hih := ih (r % 2 ^ k) (Nat.mod_lt r hkpos)
    rw [terrasParityVec_mod_eq] at hih
    have heq := terrasIter_mod_eq k r
    have hlt2 : terrasIter k r < 2 * 3 ^ countOnes (terrasParityVec k r) := by
      have hmul : 3 ^ countOnes (terrasParityVec k r) * (r / 2 ^ k) ≤
          3 ^ countOnes (terrasParityVec k r) := by
        calc 3 ^ countOnes (terrasParityVec k r) * (r / 2 ^ k)
            ≤ 3 ^ countOnes (terrasParityVec k r) * 1 := Nat.mul_le_mul_left _ hq
          _ = 3 ^ countOnes (terrasParityVec k r) := Nat.mul_one _
      omega
    have hstep := terrasStep_lt_three_mul hlt2
    rw [← terrasIter_succ_right] at hstep
    have hc : countOnes (terrasParityVec (k + 1) r) =
        countOnes (terrasParityVec k r) + (if (terrasIter k r % 2 == 1) then 1 else 0) := by
      rw [terrasParityVec_add k 1 r, countOnes_append]; simp [terrasParityVec, countOnes]
    rwa [← hc] at hstep

/-- **Sharp `2^k ≤ n` Dropping Criterion:** if `2^k ≤ n` and `2 * 3^c ≤ 2^k` where
`c = countOnes (terrasParityVec k (n % 2^k))`, then `terrasIter k n < n`,
`HasStoppingTimeLe n (2 * k)`, and `HasFiniteStoppingTime n`. -/
theorem terras_lt_of_two_mul_three_pow_le {k n : Nat} (hn : 2 ^ k ≤ n)
    (hlow : 2 * 3 ^ countOnes (terrasParityVec k (n % 2 ^ k)) ≤ 2 ^ k) :
    terrasIter k n < n ∧ HasStoppingTimeLe n (2 * k) ∧ HasFiniteStoppingTime n := by
  let r := n % 2 ^ k; let q := n / 2 ^ k; let c := countOnes (terrasParityVec k r)
  have hkpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hq : 1 ≤ q := (Nat.le_div_iff_mul_le hkpos).mpr (by rw [Nat.one_mul]; exact hn)
  have hiter_lt : terrasIter k r < 3 ^ c :=
    terrasIter_lt_three_pow_countOnes k r (Nat.mod_lt n hkpos)
  have hdiff : 3 ^ c ≤ 2 ^ k - 3 ^ c := by change 2 * 3 ^ c ≤ 2 ^ k at hlow; omega
  have hmul : 3 ^ c ≤ (2 ^ k - 3 ^ c) * q := by
    calc 3 ^ c ≤ 2 ^ k - 3 ^ c := hdiff
      _ = (2 ^ k - 3 ^ c) * 1 := (Nat.mul_one _).symm
      _ ≤ (2 ^ k - 3 ^ c) * q := Nat.mul_le_mul_left _ hq
  have h3lt : 3 ^ c < 2 ^ k := by
    have h3pos : 0 < 3 ^ c := Nat.pow_pos (by decide)
    change 2 * 3 ^ c ≤ 2 ^ k at hlow; omega
  have hdrop := terras_lt_of_low_ones h3lt (Nat.lt_of_lt_of_le hiter_lt hmul)
  rw [Nat.mod_add_div n (2 ^ k)] at hdrop
  exact ⟨hdrop.1, hasStoppingTimeLe_of_terras_lt hdrop.1, hdrop.2⟩

/-! ### 2. General Pure-`Nat` `s = 1/2` Chernoff Bounds -/

/-- General pure-`Nat` binomial weight `a ^ (k - countOnes v) * b ^ countOnes v`. -/
def cherWeight (a b k : Nat) (v : List Bool) : Nat :=
  a ^ (k - countOnes v) * b ^ countOnes v

private theorem cherWeight_cons_false {a b k : Nat} {v : List Bool} (hv : countOnes v ≤ k) :
    cherWeight a b (k + 1) (false :: v) = a * cherWeight a b k v := by
  simp only [cherWeight, countOnes, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
  have hsub : k + 1 - countOnes v = (k - countOnes v) + 1 := by omega
  rw [hsub, Nat.pow_succ, Nat.mul_comm (a ^ (k - countOnes v)) a, Nat.mul_assoc]

private theorem cherWeight_cons_true (a b k : Nat) (v : List Bool) :
    cherWeight a b (k + 1) (true :: v) = b * cherWeight a b k v := by
  simp only [cherWeight, countOnes, ↓reduceIte]
  have hsub : k + 1 - (1 + countOnes v) = k - countOnes v := by omega
  rw [hsub, Nat.add_comm 1 (countOnes v), Nat.pow_succ]; ac_rfl

private theorem sc_listSum_append {α : Type} (f : α → Nat) (l₁ l₂ : List α) :
    listSum f (l₁ ++ l₂) = listSum f l₁ + listSum f l₂ := by
  induction l₁ with | nil => simp [listSum] | cons x xs ih => simp [listSum, ih, Nat.add_assoc]

private theorem sc_listSum_map {α β : Type} (f : β → Nat) (g : α → β) (l : List α) :
    listSum f (l.map g) = listSum (f ∘ g) l := by
  induction l with | nil => rfl | cons x xs ih => simp [listSum, ih]

private theorem sc_listSum_mul_left {α : Type} (c : Nat) (f : α → Nat) (l : List α) :
    listSum (fun x => c * f x) l = c * listSum f l := by
  induction l with | nil => simp [listSum] | cons x xs ih => simp [listSum, ih, Nat.mul_add]

private theorem sc_listSum_congr {α : Type} {f g : α → Nat} {l : List α}
    (h : ∀ x : α, x ∈ l → f x = g x) : listSum f l = listSum g l := by
  induction l with | nil => rfl | cons x xs ih =>
    simp only [listSum]
    rw [h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

private theorem sc_listSum_markov {α : Type} (p : α → Bool) (f : α → Nat) (T : Nat)
    (l : List α) (hle : ∀ x : α, x ∈ l → p x = true → T ≤ f x) :
    (l.filter p).length * T ≤ listSum f l := by
  induction l with
  | nil => simp [listSum]
  | cons x xs ih =>
    have hih := ih (fun y hy => hle y (List.mem_cons_of_mem x hy))
    cases hp : p x
    · simp only [List.filter, hp, listSum]; omega
    · have hx : T ≤ f x := hle x List.mem_cons_self hp
      simp only [List.filter, hp, listSum, List.length_cons, Nat.succ_mul]; omega

/-- **Exact Pure-`Nat` General Binomial Sum:**
`∑_{v ∈ allBitVecs k} a ^ (k - countOnes v) * b ^ countOnes v = (a + b) ^ k`. -/
theorem cherWeight_allBitVecs_sum (a b k : Nat) :
    listSum (cherWeight a b k) (allBitVecs k) = (a + b) ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [allBitVecs, sc_listSum_append, sc_listSum_map, sc_listSum_map]
    have hfalse : listSum (cherWeight a b (k + 1) ∘ (false :: ·)) (allBitVecs k) =
        a * listSum (cherWeight a b k) (allBitVecs k) := by
      rw [← sc_listSum_mul_left]
      exact sc_listSum_congr (fun v hv =>
        cherWeight_cons_false ((mem_allBitVecs_iff k v).mp hv ▸ countOnes_le_length v))
    have htrue : listSum (cherWeight a b (k + 1) ∘ (true :: ·)) (allBitVecs k) =
        b * listSum (cherWeight a b k) (allBitVecs k) := by
      rw [← sc_listSum_mul_left]
      exact sc_listSum_congr (fun v _ => cherWeight_cons_true a b k v)
    rw [hfalse, htrue, ih, Nat.pow_succ, Nat.mul_comm ((a + b) ^ k) (a + b), Nat.add_mul]

/-- Pure-`Nat` square-root monotonicity: `x * x ≤ y * y → x ≤ y`. -/
theorem nat_le_of_sq_le {x y : Nat} (h : x * x ≤ y * y) : x ≤ y := by
  by_cases hle : x ≤ y
  · exact hle
  · exfalso; have hlt : y < x := Nat.lt_of_not_ge hle
    have hsq := Nat.mul_lt_mul_of_lt_of_lt hlt hlt
    omega

private theorem cherWeight_sq_ge {a b k c : Nat} (hab : 3 * (a * a) ≤ b * b) (hc : c ≤ k) :
    3 ^ c * a ^ (2 * k) ≤ (a ^ (k - c) * b ^ c) * (a ^ (k - c) * b ^ c) := by
  have hsq : (a ^ (k - c) * b ^ c) * (a ^ (k - c) * b ^ c) =
      a ^ (2 * (k - c)) * (b * b) ^ c := by
    rw [← Nat.pow_two, Nat.mul_pow, ← Nat.pow_mul a (k - c) 2, ← Nat.pow_mul b c 2,
      Nat.mul_comm (k - c) 2, Nat.mul_comm c 2, Nat.pow_mul b 2 c, Nat.pow_two b]
  have hpow3 : (3 * (a * a)) ^ c ≤ (b * b) ^ c := Nat.pow_le_pow_left hab c
  have hleft : (3 * (a * a)) ^ c = 3 ^ c * a ^ (2 * c) := by
    rw [Nat.mul_pow, ← Nat.pow_two a, ← Nat.pow_mul a 2 c]
  have hmul : a ^ (2 * (k - c)) * (3 ^ c * a ^ (2 * c)) ≤
      a ^ (2 * (k - c)) * (b * b) ^ c := Nat.mul_le_mul_left _ (hleft ▸ hpow3)
  have hexp : 2 * (k - c) + 2 * c = 2 * k := by omega
  calc 3 ^ c * a ^ (2 * k) = 3 ^ c * (a ^ (2 * (k - c)) * a ^ (2 * c)) := by
        rw [← Nat.pow_add, hexp]
    _ = a ^ (2 * (k - c)) * (3 ^ c * a ^ (2 * c)) := by ac_rfl
    _ ≤ (a ^ (k - c) * b ^ c) * (a ^ (k - c) * b ^ c) := hsq ▸ hmul

/-- **Pure-`Nat` `s = 1/2` Chernoff Bound (Even Length `2 * m`):**
for any `a, b` with `3 * (a * a) ≤ b * b`,
`badCount (2 * m) * (8 * (a * a)) ^ m ≤ ((a + b) * (a + b)) ^ m * 2 ^ (2 * m)`. -/
theorem badCount_even_chernoff {a b : Nat} (hab : 3 * (a * a) ≤ b * b) (m : Nat) :
    badCount (2 * m) * (8 * (a * a)) ^ m ≤ ((a + b) * (a + b)) ^ m * 2 ^ (2 * m) := by
  rw [badCount_eq_filter_allBitVecs]
  have hmarkov := sc_listSum_markov
    (fun v => decide (2 ^ (2 * m) ≤ 3 ^ countOnes v))
    (cherWeight a b (2 * m)) (2 ^ m * a ^ (2 * m)) (allBitVecs (2 * m))
    (fun v hv hp => by
      have hc : countOnes v ≤ 2 * m := (mem_allBitVecs_iff (2 * m) v).mp hv ▸ countOnes_le_length v
      have h3c : 2 ^ (2 * m) ≤ 3 ^ countOnes v := of_decide_eq_true hp
      have hsq1 : (2 ^ m * a ^ (2 * m)) * (2 ^ m * a ^ (2 * m)) = 2 ^ (2 * m) * a ^ (4 * m) := by
        rw [← Nat.pow_two, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul,
          Nat.mul_comm m 2, show 2 * m * 2 = 4 * m by omega]
      have hsq2 := cherWeight_sq_ge hab hc
      rw [show 2 * (2 * m) = 4 * m by omega] at hsq2
      exact nat_le_of_sq_le (Nat.le_trans (hsq1 ▸ Nat.mul_le_mul_right _ h3c) hsq2))
  rw [cherWeight_allBitVecs_sum] at hmarkov
  have h1 : (2 ^ m * a ^ (2 * m)) * 2 ^ (2 * m) = (8 * (a * a)) ^ m := by
    rw [Nat.mul_right_comm, ← Nat.pow_add, show m + 2 * m = 3 * m by omega,
      Nat.pow_mul 2 3 m, Nat.pow_mul a 2 m, ← Nat.mul_pow, show 2 ^ 3 = 8 by decide, Nat.pow_two]
  have h2 : (a + b) ^ (2 * m) = ((a + b) * (a + b)) ^ m := by
    rw [Nat.pow_mul, Nat.pow_two (a + b)]
  have h3 := Nat.mul_le_mul_right (2 ^ (2 * m)) hmarkov
  rwa [Nat.mul_assoc, h1, h2] at h3

/-- **Concrete `(56, 97)` `s = 1/2` Chernoff Decay:**
`badCount (2 * m) * 25088 ^ m ≤ 23409 ^ m * 2 ^ (2 * m)`. -/
theorem badCount_even_chernoff_56_97 (m : Nat) :
    badCount (2 * m) * 25088 ^ m ≤ 23409 ^ m * 2 ^ (2 * m) := by
  simpa using badCount_even_chernoff (a := 56) (b := 97) (by decide) m

/-- **Pell-Optimal `(780, 1351)` `s = 1/2` Chernoff Decay:**
`badCount (2 * m) * 4867200 ^ m ≤ 4541161 ^ m * 2 ^ (2 * m)`. -/
theorem badCount_even_chernoff_780_1351 (m : Nat) :
    badCount (2 * m) * 4867200 ^ m ≤ 4541161 ^ m * 2 ^ (2 * m) := by
  simpa using badCount_even_chernoff (a := 780) (b := 1351) (by decide) m

/-- Strict bad-residue indicator `2^k < 2 * 3^c` required for the sharp `n ≥ 2^k` threshold. -/
def badStrictResidue (k r : Nat) : Bool :=
  decide (2 ^ k < 2 * 3 ^ countOnes (terrasParityVec k r))

/-- Number of residues `r < 2^k` failing `2 * 3 ^ countOnes (terrasParityVec k r) ≤ 2^k`. -/
def badStrictCount (k : Nat) : Nat :=
  countLt (badStrictResidue k) (2 ^ k)

/-- Periodicity of `badStrictResidue k (i % 2^k)`. -/
theorem badStrictResidue_mod_periodic (k i : Nat) :
    badStrictResidue k ((i + 2 ^ k) % 2 ^ k) = badStrictResidue k (i % 2 ^ k) := by
  rw [Nat.add_mod_right]

private theorem countLt_badStrictResidue_mod_eq (k : Nat) :
    countLt (fun n => badStrictResidue k (n % 2 ^ k)) (2 ^ k) = badStrictCount k :=
  Nat.le_antisymm
    (countLt_mono_pred (2 ^ k) (fun _ hi h => by rw [Nat.mod_eq_of_lt hi] at h; exact h))
    (countLt_mono_pred (2 ^ k) (fun _ hi h => by rw [Nat.mod_eq_of_lt hi]; exact h))

/-- Combinatorial expression for `badStrictCount k` via `allBitVecs k`. -/
theorem badStrictCount_eq_filter_allBitVecs (k : Nat) :
    badStrictCount k =
      ((allBitVecs k).filter (fun v => decide (2 ^ k < 2 * 3 ^ countOnes v))).length := by
  let p : List Bool → Bool := fun v => decide (2 ^ k < 2 * 3 ^ countOnes v)
  have hperm := (map_terrasParityVec_perm_allBitVecs k).filter p
  have hlen : (((List.range (2 ^ k)).map (terrasParityVec k)).filter p).length =
      ((allBitVecs k).filter p).length := hperm.length_eq
  rw [List.filter_map, List.length_map] at hlen
  have hcomp : p ∘ terrasParityVec k = badStrictResidue k := rfl
  rw [badStrictCount, countLt_eq_filter_range, ← hcomp, hlen]

/-- **Pure-`Nat` `s = 1/2` Chernoff Bound (Odd Length `2 * m + 1`, Strict Threshold):**
for any `a, b` with `3 * (a * a) ≤ b * b`,
`badStrictCount (2 * m + 1) * (2 * a) * (8 * (a * a)) ^ m ≤
  (a + b) * ((a + b) * (a + b)) ^ m * 2 ^ (2 * m + 1)`. -/
theorem badStrictCount_odd_chernoff {a b : Nat} (hab : 3 * (a * a) ≤ b * b) (m : Nat) :
    badStrictCount (2 * m + 1) * (2 * a) * (8 * (a * a)) ^ m ≤
      (a + b) * ((a + b) * (a + b)) ^ m * 2 ^ (2 * m + 1) := by
  rw [badStrictCount_eq_filter_allBitVecs]
  have hmarkov := sc_listSum_markov
    (fun v => decide (2 ^ (2 * m + 1) < 2 * 3 ^ countOnes v))
    (cherWeight a b (2 * m + 1)) (2 ^ m * a ^ (2 * m + 1)) (allBitVecs (2 * m + 1))
    (fun v hv hp => by
      have hc : countOnes v ≤ 2 * m + 1 :=
        (mem_allBitVecs_iff (2 * m + 1) v).mp hv ▸ countOnes_le_length v
      have hlt : 2 ^ (2 * m + 1) < 2 * 3 ^ countOnes v := of_decide_eq_true hp
      have h3c : 2 ^ (2 * m) ≤ 3 ^ countOnes v := by rw [Nat.pow_succ] at hlt; omega
      have hsq1 : (2 ^ m * a ^ (2 * m + 1)) * (2 ^ m * a ^ (2 * m + 1)) =
          2 ^ (2 * m) * a ^ (2 * (2 * m + 1)) := by
        rw [← Nat.pow_two, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm m 2,
          Nat.mul_comm (2 * m + 1) 2]
      exact nat_le_of_sq_le (Nat.le_trans (hsq1 ▸ Nat.mul_le_mul_right _ h3c)
        (cherWeight_sq_ge hab hc)))
  rw [cherWeight_allBitVecs_sum] at hmarkov
  have h1 : (2 ^ m * a ^ (2 * m + 1)) * 2 ^ (2 * m + 1) = (2 * a) * (8 * (a * a)) ^ m := by
    have h2pow : 2 ^ m * 2 ^ (2 * m + 1) = 2 * 8 ^ m := by
      rw [← Nat.pow_add, show m + (2 * m + 1) = 3 * m + 1 by omega,
        Nat.pow_succ, Nat.pow_mul, show 2 ^ 3 = 8 by decide, Nat.mul_comm]
    have hapow : a ^ (2 * m + 1) = a * (a * a) ^ m := by
      rw [Nat.pow_succ, Nat.pow_mul, Nat.pow_two a, Nat.mul_comm]
    calc (2 ^ m * a ^ (2 * m + 1)) * 2 ^ (2 * m + 1)
        = (2 ^ m * 2 ^ (2 * m + 1)) * a ^ (2 * m + 1) := by ac_rfl
      _ = (2 * 8 ^ m) * (a * (a * a) ^ m) := by rw [h2pow, hapow]
      _ = (2 * a) * (8 * (a * a)) ^ m := by rw [Nat.mul_pow 8 (a * a) m]; ac_rfl
  have h2 : (a + b) ^ (2 * m + 1) = (a + b) * ((a + b) * (a + b)) ^ m := by
    rw [Nat.pow_succ, Nat.pow_mul, Nat.pow_two (a + b), Nat.mul_comm]
  have h3 := Nat.mul_le_mul_right (2 ^ (2 * m + 1)) hmarkov
  calc ((allBitVecs (2 * m + 1)).filter _).length * (2 * a) * (8 * (a * a)) ^ m
      = ((allBitVecs (2 * m + 1)).filter _).length * ((2 * a) * (8 * (a * a)) ^ m) :=
          Nat.mul_assoc _ _ _
    _ = ((allBitVecs (2 * m + 1)).filter _).length * (2 ^ m * a ^ (2 * m + 1)) *
          2 ^ (2 * m + 1) := by rw [← h1]; exact (Nat.mul_assoc _ _ _).symm
    _ ≤ (a + b) * ((a + b) * (a + b)) ^ m * 2 ^ (2 * m + 1) := h2 ▸ h3

/-! ### 3. Dyadic Shell Decomposition & Power-Saving Density `19/20` -/

/-- Cumulative `badStrictCount (2 * m + 1)` over the first `M` dyadic 2-bit shells. -/
def shellBadSum : Nat → Nat
  | 0 => 0
  | M + 1 => shellBadSum M + badStrictCount (2 * M + 1)

private def geomShellSum (X Y : Nat) : Nat → Nat
  | 0 => 0
  | M + 1 => Y * geomShellSum X Y M + X ^ M * Y

private theorem geomShellSum_le {X Y : Nat} (hXY : 2 * Y ≤ X) (M : Nat) :
    geomShellSum X Y M ≤ X ^ M := by
  induction M with
  | zero => simp [geomShellSum]
  | succ M ih =>
    simp only [geomShellSum, Nat.pow_succ]
    calc Y * geomShellSum X Y M + X ^ M * Y
        ≤ Y * X ^ M + X ^ M * Y := Nat.add_le_add_right (Nat.mul_le_mul_left Y ih) _
      _ = (2 * Y) * X ^ M := by rw [Nat.mul_comm (X ^ M) Y, ← Nat.two_mul, Nat.mul_assoc]
      _ ≤ X * X ^ M := Nat.mul_le_mul_right _ hXY
      _ = X ^ M * X := Nat.mul_comm _ _

private theorem shell_step_count_le (M : Nat) :
    countLt (fun i => @decide (¬ HasStoppingTimeLe (2 ^ (2 * M + 1) + i) (4 * (M + 1)))
      (Classical.propDecidable _)) (3 * 2 ^ (2 * M + 1)) ≤ 3 * badStrictCount (2 * M + 1) := by
  let k := 2 * M + 1
  have hmono : countLt (fun i => @decide (¬ HasStoppingTimeLe (2 ^ k + i) (4 * (M + 1)))
      (Classical.propDecidable _)) (3 * 2 ^ k) ≤
      countLt (fun i => badStrictResidue k ((2 ^ k + i) % 2 ^ k)) (3 * 2 ^ k) := by
    refine countLt_mono_pred _ (fun i _ hi => ?_)
    have hnot : ¬ HasStoppingTimeLe (2 ^ k + i) (4 * (M + 1)) := sc_of_dec_true hi
    by_cases hbad : badStrictResidue k ((2 ^ k + i) % 2 ^ k) = true
    · exact hbad
    · exfalso
      have hlow : 2 * 3 ^ countOnes (terrasParityVec k ((2 ^ k + i) % 2 ^ k)) ≤ 2 ^ k :=
        Nat.le_of_not_lt (fun hlt => absurd (decide_eq_true hlt) hbad)
      have hdrop := (terras_lt_of_two_mul_three_pow_le (by omega : 2 ^ k ≤ 2 ^ k + i) hlow).2.1
      exact hnot (hasStoppingTimeLe_mono (by dsimp [k]; omega : 2 * k ≤ 4 * (M + 1)) hdrop)
  have hper := countLt_mul_periodic (fun n => badStrictResidue k (n % 2 ^ k)) (2 ^ k) 3
    (badStrictResidue_mod_periodic k)
  rw [Nat.mul_comm (2 ^ k) 3] at hper
  have hsh := countLt_periodic_shift (fun n => badStrictResidue k (n % 2 ^ k)) (3 * 2 ^ k) (2 ^ k)
    (fun i => by rw [show i + 3 * 2 ^ k = i + 2 ^ k * 3 by omega, Nat.add_mul_mod_self_left])
  rw [hsh, hper, countLt_badStrictResidue_mod_eq k, Nat.mul_comm _ 3] at hmono
  exact hmono

/-- **Dyadic Shell Counting Bound (Bounded Stopping Time):**
on `[0, 2 ^ (2 * M + 1))`, failures of `HasStoppingTimeLe n (4 * M)` are bounded by
`2 + 3 * shellBadSum M`. -/
theorem dyadic_shell_stopping_bound (M : Nat) :
    countLt (fun n => @decide (¬ HasStoppingTimeLe n (4 * M)) (Classical.propDecidable _))
      (2 ^ (2 * M + 1)) ≤ 2 + 3 * shellBadSum M := by
  induction M with
  | zero => exact countLt_le _ 2
  | succ M ih =>
    have hsplit : 2 ^ (2 * (M + 1) + 1) = 2 ^ (2 * M + 1) + 3 * 2 ^ (2 * M + 1) := by
      rw [show 2 * (M + 1) + 1 = (2 * M + 1) + 2 by omega, Nat.pow_add]; omega
    rw [hsplit, countLt_add]
    have hhead : countLt (fun n => @decide (¬ HasStoppingTimeLe n (4 * (M + 1)))
        (Classical.propDecidable _)) (2 ^ (2 * M + 1)) ≤
        countLt (fun n => @decide (¬ HasStoppingTimeLe n (4 * M)) (Classical.propDecidable _))
          (2 ^ (2 * M + 1)) :=
      countLt_mono_pred _ (fun n _ hn => sc_dec_true (fun h =>
        sc_of_dec_true hn (hasStoppingTimeLe_mono (by omega : 4 * M ≤ 4 * (M + 1)) h)))
    have htail := shell_step_count_le M
    simp only [shellBadSum]
    omega

private theorem shellBadSum_chernoff_bound {a b : Nat} (hab : 3 * (a * a) ≤ b * b) (M : Nat) :
    let A := (a + b) * (a + b)
    let B := 8 * (a * a)
    shellBadSum M * (2 * a) * B ^ M ≤ 2 * (a + b) * geomShellSum (4 * A) B M := by
  intro A B
  induction M with
  | zero => simp [shellBadSum, geomShellSum]
  | succ M ih =>
    simp only [shellBadSum, geomShellSum, Nat.add_mul]
    have h1 : shellBadSum M * (2 * a) * B ^ (M + 1) ≤
        2 * (a + b) * (B * geomShellSum (4 * A) B M) := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]
      calc shellBadSum M * (2 * a) * B ^ M * B
          ≤ (2 * (a + b) * geomShellSum (4 * A) B M) * B := Nat.mul_le_mul_right B ih
        _ = 2 * (a + b) * (B * geomShellSum (4 * A) B M) := by ac_rfl
    have h2 : badStrictCount (2 * M + 1) * (2 * a) * B ^ (M + 1) ≤
        2 * (a + b) * ((4 * A) ^ M * B) := by
      have hc := badStrictCount_odd_chernoff hab M
      have heq : (a + b) * A ^ M * 2 ^ (2 * M + 1) = 2 * (a + b) * (4 * A) ^ M := by
        rw [Nat.pow_succ, Nat.pow_mul 2 2 M, show 2 ^ 2 = 4 by decide, Nat.mul_pow 4 A M]; ac_rfl
      rw [Nat.pow_succ, ← Nat.mul_assoc]
      calc badStrictCount (2 * M + 1) * (2 * a) * B ^ M * B
          ≤ (2 * (a + b) * (4 * A) ^ M) * B := Nat.mul_le_mul_right B (heq ▸ hc)
        _ = 2 * (a + b) * ((4 * A) ^ M * B) := by ac_rfl
    rw [Nat.mul_add]; exact Nat.add_le_add h1 h2

private theorem shell_geom_ratio {a b : Nat} (hab : 3 * (a * a) ≤ b * b) :
    2 * (8 * (a * a)) ≤ 4 * ((a + b) * (a + b)) := by
  have h1 : a ≤ b := nat_le_of_sq_le (by omega)
  have h2 : 4 * (a * a) ≤ (a + b) * (a + b) := by
    have : (2 * a) * (2 * a) ≤ (a + b) * (a + b) := Nat.mul_le_mul (by omega) (by omega)
    calc 4 * (a * a) = (2 * a) * (2 * a) := by ac_rfl
      _ ≤ (a + b) * (a + b) := this
  omega

/-- **Master Dyadic Shell Bound:** for any `a, b` with `3 * (a * a) ≤ b * b` and every `M`,
failures of `HasStoppingTimeLe n (4 * M)` on `[0, 2^(2M+1))` satisfy
`count * (2 * a) * (8 * a^2)^M ≤ (10 * a + 6 * b) * (4 * (a + b)^2)^M`. -/
theorem sharper_shell_master_bound {a b : Nat} (hab : 3 * (a * a) ≤ b * b) (M : Nat) :
    countLt (fun n => @decide (¬ HasStoppingTimeLe n (4 * M)) (Classical.propDecidable _))
      (2 ^ (2 * M + 1)) * (2 * a) * (8 * (a * a)) ^ M ≤
      (10 * a + 6 * b) * (4 * ((a + b) * (a + b))) ^ M := by
  let A := (a + b) * (a + b); let B := 8 * (a * a)
  have hgeo := shell_geom_ratio hab
  have hsum := Nat.le_trans (shellBadSum_chernoff_bound hab M)
    (Nat.mul_le_mul_left (2 * (a + b)) (geomShellSum_le hgeo M))
  have hB_le : B ^ M ≤ (4 * A) ^ M := Nat.pow_le_pow_left (by omega) M
  have hsh := Nat.mul_le_mul_right ((2 * a) * B ^ M) (dyadic_shell_stopping_bound M)
  rw [Nat.add_mul] at hsh
  have h2 : 2 * (2 * a * B ^ M) ≤ 4 * a * (4 * A) ^ M := by
    calc 2 * (2 * a * B ^ M) = 4 * a * B ^ M := by rw [← Nat.mul_assoc, ← Nat.mul_assoc 2 2 a]
      _ ≤ 4 * a * (4 * A) ^ M := Nat.mul_le_mul_left _ hB_le
  have h3 : 3 * shellBadSum M * (2 * a * B ^ M) ≤ 6 * (a + b) * (4 * A) ^ M := by
    calc 3 * shellBadSum M * (2 * a * B ^ M)
        = 3 * (shellBadSum M * (2 * a) * B ^ M) := by ac_rfl
      _ ≤ 3 * (2 * (a + b) * (4 * A) ^ M) := Nat.mul_le_mul_left 3 hsum
      _ = 6 * (a + b) * (4 * A) ^ M := by rw [← Nat.mul_assoc, ← Nat.mul_assoc 3 2 (a + b)]
  calc countLt (fun n => @decide (¬ HasStoppingTimeLe n (4 * M)) (Classical.propDecidable _))
        (2 ^ (2 * M + 1)) * (2 * a) * B ^ M
      = countLt (fun n => @decide (¬ HasStoppingTimeLe n (4 * M)) (Classical.propDecidable _))
          (2 ^ (2 * M + 1)) * (2 * a * B ^ M) := Nat.mul_assoc _ _ _
    _ ≤ 2 * (2 * a * B ^ M) + 3 * shellBadSum M * (2 * a * B ^ M) := hsh
    _ ≤ 4 * a * (4 * A) ^ M + 6 * (a + b) * (4 * A) ^ M := Nat.add_le_add h2 h3
    _ = (10 * a + 6 * b) * (4 * A) ^ M := by
        rw [← Nat.add_mul, show 4 * a + 6 * (a + b) = 10 * a + 6 * b by omega]

/-- **Prefix Shell Bound for `N ≥ 1`:** with `M = bitLen N / 2`, both
`natExceptionalCount (fun n => HasStoppingTimeLe n (4 * M)) N` and
`natExceptionalCount HasFiniteStoppingTime N` satisfy the exact shell bound with `4^M ≤ 2 * N`. -/
theorem sharper_prefix_master_bound {a b : Nat} (hab : 3 * (a * a) ≤ b * b)
    {N : Nat} (hN : 1 ≤ N) :
    let M := bitLen N / 2
    natExceptionalCount (fun n => HasStoppingTimeLe n (4 * M)) N * (2 * a) * (8 * (a * a)) ^ M ≤
      (10 * a + 6 * b) * (4 * ((a + b) * (a + b))) ^ M ∧
    natExceptionalCount HasFiniteStoppingTime N * (2 * a) * (8 * (a * a)) ^ M ≤
      (10 * a + 6 * b) * (4 * ((a + b) * (a + b))) ^ M ∧
    (1 ≤ M → 4 ^ M ≤ 2 * N) := by
  intro M
  have hbit : N + 1 ≤ 2 ^ (2 * M + 1) := by
    have hlt : N < 2 ^ bitLen N := lt_two_pow_bitLen N
    have hpow : 2 ^ bitLen N ≤ 2 ^ (2 * M + 1) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by dsimp [M]; omega)
    omega
  have hcnt1 : natExceptionalCount (fun n => HasStoppingTimeLe n (4 * M)) N ≤
      countLt (fun n => @decide (¬ HasStoppingTimeLe n (4 * M)) (Classical.propDecidable _))
        (2 ^ (2 * M + 1)) := by
    unfold natExceptionalCount
    exact Nat.le_trans (countLt_mono_pred (N + 1) (fun _ _ hn => sc_dec_true (sc_of_dec_true hn).2))
      (countLt_mono_bound _ hbit)
  have hcnt2 : natExceptionalCount HasFiniteStoppingTime N ≤
      natExceptionalCount (fun n => HasStoppingTimeLe n (4 * M)) N := by
    unfold natExceptionalCount
    exact countLt_mono_pred (N + 1) (fun _ _ hn =>
      let h1 := sc_of_dec_true hn
      sc_dec_true ⟨h1.1, fun h => h1.2 (hasFiniteStoppingTime_of_hasStoppingTimeLe h)⟩)
  have hb1 := Nat.le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hcnt1))
    (sharper_shell_master_bound hab M)
  have hb2 := Nat.le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hcnt2)) hb1
  refine ⟨hb1, hb2, fun hM => ?_⟩
  have h2m : 2 ^ (2 * M - 1) ≤ N :=
    Nat.le_trans (Nat.pow_le_pow_right (by decide : 0 < 2) (by dsimp [M]; omega))
      (two_pow_pred_bitLen_le hN)
  have hexp : 2 * M = (2 * M - 1) + 1 := by omega
  rw [show (4 : Nat) = 2 ^ 2 by decide, ← Nat.pow_mul, hexp, Nat.pow_succ, Nat.mul_comm]
  exact Nat.mul_le_mul_left 2 h2m

private theorem pow_lt_of_ge {x y D M₀ M : Nat} (hy : 0 < y) (hxy : x ≤ y)
    (hbase : x ^ M₀ * D < y ^ M₀) (hM : M₀ ≤ M) : x ^ M * D < y ^ M := by
  by_cases hx : x = 0
  · subst hx
    cases M₀ with
    | zero =>
      simp at hbase
      cases M with | zero => simpa using hbase | succ k => simp [hbase, Nat.pow_pos hy]
    | succ k =>
      have hM1 : 0 < M := by omega
      rw [Nat.zero_pow hM1, Nat.zero_mul]; exact Nat.pow_pos hy
  · have hdiff : M = M₀ + (M - M₀) := (Nat.add_sub_of_le hM).symm
    rw [hdiff, Nat.pow_add, Nat.pow_add, Nat.mul_right_comm (x ^ M₀) (x ^ (M - M₀)) D]
    exact Nat.lt_of_lt_of_le
      (Nat.mul_lt_mul_of_pos_right hbase (Nat.pow_pos (Nat.pos_of_ne_zero hx)))
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hxy _))

private theorem bitLen_div_two_ge {M₀ N : Nat} (hN : 2 ^ (2 * M₀) ≤ N) : M₀ ≤ bitLen N / 2 := by
  have hlt : N < 2 ^ bitLen N := lt_two_pow_bitLen N
  have hexp : 2 * M₀ < bitLen N :=
    Nat.lt_of_not_ge (fun h => absurd (Nat.pow_le_pow_right (by decide : 0 < 2) h) (by omega))
  omega

private theorem prefix_pow_split {c p q M A B C a2 N : Nat} (hpq : p ≤ q)
    (h4M : 4 ^ M ≤ 2 * N) (hpref : c * a2 * B ^ M ≤ C * (4 * A) ^ M) :
    c ^ q * (a2 ^ q * B ^ (q * M)) ≤ C ^ q * (2 ^ p * N ^ p * (4 ^ (q - p) * A ^ q) ^ M) := by
  have h1 := Nat.pow_le_pow_left hpref q
  have hgec : c ^ q * (a2 ^ q * B ^ (q * M)) = (c * a2 * B ^ M) ^ q := by
    rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul B M q, Nat.mul_comm M q, Nat.mul_assoc]
  have h4split : (4 ^ M) ^ q = (4 ^ M) ^ p * (4 ^ M) ^ (q - p) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hpq]
  have h4p : (4 ^ M) ^ p ≤ 2 ^ p * N ^ p := by rw [← Nat.mul_pow]; exact Nat.pow_le_pow_left h4M p
  have hR : (C * (4 * A) ^ M) ^ q =
      C ^ q * ((4 ^ M) ^ p * ((4 ^ (q - p) * A ^ q) ^ M)) := by
    rw [Nat.mul_pow, Nat.mul_pow 4 A M, Nat.mul_pow (4 ^ M) (A ^ M) q, h4split,
      Nat.mul_pow (4 ^ (q - p)) (A ^ q) M, ← Nat.pow_mul 4 M (q - p),
      ← Nat.pow_mul 4 (q - p) M, Nat.mul_comm M (q - p), ← Nat.pow_mul A M q,
      ← Nat.pow_mul A q M, Nat.mul_comm M q, Nat.mul_assoc ((4 ^ M) ^ p)]
  calc c ^ q * (a2 ^ q * B ^ (q * M)) = (c * a2 * B ^ M) ^ q := hgec
    _ ≤ (C * (4 * A) ^ M) ^ q := h1
    _ ≤ C ^ q * (2 ^ p * N ^ p * (4 ^ (q - p) * A ^ q) ^ M) := by
        rw [hR]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h4p)

/-- **General Power-Saving Lift:** if `0 < a`, `3 * (a * a) ≤ b * b`, `0 < p < q`, and
`4 ^ (q - p) * ((a + b) * (a + b)) ^ q < (8 * (a * a)) ^ q`, then
`HasPowerSavingDensityOne HasFiniteStoppingTime p q`. -/
theorem sharper_powerSaving_general {a b p q : Nat} (ha : 0 < a) (hab : 3 * (a * a) ≤ b * b)
    (_hp : 0 < p) (hpq : p < q)
    (hratio : 4 ^ (q - p) * ((a + b) * (a + b)) ^ q < (8 * (a * a)) ^ q) :
    HasPowerSavingDensityOne HasFiniteStoppingTime p q := by
  let A := (a + b) * (a + b); let B := 8 * (a * a); let C := 10 * a + 6 * b
  have hXpos : 0 < 4 ^ (q - p) * A ^ q :=
    Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (Nat.mul_pos (by omega) (by omega)))
  have hDpos : 0 < C ^ q * 2 ^ p :=
    Nat.mul_pos (Nat.pow_pos (by dsimp [C]; omega)) (Nat.pow_pos (by decide))
  rcases pow_mul_lt_pow_of_lt hXpos hratio hDpos with ⟨M₁, hM₁, hdom⟩
  refine ⟨2 ^ (2 * M₁), fun N hN => ?_⟩
  let M := bitLen N / 2
  have hM : M₁ ≤ M := bitLen_div_two_ge hN
  have hNpos : 1 ≤ N := Nat.le_trans (Nat.two_pow_pos _) hN
  have hpref := sharper_prefix_master_bound hab hNpos
  have hM1 : 1 ≤ M := Nat.le_trans hM₁ hM
  have hpowq := prefix_pow_split (M := M) (Nat.le_of_lt hpq) (hpref.2.2 hM1) hpref.2.1
  have hdrop : natExceptionalCount HasFiniteStoppingTime N ^ q * B ^ (q * M) ≤
      natExceptionalCount HasFiniteStoppingTime N ^ q * ((2 * a) ^ q * B ^ (q * M)) :=
    Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega)))
  have hBpos : 0 < B ^ q := Nat.pow_pos (Nat.mul_pos (by decide) (Nat.mul_pos ha ha))
  have hdomM := pow_lt_of_ge hBpos (Nat.le_of_lt hratio) hdom hM
  rw [← Nat.pow_mul B q M] at hdomM
  have hfin : natExceptionalCount HasFiniteStoppingTime N ^ q * B ^ (q * M) <
      N ^ p * B ^ (q * M) := by
    calc natExceptionalCount HasFiniteStoppingTime N ^ q * B ^ (q * M)
        ≤ C ^ q * (2 ^ p * N ^ p * (4 ^ (q - p) * A ^ q) ^ M) := Nat.le_trans hdrop hpowq
      _ = N ^ p * ((4 ^ (q - p) * A ^ q) ^ M * (C ^ q * 2 ^ p)) := by ac_rfl
      _ < N ^ p * B ^ (q * M) := Nat.mul_lt_mul_of_pos_left hdomM (Nat.pow_pos hNpos)
  exact Nat.lt_of_mul_lt_mul_right hfin

private theorem pell_780_1351_ten : 2 * 4541161 ^ 10 < 4867200 ^ 10 := by decide
private theorem pell_780_1351_forty_one : 16 * 4541161 ^ 41 < 4867200 ^ 41 := by decide

/-- **Main Sharper Chernoff Theorem (`19/20 = 0.95`):** unconditional pure-`Nat` power-saving
exceptional-set bound `HasPowerSavingDensityOne HasFiniteStoppingTime 19 20` (`count^20 < N^19`),
sharpening `237/238` (`0.9958`) by more than `11x` in the saving exponent. -/
theorem sharper_power_saving_density_19_20 :
    HasPowerSavingDensityOne HasFiniteStoppingTime 19 20 := by
  have h20 : 4 ^ (20 - 19) * ((780 + 1351) * (780 + 1351)) ^ 20 <
      (8 * (780 * 780)) ^ 20 := by
    have hsq := Nat.mul_lt_mul_of_lt_of_lt pell_780_1351_ten pell_780_1351_ten
    have h1 : (2 * 4541161 ^ 10) * (2 * 4541161 ^ 10) =
        4 ^ (20 - 19) * ((780 + 1351) * (780 + 1351)) ^ 20 := by
      calc (2 * 4541161 ^ 10) * (2 * 4541161 ^ 10)
          = 4 * (4541161 ^ 10 * 4541161 ^ 10) := by ac_rfl
        _ = 4 ^ (20 - 19) * ((780 + 1351) * (780 + 1351)) ^ 20 := by
            rw [show (780 + 1351) * (780 + 1351) = 4541161 by decide,
              show (20 - 19 : Nat) = 1 by decide, Nat.pow_one,
              show (20 : Nat) = 10 + 10 by decide, Nat.pow_add]
    have h2 : 4867200 ^ 10 * 4867200 ^ 10 = (8 * (780 * 780)) ^ 20 := by
      rw [show 8 * (780 * 780) = 4867200 by decide,
        show (20 : Nat) = 10 + 10 by decide, Nat.pow_add]
    rwa [← h1, ← h2]
  exact sharper_powerSaving_general (by decide) (by decide) (by decide) (by decide) h20

/-- **Sharper Chernoff Theorem (`39/41 = 0.9512`):** unconditional power-saving exceptional-set
bound `HasPowerSavingDensityOne HasFiniteStoppingTime 39 41`. -/
theorem sharper_power_saving_density_39_41 :
    HasPowerSavingDensityOne HasFiniteStoppingTime 39 41 := by
  have h41 : 4 ^ (41 - 39) * ((780 + 1351) * (780 + 1351)) ^ 41 <
      (8 * (780 * 780)) ^ 41 := by
    rw [show 4 ^ (41 - 39) = 16 by decide,
      show (780 + 1351) * (780 + 1351) = 4541161 by decide,
      show 8 * (780 * 780) = 4867200 by decide]
    exact pell_780_1351_forty_one
  exact sharper_powerSaving_general (by decide) (by decide) (by decide) (by decide) h41

private theorem pow_15_16_mul_lt (k M : Nat) (hk : 0 < k) (hM : 11 * k ≤ M) :
    2 ^ k * 15 ^ M < 16 ^ M := by
  have h15_11 : 2 * 15 ^ 11 < 16 ^ 11 := by decide
  have hk' : 15 ^ (11 * k) * 2 ^ k < 16 ^ (11 * k) := by
    have hpow := Nat.pow_lt_pow_left h15_11 (Nat.ne_of_gt hk)
    rw [Nat.mul_pow, Nat.mul_comm (2 ^ k), ← Nat.pow_mul 15 11 k, ← Nat.pow_mul 16 11 k] at hpow
    exact hpow
  have hM' := pow_lt_of_ge (by decide : 0 < 16) (by decide : 15 ≤ 16) hk' hM
  rwa [Nat.mul_comm] at hM'

private theorem pell_explicit_ratio_20_21 {M : Nat} (hM : 1001 ≤ M) :
    (4 * 4541161 ^ 21) ^ M * (15906 ^ 21 * 2 ^ 20) < 1560 ^ 21 * 4867200 ^ (21 * M) := by
  have h16_15 : 16 * (4 * 4541161 ^ 21) < 15 * 4867200 ^ 21 := by decide
  have hconst : 15906 ^ 21 * 2 ^ 20 < 1560 ^ 21 * 2 ^ 91 := by decide
  have h15_pow : 2 ^ 91 * 15 ^ M < 16 ^ M := pow_15_16_mul_lt 91 M (by decide) (by omega)
  have hpowM : 16 ^ M * (4 * 4541161 ^ 21) ^ M ≤ 15 ^ M * 4867200 ^ (21 * M) := by
    rw [← Nat.mul_pow 16 (4 * 4541161 ^ 21) M, Nat.pow_mul 4867200 21 M,
      ← Nat.mul_pow 15 (4867200 ^ 21) M]
    exact Nat.pow_le_pow_left (Nat.le_of_lt h16_15) M
  have hmul : 16 ^ M * ((4 * 4541161 ^ 21) ^ M * (15906 ^ 21 * 2 ^ 20)) <
      16 ^ M * (1560 ^ 21 * 4867200 ^ (21 * M)) := by
    calc 16 ^ M * ((4 * 4541161 ^ 21) ^ M * (15906 ^ 21 * 2 ^ 20))
        = (16 ^ M * (4 * 4541161 ^ 21) ^ M) * (15906 ^ 21 * 2 ^ 20) := by ac_rfl
      _ ≤ (15 ^ M * 4867200 ^ (21 * M)) * (15906 ^ 21 * 2 ^ 20) := Nat.mul_le_mul_right _ hpowM
      _ < (15 ^ M * 4867200 ^ (21 * M)) * (1560 ^ 21 * 2 ^ 91) :=
          Nat.mul_lt_mul_of_pos_left hconst (Nat.mul_pos (Nat.pow_pos (by decide))
            (Nat.pow_pos (by decide)))
      _ = (2 ^ 91 * 15 ^ M) * (1560 ^ 21 * 4867200 ^ (21 * M)) := by ac_rfl
      _ < 16 ^ M * (1560 ^ 21 * 4867200 ^ (21 * M)) :=
          Nat.mul_lt_mul_of_pos_right h15_pow (Nat.mul_pos (Nat.pow_pos (by decide))
            (Nat.pow_pos (by decide)))
  exact Nat.lt_of_mul_lt_mul_left hmul

/-- **Explicit Concrete `20/21` Bound (`N ≥ 2 ^ 2002`):** for every `N ≥ 2 ^ 2002`,
`natExceptionalCount HasFiniteStoppingTime N ^ 21 < N ^ 20`. -/
theorem sharper_power_saving_explicit_20_21 (N : Nat) (hN : 2 ^ 2002 ≤ N) :
    natExceptionalCount HasFiniteStoppingTime N ^ 21 < N ^ 20 := by
  let M := bitLen N / 2
  have hN' : 2 ^ (2 * 1001) ≤ N := by rw [show 2 * 1001 = 2002 by decide]; exact hN
  have hM : 1001 ≤ M := bitLen_div_two_ge hN'
  have hNpos : 1 ≤ N := Nat.le_trans (Nat.two_pow_pos _) hN
  have hpref := sharper_prefix_master_bound (a := 780) (b := 1351) (by decide) hNpos
  rw [show 2 * 780 = 1560 by decide, show 8 * (780 * 780) = 4867200 by decide,
    show 10 * 780 + 6 * 1351 = 15906 by decide,
    show (780 + 1351) * (780 + 1351) = 4541161 by decide] at hpref
  have hpow21 := prefix_pow_split (p := 20) (q := 21) (M := M) (A := 4541161) (B := 4867200)
    (C := 15906) (a2 := 1560) (by decide) (hpref.2.2 (by omega)) hpref.2.1
  rw [show (21 - 20 : Nat) = 1 by decide, Nat.pow_one] at hpow21
  have hcomb : natExceptionalCount HasFiniteStoppingTime N ^ 21 *
      (1560 ^ 21 * 4867200 ^ (21 * M)) < N ^ 20 * (1560 ^ 21 * 4867200 ^ (21 * M)) := by
    calc natExceptionalCount HasFiniteStoppingTime N ^ 21 * (1560 ^ 21 * 4867200 ^ (21 * M))
        ≤ 15906 ^ 21 * (2 ^ 20 * N ^ 20 * (4 * 4541161 ^ 21) ^ M) := hpow21
      _ = N ^ 20 * ((4 * 4541161 ^ 21) ^ M * (15906 ^ 21 * 2 ^ 20)) := by ac_rfl
      _ < N ^ 20 * (1560 ^ 21 * 4867200 ^ (21 * M)) :=
          Nat.mul_lt_mul_of_pos_left (pell_explicit_ratio_20_21 hM) (Nat.pow_pos hNpos)
  exact Nat.lt_of_mul_lt_mul_right hcomb

/-- **Sharper Chernoff Theorem (`20/21 = 0.9524`):**
`HasPowerSavingDensityOne HasFiniteStoppingTime 20 21` with explicit threshold `2 ^ 2002`. -/
theorem sharper_power_saving_density_20_21 :
    HasPowerSavingDensityOne HasFiniteStoppingTime 20 21 :=
  ⟨2 ^ 2002, sharper_power_saving_explicit_20_21⟩

/-! ### 4. Constructive Natural-Density Modulus (`6x` Tighter) & Stopping-Time Tail -/

/-- **Sharper Constructive Density Modulus:** `2 ^ (20 * bitLen D + 100)`, improving on
`ExceptionalDensity.explicitDensityThreshold D = 2 ^ (119 * bitLen (4 * D))` by nearly `6x`
in the bit exponent. -/
def sharperDensityThreshold (D : Nat) : Nat :=
  2 ^ (20 * bitLen D + 100)

/-- `sharperDensityThreshold D` is strictly smaller than `explicitDensityThreshold D` for every
`D > 0`. -/
theorem sharperDensityThreshold_lt_explicit {D : Nat} (hD : 0 < D) :
    sharperDensityThreshold D < explicitDensityThreshold D := by
  have h4 : bitLen D + 2 ≤ bitLen (4 * D) := by
    cases D with
    | zero => omega
    | succ d =>
      have h2 : bitLen (2 * (d + 1)) = bitLen (d + 1) + 1 := by
        rw [show 2 * (d + 1) = (2 * d + 1) + 1 by omega, bitLen,
          show (2 * d + 1 + 1) / 2 = d + 1 by omega]
      have h3 : bitLen (4 * (d + 1)) = bitLen (2 * (d + 1)) + 1 := by
        rw [show 4 * (d + 1) = (4 * d + 3) + 1 by omega, bitLen,
          show (4 * d + 3 + 1) / 2 = 2 * (d + 1) by omega]
      omega
  exact Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)

private theorem sharper_modulus_ratio {D M : Nat} (hM : 10 * (bitLen D + 5) ≤ M) :
    31812 * D * 4541161 ^ M < 1560 * 4867200 ^ M := by
  let t := bitLen D + 5
  have hDlt : 31812 * D < 1560 * 2 ^ t := by
    have hd : D < 2 ^ bitLen D := lt_two_pow_bitLen D
    have h25 : 31812 < 1560 * 2 ^ 5 := by decide
    have hpow : 2 ^ t = 2 ^ bitLen D * 2 ^ 5 := by dsimp [t]; rw [Nat.pow_add]
    calc 31812 * D ≤ 31812 * 2 ^ bitLen D := Nat.mul_le_mul_left _ (Nat.le_of_lt hd)
      _ < (1560 * 2 ^ 5) * 2 ^ bitLen D := Nat.mul_lt_mul_of_pos_right h25 (Nat.two_pow_pos _)
      _ = 1560 * 2 ^ t := by rw [hpow]; ac_rfl
  have hpowM : 2 ^ t * 4541161 ^ M < 4867200 ^ M := by
    have hbase : 4541161 ^ (10 * t) * 2 ^ t < 4867200 ^ (10 * t) := by
      rw [Nat.mul_comm _ (2 ^ t), Nat.pow_mul 4541161 10 t, ← Nat.mul_pow, Nat.pow_mul 4867200]
      exact Nat.pow_lt_pow_left pell_780_1351_ten (by dsimp [t]; omega)
    rw [Nat.mul_comm]
    exact pow_lt_of_ge (by decide : 0 < 4867200) (by decide : 4541161 ≤ 4867200) hbase hM
  calc 31812 * D * 4541161 ^ M < (1560 * 2 ^ t) * 4541161 ^ M :=
        Nat.mul_lt_mul_of_pos_right hDlt (Nat.pow_pos (by decide))
    _ = 1560 * (2 ^ t * 4541161 ^ M) := Nat.mul_assoc _ _ _
    _ < 1560 * 4867200 ^ M := Nat.mul_lt_mul_of_pos_left hpowM (by decide)

/-- **Constructive Natural-Density Modulus (`20 * bitLen D + 100`):** for every `D > 0` and
`N ≥ sharperDensityThreshold D`, `natExceptionalCount HasFiniteStoppingTime N * D < N` (and even
within `2 * bitLen N` standard Collatz steps). -/
theorem sharper_explicit_modulus {D N : Nat} (_hD : 0 < D) (hN : sharperDensityThreshold D ≤ N) :
    natExceptionalCount (fun n => HasStoppingTimeLe n (2 * bitLen N)) N * D < N ∧
      natExceptionalCount HasFiniteStoppingTime N * D < N := by
  let t := bitLen D + 5; let M := bitLen N / 2
  have hpowN : 2 ^ (2 * (10 * t)) ≤ N := by
    dsimp [t]; rw [show 2 * (10 * (bitLen D + 5)) = 20 * bitLen D + 100 by omega]; exact hN
  have hM : 10 * t ≤ M := bitLen_div_two_ge hpowN
  have hNpos : 1 ≤ N := Nat.le_trans (Nat.two_pow_pos _) hN
  have hpref := sharper_prefix_master_bound (a := 780) (b := 1351) (by decide) hNpos
  dsimp only at hpref
  rw [show 2 * 780 = 1560 by decide, show 8 * (780 * 780) = 4867200 by decide,
    show 10 * 780 + 6 * 1351 = 15906 by decide,
    show 4 * ((780 + 1351) * (780 + 1351)) = 4 * 4541161 by decide] at hpref
  have h4M : 4 ^ M ≤ 2 * N := hpref.2.2 (by dsimp [t] at hM; omega)
  have hcnt_le : natExceptionalCount (fun n => HasStoppingTimeLe n (2 * bitLen N)) N ≤
      natExceptionalCount (fun n => HasStoppingTimeLe n (4 * M)) N := by
    unfold natExceptionalCount
    exact countLt_mono_pred (N + 1) (fun _ _ hn =>
      let h1 := sc_of_dec_true hn
      sc_dec_true ⟨h1.1, fun h => h1.2 (hasStoppingTimeLe_mono (by dsimp [M]; omega) h)⟩)
  have hmul : natExceptionalCount (fun n => HasStoppingTimeLe n (4 * M)) N * D *
      (1560 * 4867200 ^ M) ≤ (31812 * D * 4541161 ^ M) * N := by
    calc natExceptionalCount (fun n => HasStoppingTimeLe n (4 * M)) N * D * (1560 * 4867200 ^ M)
        = (natExceptionalCount (fun n => HasStoppingTimeLe n (4 * M)) N * 1560 *
            4867200 ^ M) * D := by ac_rfl
      _ ≤ (15906 * (4 ^ M * 4541161 ^ M)) * D := by
            rw [Nat.mul_pow 4 4541161 M] at hpref; exact Nat.mul_le_mul_right D hpref.1
      _ ≤ (15906 * ((2 * N) * 4541161 ^ M)) * D :=
            Nat.mul_le_mul_right D (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h4M))
      _ = (31812 * D * 4541161 ^ M) * N := by
            rw [show 31812 = 15906 * 2 by decide]; ac_rfl
  have hlt_N := Nat.mul_lt_mul_of_pos_right (sharper_modulus_ratio hM) hNpos
  rw [Nat.mul_comm (1560 * 4867200 ^ M) N] at hlt_N
  have hlt1 := Nat.lt_of_mul_lt_mul_right (Nat.lt_of_le_of_lt hmul hlt_N)
  have hlt_tail := Nat.lt_of_le_of_lt (Nat.mul_le_mul_right D hcnt_le) hlt1
  have hle_fin : natExceptionalCount HasFiniteStoppingTime N ≤
      natExceptionalCount (fun n => HasStoppingTimeLe n (2 * bitLen N)) N := by
    unfold natExceptionalCount
    exact countLt_mono_pred (N + 1) (fun _ _ hn =>
      let h1 := sc_of_dec_true hn
      sc_dec_true ⟨h1.1, fun h => h1.2 (hasFiniteStoppingTime_of_hasStoppingTimeLe h)⟩)
  exact ⟨hlt_tail, Nat.lt_of_le_of_lt (Nat.mul_le_mul_right D hle_fin) hlt_tail⟩

private theorem badStrictCount_tail_half (t : Nat) :
    badStrictCount (20 * t + 41) * 2 ^ (t + 1) ≤ 2 ^ (20 * t + 41) := by
  let m := 10 * (t + 2); let k := 20 * t + 41
  have hc := badStrictCount_odd_chernoff (a := 780) (b := 1351) (by decide) m
  have hk_eq : 2 * m + 1 = k := by dsimp [m, k]; omega
  have hpow : 2 ^ (t + 2) * 4541161 ^ m ≤ 4867200 ^ m := by
    dsimp [m]; rw [Nat.pow_mul 4541161 10 (t + 2), ← Nat.mul_pow, Nat.pow_mul 4867200 10 (t + 2)]
    exact Nat.pow_le_pow_left (Nat.le_of_lt pell_780_1351_ten) (t + 2)
  have hmul : badStrictCount k * 2 ^ (t + 1) * (1560 * 4867200 ^ m) ≤
      2 ^ k * (1560 * 4867200 ^ m) := by
    have hc' : badStrictCount k * 1560 * 4867200 ^ m ≤ 2131 * 4541161 ^ m * 2 ^ k := by
      rw [← hk_eq, show (1560 : Nat) = 2 * 780 by decide,
        show (4867200 : Nat) = 8 * (780 * 780) by decide,
        show (2131 : Nat) = 780 + 1351 by decide,
        show (4541161 : Nat) = 2131 * 2131 by decide]
      exact hc
    have hstep1 : badStrictCount k * 2 ^ (t + 1) * (1560 * 4867200 ^ m) ≤
        2131 * 4541161 ^ m * 2 ^ (t + 1) * 2 ^ k := by
      calc badStrictCount k * 2 ^ (t + 1) * (1560 * 4867200 ^ m)
          = badStrictCount k * (2 ^ (t + 1) * (1560 * 4867200 ^ m)) := Nat.mul_assoc _ _ _
        _ = badStrictCount k * ((1560 * 4867200 ^ m) * 2 ^ (t + 1)) := by
              rw [Nat.mul_comm (2 ^ (t + 1)) (1560 * 4867200 ^ m)]
        _ = (badStrictCount k * 1560 * 4867200 ^ m) * 2 ^ (t + 1) := by
              rw [← Nat.mul_assoc, ← Nat.mul_assoc]
        _ ≤ (2131 * 4541161 ^ m * 2 ^ k) * 2 ^ (t + 1) := Nat.mul_le_mul_right _ hc'
        _ = 2131 * 4541161 ^ m * 2 ^ (t + 1) * 2 ^ k := Nat.mul_right_comm _ _ _
    have hstep2 : 2131 * 4541161 ^ m * 2 ^ (t + 1) ≤ 1560 * (2 ^ (t + 2) * 4541161 ^ m) := by
      rw [Nat.pow_succ 2 (t + 1)]
      calc 2131 * 4541161 ^ m * 2 ^ (t + 1)
          ≤ 3120 * 4541161 ^ m * 2 ^ (t + 1) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
        _ = 1560 * (2 ^ (t + 1) * 2 * 4541161 ^ m) := by
            rw [show (3120 : Nat) = 1560 * 2 by decide, Nat.mul_assoc 1560 2,
              Nat.mul_assoc 1560 (2 * 4541161 ^ m) (2 ^ (t + 1)),
              Nat.mul_comm (2 * 4541161 ^ m) (2 ^ (t + 1)),
              ← Nat.mul_assoc (2 ^ (t + 1)) 2 (4541161 ^ m)]
    calc badStrictCount k * 2 ^ (t + 1) * (1560 * 4867200 ^ m)
        ≤ 2131 * 4541161 ^ m * 2 ^ (t + 1) * 2 ^ k := hstep1
      _ ≤ 1560 * (2 ^ (t + 2) * 4541161 ^ m) * 2 ^ k := Nat.mul_le_mul_right _ hstep2
      _ ≤ 1560 * 4867200 ^ m * 2 ^ k :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 1560 hpow)
      _ = 2 ^ k * (1560 * 4867200 ^ m) := Nat.mul_comm _ _
  exact Nat.le_of_mul_le_mul_right hmul (Nat.mul_pos (by decide) (Nat.pow_pos (by decide)))

private theorem countLt_bounded_stopping_le (k N : Nat) :
    natExceptionalCount (fun n => HasStoppingTimeLe n (2 * k)) N ≤
      2 ^ k + (badStrictCount k * ((N + 1) / 2 ^ k) + badStrictCount k) := by
  unfold natExceptionalCount; dsimp only
  have h1 := countLt_mono_pred (N + 1)
    (p := fun n => @decide (1 ≤ n ∧ ¬ HasStoppingTimeLe n (2 * k)) (Classical.propDecidable _))
    (q := fun n => decide (n < 2 ^ k) || badStrictResidue k (n % 2 ^ k)) (fun n _ hn => by
    by_cases hsm : n < 2 ^ k
    · rw [Bool.or_eq_true, decide_eq_true hsm]; exact Or.inl rfl
    · by_cases hbad : badStrictResidue k (n % 2 ^ k) = true
      · rw [Bool.or_eq_true, hbad]; exact Or.inr rfl
      · exfalso
        have hlow := Nat.le_of_not_lt (fun hlt => absurd (decide_eq_true hlt) hbad)
        have hdrop := (terras_lt_of_two_mul_three_pow_le (Nat.le_of_not_lt hsm) hlow).2.1
        exact (sc_of_dec_true hn).2 hdrop)
  have hor := countLt_or_le (fun n => decide (n < 2 ^ k))
    (fun n => badStrictResidue k (n % 2 ^ k)) (N + 1)
  have hper := countLt_periodic_le (fun n => badStrictResidue k (n % 2 ^ k)) (Nat.two_pow_pos k)
    (badStrictResidue_mod_periodic k) (N + 1)
  rw [countLt_badStrictResidue_mod_eq k] at hper
  have hsm := countLt_lt_bound (2 ^ k) (N + 1)
  omega

/-- **Fixed-Horizon Quantitative Stopping-Time Tail:** for any `t : Nat` and
`N ≥ 2 ^ (21 * t + 44)`, exceptions failing `HasStoppingTimeLe n (40 * t + 82)` satisfy
`count * 2 ^ t < N`. -/
theorem sharper_fixed_horizon_tail (t N : Nat) (hN : 2 ^ (21 * t + 44) ≤ N) :
    natExceptionalCount (fun n => HasStoppingTimeLe n (40 * t + 82)) N * 2 ^ t < N := by
  let k := 20 * t + 41
  have hNpos : 1 ≤ N := Nat.le_trans (Nat.two_pow_pos _) hN
  have hcnt : natExceptionalCount (fun n => HasStoppingTimeLe n (40 * t + 82)) N ≤
      2 ^ k + (badStrictCount k * ((N + 1) / 2 ^ k) + badStrictCount k) := by
    rw [show 40 * t + 82 = 2 * k by dsimp [k]; omega]; exact countLt_bounded_stopping_le k N
  have hbad : badStrictCount k * 2 ^ (t + 1) ≤ 2 ^ k := badStrictCount_tail_half t
  have h8k : 8 * 2 ^ k ≤ N := by
    rw [show (8 : Nat) = 2 ^ 3 by decide, ← Nat.pow_add]
    exact Nat.le_trans (Nat.pow_le_pow_right (by decide : 0 < 2) (by dsimp [k]; omega)) hN
  have h8kt : 8 * (2 ^ k * 2 ^ t) ≤ N := by
    rw [← Nat.pow_add, show (8 : Nat) = 2 ^ 3 by decide, ← Nat.pow_add]
    exact Nat.le_trans (Nat.pow_le_pow_right (by decide : 0 < 2) (by dsimp [k]; omega)) hN
  have hdiv : (N + 1) / 2 ^ k ≤ N / 2 ^ k + 1 := by
    have : N + 1 ≤ N + 2 ^ k := by have := Nat.two_pow_pos k; omega
    have hle := Nat.div_le_div_right (c := 2 ^ k) this
    rwa [Nat.add_div_right N (Nat.two_pow_pos k)] at hle
  have hq : badStrictCount k * ((N + 1) / 2 ^ k) * (2 * 2 ^ t) ≤ N + 2 ^ k := by
    have hmul := Nat.mul_le_mul_right ((N + 1) / 2 ^ k) hbad
    have hpow : 2 ^ k * ((N + 1) / 2 ^ k) ≤ N + 2 ^ k := by
      calc 2 ^ k * ((N + 1) / 2 ^ k) ≤ 2 ^ k * (N / 2 ^ k + 1) := Nat.mul_le_mul_left _ hdiv
        _ = 2 ^ k * (N / 2 ^ k) + 2 ^ k := by rw [Nat.mul_add, Nat.mul_one]
        _ ≤ N + 2 ^ k := Nat.add_le_add_right (Nat.mul_div_le N (2 ^ k)) _
    calc badStrictCount k * ((N + 1) / 2 ^ k) * (2 * 2 ^ t)
        = badStrictCount k * 2 ^ (t + 1) * ((N + 1) / 2 ^ k) := by
            rw [Nat.mul_comm 2 (2 ^ t), ← Nat.pow_succ, Nat.mul_right_comm]
      _ ≤ 2 ^ k * ((N + 1) / 2 ^ k) := hmul
      _ ≤ N + 2 ^ k := hpow
  have hb_t : badStrictCount k * (2 * 2 ^ t) ≤ 2 ^ k := by
    rw [Nat.mul_comm 2 (2 ^ t), ← Nat.pow_succ]; exact hbad
  have htot := Nat.mul_le_mul_right (2 * 2 ^ t) hcnt
  rw [Nat.add_mul, Nat.add_mul] at htot
  have h2kt : 2 ^ k * (2 * 2 ^ t) = 2 * (2 ^ k * 2 ^ t) := Nat.mul_left_comm _ 2 _
  have hlhs : natExceptionalCount (fun n => HasStoppingTimeLe n (40 * t + 82)) N * 2 ^ t * 2 =
      natExceptionalCount (fun n => HasStoppingTimeLe n (40 * t + 82)) N * (2 * 2 ^ t) := by
    rw [Nat.mul_assoc, Nat.mul_comm (2 ^ t) 2]
  omega

/-! ### 5. Barrier 2 (`5n + 1`) Chernoff Contrast & Compatibility Bridges -/

/-- **Barrier 2 (`5n + 1`) Moment Growth:** for any `0 < a` with `b * b ≤ 5 * (a * a)` and
`8 * (a * a) < (a + b) * (a + b)`, the `s = 1/2` moment weight `cherWeight a b (2 * m)` is a
strict lower bound on `5^(c/2) * a^(2m)` whose sum over `allBitVecs (2 * m)` grows
exponentially relative to `2^(2m) * 2^m * a^(2m)`. -/
theorem five_n_plus_one_moment_growth {a b : Nat} (ha : 0 < a) (hb5 : b * b ≤ 5 * (a * a))
    (hgrows : 8 * (a * a) < (a + b) * (a + b)) :
    (∀ m : Nat, ∀ v ∈ allBitVecs (2 * m),
      cherWeight a b (2 * m) v * cherWeight a b (2 * m) v ≤ 5 ^ countOnes v * a ^ (4 * m)) ∧
    (∀ m : Nat, 1 ≤ m →
      2 ^ (2 * m) * (2 ^ m * a ^ (2 * m)) < listSum (cherWeight a b (2 * m)) (allBitVecs (2 * m))) ∧
    (∀ D : Nat, 0 < D → ∃ m : Nat, 0 < m ∧
      2 ^ (2 * m) * (2 ^ m * a ^ (2 * m)) * D <
        listSum (cherWeight a b (2 * m)) (allBitVecs (2 * m))) := by
  refine ⟨fun m v hv => ?_, fun m hm => ?_, fun D hD => ?_⟩
  · have hc : countOnes v ≤ 2 * m := (mem_allBitVecs_iff (2 * m) v).mp hv ▸ countOnes_le_length v
    have hsq : cherWeight a b (2 * m) v * cherWeight a b (2 * m) v =
        a ^ (2 * (2 * m - countOnes v)) * (b * b) ^ countOnes v := by
      simp only [cherWeight]
      rw [← Nat.pow_two, Nat.mul_pow, ← Nat.pow_mul b (countOnes v) 2,
        Nat.mul_comm (countOnes v) 2, Nat.pow_mul b 2 (countOnes v), Nat.pow_two b,
        ← Nat.pow_mul a (2 * m - countOnes v) 2, Nat.mul_comm (2 * m - countOnes v) 2]
    have hpow5 : (b * b) ^ countOnes v ≤ 5 ^ countOnes v * a ^ (2 * countOnes v) := by
      have h5 := Nat.pow_le_pow_left hb5 (countOnes v)
      rwa [Nat.mul_pow 5 (a * a), ← Nat.pow_two a, ← Nat.pow_mul a 2 (countOnes v)] at h5
    have hexp : 2 * (2 * m - countOnes v) + 2 * countOnes v = 4 * m := by omega
    calc cherWeight a b (2 * m) v * cherWeight a b (2 * m) v
        ≤ a ^ (2 * (2 * m - countOnes v)) * (5 ^ countOnes v * a ^ (2 * countOnes v)) :=
          hsq ▸ Nat.mul_le_mul_left _ hpow5
      _ = 5 ^ countOnes v * (a ^ (2 * (2 * m - countOnes v)) * a ^ (2 * countOnes v)) := by ac_rfl
      _ = 5 ^ countOnes v * a ^ (4 * m) := by rw [← Nat.pow_add, hexp]
  · rw [cherWeight_allBitVecs_sum, Nat.pow_mul (a + b) 2 m, Nat.pow_two (a + b)]
    have h8 : 2 ^ (2 * m) * (2 ^ m * a ^ (2 * m)) = (8 * (a * a)) ^ m := by
      rw [← Nat.mul_assoc, ← Nat.pow_add, show 2 * m + m = 3 * m by omega, Nat.pow_mul 2 3 m,
        show 2 ^ 3 = 8 by decide, Nat.pow_mul a 2 m, Nat.pow_two a, ← Nat.mul_pow]
    rw [h8]; exact Nat.pow_lt_pow_left hgrows (Nat.ne_of_gt hm)
  · rcases pow_mul_lt_pow_of_lt (Nat.mul_pos (by decide) (Nat.mul_pos ha ha)) hgrows hD with
      ⟨m, hm, hdom⟩
    refine ⟨m, hm, ?_⟩
    rw [cherWeight_allBitVecs_sum, Nat.pow_mul (a + b) 2 m, Nat.pow_two (a + b)]
    have h8 : 2 ^ (2 * m) * (2 ^ m * a ^ (2 * m)) = (8 * (a * a)) ^ m := by
      rw [← Nat.mul_assoc, ← Nat.pow_add, show 2 * m + m = 3 * m by omega, Nat.pow_mul 2 3 m,
        show 2 ^ 3 = 8 by decide, Nat.pow_mul a 2 m, Nat.pow_two a, ← Nat.mul_pow]
    rwa [h8]

/-- **Barrier 2 (`5n + 1`) vs `3n + 1` Dichotomy:**
for `3n + 1`, the `s = 1/2` Chernoff factor decays exponentially as `(4541161 / 4867200)^m`;
for `5n + 1`, the `s = 1/2` moment lower bound (`a = 100, b = 223`) grows exponentially as
`(104329 / 80000)^m` (and `5n + 1` admits the positive cycle `13 → 66 → … → 13`). -/
theorem chernoff_separates_3n1_from_5n1 :
    (∀ m : Nat, badCount (2 * m) * 4867200 ^ m ≤ 4541161 ^ m * 2 ^ (2 * m)) ∧
    (∀ m : Nat, ∀ v ∈ allBitVecs (2 * m),
      cherWeight 100 223 (2 * m) v * cherWeight 100 223 (2 * m) v ≤
        5 ^ countOnes v * 100 ^ (4 * m)) ∧
    (∀ D : Nat, 0 < D → ∃ m : Nat, 0 < m ∧
      80000 ^ m * D < listSum (cherWeight 100 223 (2 * m)) (allBitVecs (2 * m))) := by
  have h5 := five_n_plus_one_moment_growth (a := 100) (b := 223) (by decide) (by decide) (by decide)
  refine ⟨badCount_even_chernoff_780_1351, h5.1, fun D hD => ?_⟩
  rcases h5.2.2 D hD with ⟨m, hm, hdom⟩
  refine ⟨m, hm, ?_⟩
  have h8 : 2 ^ (2 * m) * (2 ^ m * 100 ^ (2 * m)) = 80000 ^ m := by
    rw [← Nat.mul_assoc, ← Nat.pow_add, show 2 * m + m = 3 * m by omega, Nat.pow_mul 2 3 m,
      show 2 ^ 3 = 8 by decide, Nat.pow_mul 100 2 m, ← Nat.mul_pow,
      show 8 * 100 ^ 2 = 80000 by decide]
  rwa [h8] at hdom

/-- Compatibility bridge: `sharper_power_saving_density_19_20` implies `HasNaturalDensityOne`
and `HasLogDensityOne` for `HasFiniteStoppingTime`. -/
theorem sharper_powerSaving_bridges_density_one :
    HasNaturalDensityOne HasFiniteStoppingTime ∧ HasLogDensityOne HasFiniteStoppingTime :=
  ⟨hasNaturalDensityOne_of_powerSaving (by decide) (by decide) sharper_power_saving_density_19_20,
   hasLogDensityOne_of_powerSaving (by decide) (by decide) sharper_power_saving_density_19_20⟩

/-- **Cycle Obstruction (`Barrier 4`):** even the sharpened `N^(19/20)` bound still permits
excluding any finite cycle orbit `cycleOrbitList n L` at exponent `39/40`. -/
theorem sharper_powerSaving_allows_cycle (n L : Nat) :
    HasPowerSavingDensityOne
      (fun m => HasFiniteStoppingTime m ∧ m ∉ cycleOrbitList n L) 39 40 :=
  hasPowerSaving_and_expSparse (by decide) (by decide)
    sharper_power_saving_density_19_20 (isExpSparse_cycleOrbitList n L)

end SolveCollatz
