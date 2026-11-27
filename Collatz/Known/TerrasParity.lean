/-
Copyright (c) 2026 The solve-collatz contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Collatz.Core.Syracuse

/-!
# Terras (1976) Parity-Vector Bijection mod `2^k` (`KNOWN-001`, Part 1)

Self-contained Lean 4 core formalization (zero Mathlib) of the compressed Collatz (Terras) map
and Terras's fundamental parity-vector theorem modulo `2^k`:
- Compressed map `terrasStep`, iterates `terrasIter`, parity vectors `terrasParityVec`, and
  `countOnes`.
- Exact orbit bridge `collatzIter_eq_terrasIter` linking `terrasIter` to frozen
  `Challenge.collatzIter`.
- Exact congruence law `terrasParityVec_mod_two_pow`:
  `terrasParityVec k (n + 2 ^ k * q) = terrasParityVec k n` and
  `terrasIter k (n + 2 ^ k * q) = terrasIter k n + 3 ^ countOnes (terrasParityVec k n) * q`.
- Fundamental bijection mod `2^k`: injectivity (`terrasParityVec_inj_mod_two_pow`) and
  constructive surjectivity (`terrasParityVec_surj_mod_two_pow`).
- Explicit `REF-002` barrier corollary `terras_every_vector_realized`: every length-`k` parity
  vector is realized by a full residue class mod `2^k`, and `n ≡ 2^k - 1 (mod 2^k)` gives an
  all-odd strictly rising trajectory over `k` compressed steps.
-/

@[expose] public section

namespace SolveCollatz

/-! ### 1. Compressed Collatz (Terras) Map and Parity Vectors -/

/-- One step of the compressed Collatz (Terras) map on `ℕ`:
`n / 2` if `n` is even, `(3 * n + 1) / 2` if `n` is odd. -/
def terrasStep (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- The `k`-th iterate of `terrasStep` starting from `n`. -/
def terrasIter : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => terrasIter k (terrasStep n)

/-- The length-`k` Terras parity vector recording `n % 2 = 1` at each step along the orbit. -/
def terrasParityVec : Nat → Nat → List Bool
  | 0, _ => []
  | k + 1, n => (n % 2 == 1) :: terrasParityVec k (terrasStep n)

/-- Number of `true` entries (odd steps) in a Boolean parity vector. -/
def countOnes : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + countOnes bs

/-- Unfolding rule for `terrasStep` on even inputs. -/
theorem terrasStep_even {n : Nat} (heven : n % 2 = 0) : terrasStep n = n / 2 := by
  rw [terrasStep, ite_eq_left heven]

/-- Unfolding rule for `terrasStep` on odd inputs. -/
theorem terrasStep_odd {n : Nat} (hodd : n % 2 = 1) : terrasStep n = (3 * n + 1) / 2 := by
  rw [terrasStep, ite_eq_right (by omega)]

/-- `terrasParityVec k n` has exact length `k`. -/
theorem terrasParityVec_length (k n : Nat) : (terrasParityVec k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [terrasParityVec, ih]

/-- `countOnes` of a parity vector never exceeds its length. -/
theorem countOnes_le_length (v : List Bool) : countOnes v ≤ v.length := by
  induction v with
  | nil => exact Nat.zero_le 0
  | cons b bs ih =>
    cases b <;> simp [countOnes] <;> omega

/-- `countOnes` is additive under list concatenation. -/
theorem countOnes_append (u v : List Bool) :
    countOnes (u ++ v) = countOnes u + countOnes v := by
  induction u with
  | nil => simp [countOnes]
  | cons b bs ih =>
    simp only [List.cons_append, countOnes, ih, Nat.add_assoc]

/-- Iterating `terrasStep` `k` times and then `m` times equals iterating `k + m` times. -/
theorem terrasIter_add (k m n : Nat) :
    terrasIter m (terrasIter k n) = terrasIter (k + m) n := by
  induction k generalizing n with
  | zero => simp [terrasIter]
  | succ k ih =>
    simp only [terrasIter, Nat.succ_add]
    exact ih (terrasStep n)

/-- Right-stepping identity: `terrasIter (k + 1) n = terrasStep (terrasIter k n)`. -/
theorem terrasIter_succ_right (k n : Nat) :
    terrasIter (k + 1) n = terrasStep (terrasIter k n) :=
  (terrasIter_add k 1 n).symm

/-- Concatenation law for `terrasParityVec` along split orbits. -/
theorem terrasParityVec_add (k m n : Nat) :
    terrasParityVec (k + m) n = terrasParityVec k n ++ terrasParityVec m (terrasIter k n) := by
  induction k generalizing n with
  | zero => simp [terrasParityVec, terrasIter]
  | succ k ih =>
    simp only [Nat.succ_add, terrasParityVec, terrasIter, List.cons_append]
    rw [ih (terrasStep n)]

/-- `terrasStep` preserves positivity (`0 < n → 0 < terrasStep n`). -/
theorem terrasStep_pos {n : Nat} (hn : 0 < n) : 0 < terrasStep n := by
  unfold terrasStep
  split <;> omega

/-- Every iterate of a positive integer under `terrasIter` remains positive. -/
theorem terrasIter_pos (k : Nat) {n : Nat} (hn : 0 < n) : 0 < terrasIter k n := by
  induction k generalizing n with
  | zero => exact hn
  | succ k ih => exact ih (terrasStep_pos hn)

/-! ### 2. Bridge to Frozen `Challenge.collatzIter` -/

/-- One compressed Terras step equals `1` standard Collatz step when `n` is even,
and `2` standard Collatz steps when `n` is odd. -/
theorem collatzIter_eq_terrasStep (n : Nat) :
    collatzIter (1 + (if (n % 2 == 1) then 1 else 0)) n = terrasStep n := by
  by_cases hodd : n % 2 = 1
  · have hbool : (n % 2 == 1) = true := beq_iff_eq.mpr hodd
    have hstep1 : collatzStep n = 3 * n + 1 := by
      rw [collatzStep, ite_eq_right (by omega)]
    have hstep2 : collatzStep (3 * n + 1) = (3 * n + 1) / 2 := by
      rw [collatzStep, ite_eq_left (by omega)]
    simp only [hbool, ↓reduceIte, terrasStep_odd hodd, collatzIter, hstep1, hstep2]
  · have heven : n % 2 = 0 := by omega
    have hbool : (n % 2 == 1) = false := by
      cases h : (n % 2 == 1)
      · rfl
      · exfalso; have := beq_iff_eq.mp h; omega
    simp only [hbool, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, terrasStep_even heven,
      collatzIter, collatzStep, ite_eq_left heven]

/-- **Orbit Bridge to `Challenge.lean`:** `k` compressed Terras steps equal
`k + countOnes (terrasParityVec k n)` standard Collatz steps. -/
theorem collatzIter_eq_terrasIter (k n : Nat) :
    collatzIter (k + countOnes (terrasParityVec k n)) n = terrasIter k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    let b := if (n % 2 == 1) then 1 else 0
    have hsplit :
        (k + 1) + countOnes (terrasParityVec (k + 1) n) =
          (1 + b) + (k + countOnes (terrasParityVec k (terrasStep n))) := by
      simp only [terrasParityVec, countOnes, b]
      omega
    calc collatzIter ((k + 1) + countOnes (terrasParityVec (k + 1) n)) n
        = collatzIter ((1 + b) + (k + countOnes (terrasParityVec k (terrasStep n)))) n := by
            rw [hsplit]
      _ = collatzIter (k + countOnes (terrasParityVec k (terrasStep n)))
            (collatzIter (1 + b) n) := (collatzIter_add (1 + b) _ n).symm
      _ = collatzIter (k + countOnes (terrasParityVec k (terrasStep n))) (terrasStep n) := by
            rw [collatzIter_eq_terrasStep n]
      _ = terrasIter k (terrasStep n) := ih (terrasStep n)
      _ = terrasIter (k + 1) n := rfl

/-! ### 3. Exact Congruence Law Modulo `2^k` -/

/-- One-step translation law for `terrasStep` when adding `2 ^ (k + 1) * q`:
even inputs shift by `2 ^ k * q`; odd inputs shift by `2 ^ k * (3 * q)`. -/
private theorem terrasStep_add_two_pow_succ (k n q : Nat) :
    (if n % 2 = 0 then
      terrasStep (n + 2 ^ (k + 1) * q) = terrasStep n + 2 ^ k * q
    else
      terrasStep (n + 2 ^ (k + 1) * q) = terrasStep n + 2 ^ k * (3 * q)) ∧
    (n + 2 ^ (k + 1) * q) % 2 = n % 2 := by
  have hmul : 2 ^ (k + 1) * q = 2 * (2 ^ k * q) := by
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]
  have hmod : (n + 2 ^ (k + 1) * q) % 2 = n % 2 := by
    rw [hmul, Nat.add_mul_mod_self_left]
  refine ⟨?_, hmod⟩
  by_cases heven : n % 2 = 0
  · rw [ite_eq_left heven, terrasStep_even (by rw [hmod, heven]), terrasStep_even heven, hmul]
    exact Nat.add_mul_div_left n (2 ^ k * q) (by decide)
  · have hodd : n % 2 = 1 := by omega
    rw [ite_eq_right heven, terrasStep_odd (by rw [hmod, hodd]), terrasStep_odd hodd]
    have hnum : 3 * (n + 2 ^ (k + 1) * q) + 1 = (3 * n + 1) + 2 * (2 ^ k * (3 * q)) := by
      calc 3 * (n + 2 ^ (k + 1) * q) + 1
          = 3 * (n + 2 * (2 ^ k * q)) + 1 := by rw [hmul]
        _ = 3 * n + 2 * (3 * (2 ^ k * q)) + 1 := by
            rw [Nat.mul_add, Nat.mul_left_comm 3 2]
        _ = (3 * n + 1) + 2 * (2 ^ k * (3 * q)) := by
            rw [Nat.mul_left_comm 3 (2 ^ k), Nat.add_right_comm]
    rw [hnum]
    exact Nat.add_mul_div_left (3 * n + 1) (2 ^ k * (3 * q)) (by decide)

/-- **Exact Accelerated Congruence Law (`Terras 1976`):** shifting `n` by any multiple of `2^k`
preserves the length-`k` parity vector identically and shifts the `k`-th Terras iterate by
`3 ^ countOnes (terrasParityVec k n) * q`. -/
theorem terrasParityVec_mod_two_pow (k n q : Nat) :
    terrasParityVec k (n + 2 ^ k * q) = terrasParityVec k n ∧
      terrasIter k (n + 2 ^ k * q) =
        terrasIter k n + 3 ^ countOnes (terrasParityVec k n) * q := by
  induction k generalizing n q with
  | zero => simp [terrasParityVec, terrasIter, countOnes]
  | succ k ih =>
    have hstep := terrasStep_add_two_pow_succ k n q
    have hmod := hstep.2
    have hhead : ((n + 2 ^ (k + 1) * q) % 2 == 1) = (n % 2 == 1) := by rw [hmod]
    by_cases heven : n % 2 = 0
    · have hst : terrasStep (n + 2 ^ (k + 1) * q) = terrasStep n + 2 ^ k * q := by
        simpa [heven] using hstep.1
      have hih := ih (terrasStep n) q
      have hbool : (n % 2 == 1) = false := by
        cases h : (n % 2 == 1)
        · rfl
        · exfalso; have := beq_iff_eq.mp h; omega
      refine ⟨?_, ?_⟩
      · simp only [terrasParityVec, hhead, hst, hih.1]
      · simp only [terrasIter, hst, hih.2, terrasParityVec, countOnes, hbool, Bool.false_eq_true,
          ↓reduceIte, Nat.zero_add]
    · have hst : terrasStep (n + 2 ^ (k + 1) * q) = terrasStep n + 2 ^ k * (3 * q) := by
        simpa [heven] using hstep.1
      have hih := ih (terrasStep n) (3 * q)
      have hodd : n % 2 = 1 := by omega
      have hbool : (n % 2 == 1) = true := beq_iff_eq.mpr hodd
      refine ⟨?_, ?_⟩
      · simp only [terrasParityVec, hhead, hst, hih.1]
      · simp only [terrasIter, hst, hih.2, terrasParityVec, countOnes, hbool, ↓reduceIte]
        rw [Nat.add_comm 1 _, Nat.pow_succ, Nat.mul_assoc]

/-- The length-`k` Terras parity vector depends only on `n % 2^k`. -/
theorem terrasParityVec_mod_eq (k n : Nat) :
    terrasParityVec k (n % 2 ^ k) = terrasParityVec k n := by
  have h := (terrasParityVec_mod_two_pow k (n % 2 ^ k) (n / 2 ^ k)).1
  rw [Nat.mod_add_div] at h
  exact h.symm

/-- Exact quotient-remainder expansion of `terrasIter k n` modulo `2^k`. -/
theorem terrasIter_mod_eq (k n : Nat) :
    terrasIter k n =
      terrasIter k (n % 2 ^ k) + 3 ^ countOnes (terrasParityVec k n) * (n / 2 ^ k) := by
  have h := (terrasParityVec_mod_two_pow k (n % 2 ^ k) (n / 2 ^ k)).2
  rw [Nat.mod_add_div, terrasParityVec_mod_eq] at h
  exact h

/-! ### 4. Terras's Fundamental Bijection Modulo `2^k` -/

/-- Reduction rule `u % m = u - m` when `m ≤ u < 2 * m`. -/
private theorem mod_eq_sub_of_lt2 {u m : Nat} (hle : m ≤ u) (hlt : u < 2 * m) :
    u % m = u - m := by
  rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt (by omega)]

/-- Additive cancellation modulo `m > 0` on `ℕ`. -/
private theorem add_const_mod_eq {x y c m : Nat} (hm : 0 < m)
    (h : (x + c) % m = (y + c) % m) : x % m = y % m := by
  have h1 : (x % m + c % m) % m = (y % m + c % m) % m := by
    rw [← Nat.add_mod, ← Nat.add_mod, h]
  have hx : x % m < m := Nat.mod_lt x hm
  have hy : y % m < m := Nat.mod_lt y hm
  have hc : c % m < m := Nat.mod_lt c hm
  by_cases hxm : x % m + c % m < m <;> by_cases hym : y % m + c % m < m
  · rw [Nat.mod_eq_of_lt hxm, Nat.mod_eq_of_lt hym] at h1; omega
  · rw [Nat.mod_eq_of_lt hxm,
      mod_eq_sub_of_lt2 (by omega : m ≤ y % m + c % m) (by omega)] at h1
    omega
  · rw [mod_eq_sub_of_lt2 (by omega : m ≤ x % m + c % m) (by omega),
      Nat.mod_eq_of_lt hym] at h1
    omega
  · rw [mod_eq_sub_of_lt2 (by omega : m ≤ x % m + c % m) (by omega),
      mod_eq_sub_of_lt2 (by omega : m ≤ y % m + c % m) (by omega)] at h1
    omega

/-- Halving commutes with modulo `m` via `(x / 2) % m = (x % (2 * m)) / 2` for `m > 0`. -/
private theorem div_two_mod_eq {x m : Nat} (hm : 0 < m) :
    (x / 2) % m = (x % (2 * m)) / 2 := by
  have hdecomp : x = x % (2 * m) + 2 * (m * (x / (2 * m))) := by
    rw [← Nat.mul_assoc]
    exact (Nat.mod_add_div x (2 * m)).symm
  have hdiv : x / 2 = (x % (2 * m)) / 2 + m * (x / (2 * m)) := by
    conv => lhs; rw [hdecomp]
    exact Nat.add_mul_div_left (x % (2 * m)) (m * (x / (2 * m))) (by decide)
  have hlt : (x % (2 * m)) / 2 < m := by
    have hr : x % (2 * m) < 2 * m := Nat.mod_lt x (by omega)
    omega
  rw [hdiv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- Multiplication by `3` is injective modulo `2^m`. -/
private theorem three_mul_mod_two_pow_inj (m a b : Nat) (ha : a < 2 ^ m) (hb : b < 2 ^ m)
    (h : (3 * a) % 2 ^ m = (3 * b) % 2 ^ m) : a = b := by
  induction m generalizing a b with
  | zero =>
    have hpow : 2 ^ 0 = 1 := rfl
    omega
  | succ m ih =>
    have hmpos : 0 < 2 ^ m := Nat.two_pow_pos m
    have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow] at ha hb h
    have hmod2 : (3 * a) % 2 = (3 * b) % 2 := by
      have hdvd : 2 ∣ 2 * 2 ^ m := ⟨2 ^ m, rfl⟩
      rw [← Nat.mod_mod_of_dvd (3 * a) hdvd, ← Nat.mod_mod_of_dvd (3 * b) hdvd, h]
    have hdiv : ((3 * a) / 2) % 2 ^ m = ((3 * b) / 2) % 2 ^ m := by
      rw [div_two_mod_eq hmpos, div_two_mod_eq hmpos, h]
    have hpar : a % 2 = b % 2 := by omega
    by_cases heven : a % 2 = 0
    · have ha3 : (3 * a) / 2 = 3 * (a / 2) := by omega
      have hb3 : (3 * b) / 2 = 3 * (b / 2) := by omega
      rw [ha3, hb3] at hdiv
      have hhalf := ih (a / 2) (b / 2) (by omega) (by omega) hdiv
      omega
    · have ha3 : (3 * a) / 2 = 3 * (a / 2) + 1 := by omega
      have hb3 : (3 * b) / 2 = 3 * (b / 2) + 1 := by omega
      rw [ha3, hb3] at hdiv
      have hmul := add_const_mod_eq hmpos hdiv
      have hhalf := ih (a / 2) (b / 2) (by omega) (by omega) hmul
      omega

/-- Parity extraction from equality of Boolean `(_ % 2 == 1)` indicators. -/
private theorem mod_two_eq_of_beq_eq {a b : Nat}
    (h : (a % 2 == 1) = (b % 2 == 1)) : a % 2 = b % 2 := by
  by_cases ha1 : a % 2 = 1
  · have : (b % 2 == 1) = true := by rw [← h]; exact beq_iff_eq.mpr ha1
    have hb1 := beq_iff_eq.mp this
    omega
  · have hb_ne : b % 2 ≠ 1 := by
      intro hb1
      have : (a % 2 == 1) = true := by rw [h]; exact beq_iff_eq.mpr hb1
      have := beq_iff_eq.mp this
      omega
    omega

/-- **Terras Bijection — Injectivity mod `2^k`:** distinct residues in `[0, 2^k)` produce
distinct length-`k` Terras parity vectors. -/
theorem terrasParityVec_inj_mod_two_pow {k a b : Nat}
    (ha : a < 2 ^ k) (hb : b < 2 ^ k)
    (hvec : terrasParityVec k a = terrasParityVec k b) : a = b := by
  induction k generalizing a b with
  | zero =>
    have hpow : 2 ^ 0 = 1 := rfl
    omega
  | succ k ih =>
    have hkpos : 0 < 2 ^ k := Nat.two_pow_pos k
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow] at ha hb
    simp only [terrasParityVec, List.cons.injEq] at hvec
    have hpar : a % 2 = b % 2 := mod_two_eq_of_beq_eq hvec.1
    have htail : terrasParityVec k (terrasStep a % 2 ^ k) =
        terrasParityVec k (terrasStep b % 2 ^ k) := by
      rw [terrasParityVec_mod_eq, terrasParityVec_mod_eq, hvec.2]
    have hstep_mod := ih (Nat.mod_lt _ hkpos) (Nat.mod_lt _ hkpos) htail
    by_cases heven : a % 2 = 0
    · rw [terrasStep_even heven, terrasStep_even (by omega)] at hstep_mod
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hstep_mod
      omega
    · have haodd : a % 2 = 1 := by omega
      have hbodd : b % 2 = 1 := by omega
      rw [terrasStep_odd haodd, terrasStep_odd hbodd] at hstep_mod
      have ha3 : (3 * a + 1) / 2 = 3 * (a / 2) + 2 := by omega
      have hb3 : (3 * b + 1) / 2 = 3 * (b / 2) + 2 := by omega
      rw [ha3, hb3] at hstep_mod
      have hmul := add_const_mod_eq hkpos hstep_mod
      have hhalf := three_mul_mod_two_pow_inj k (a / 2) (b / 2) (by omega) (by omega) hmul
      omega

/-- Constructive Hensel-lifted inverse of multiplication by `3` modulo `2^k`:
returns `x < 2^k` satisfying `(3 * x) % 2^k = y % 2^k`. -/
def inv3ModTwoPow : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, y =>
    let x₀ := inv3ModTwoPow k y
    if (3 * x₀) % 2 ^ (k + 1) = y % 2 ^ (k + 1) then x₀ else x₀ + 2 ^ k

/-- Binary splitting modulo `2 * m`: `a % (2 * m)` equals either `a % m` or `a % m + m`. -/
private theorem mod_two_mul_cases (a m : Nat) (hm : 0 < m) :
    a % (2 * m) = a % m ∨ a % (2 * m) = a % m + m := by
  let q := (a / m) / 2
  have hd : a = a % m + m * (a / m) := (Nat.mod_add_div a m).symm
  have hd2 : a / m = (a / m) % 2 + 2 * q := (Nat.mod_add_div (a / m) 2).symm
  have ha_lt : a % m < m := Nat.mod_lt a hm
  rcases (by omega : (a / m) % 2 = 0 ∨ (a / m) % 2 = 1) with h0 | h1m
  · left
    have hdiv : a / m = 2 * q := by rw [hd2, h0, Nat.zero_add]
    have heq : a = a % m + (2 * m) * q := by
      conv => lhs; rw [hd, hdiv, Nat.mul_left_comm m 2, ← Nat.mul_assoc]
    conv => lhs; rw [heq]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  · right
    have hdiv : a / m = 1 + 2 * q := by rw [hd2, h1m]
    have heq : a = (a % m + m) + (2 * m) * q := by
      conv =>
        lhs
        rw [hd, hdiv, Nat.mul_add, Nat.mul_one, Nat.mul_left_comm m 2,
          ← Nat.mul_assoc, ← Nat.add_assoc]
    conv => lhs; rw [heq]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- Lifting helper for doubling the modulus from `m` to `2 * m`:
if `a % m = b % m` and `a % (2 * m) ≠ b % (2 * m)`, then `(a + m) % (2 * m) = b % (2 * m)`. -/
private theorem add_half_mod_two_mul {a b m : Nat} (hm : 0 < m)
    (h1 : a % m = b % m) (h2 : a % (2 * m) ≠ b % (2 * m)) :
    (a + m) % (2 * m) = b % (2 * m) := by
  have hsum : (a + m) % (2 * m) = (a % (2 * m) + m) % (2 * m) := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : m < 2 * m)]
  rw [hsum]
  rcases mod_two_mul_cases a m hm with ha0 | ha1 <;>
    rcases mod_two_mul_cases b m hm with hb0 | hb1
  · exact absurd (by omega) h2
  · rw [ha0, hb1, ← h1, Nat.mod_eq_of_lt (by have := Nat.mod_lt a hm; omega)]
  · rw [ha1, hb0, ← h1]
    have hlt : a % m < m := Nat.mod_lt a hm
    have heq : a % m + m + m = a % m + (2 * m) * 1 := by omega
    rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  · exact absurd (by omega) h2

/-- Correctness of `inv3ModTwoPow`: `inv3ModTwoPow k y < 2^k` and
`(3 * inv3ModTwoPow k y) % 2^k = y % 2^k`. -/
theorem inv3ModTwoPow_spec (k y : Nat) :
    inv3ModTwoPow k y < 2 ^ k ∧ (3 * inv3ModTwoPow k y) % 2 ^ k = y % 2 ^ k := by
  induction k with
  | zero => simp [inv3ModTwoPow, Nat.mod_one]
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hkpos : 0 < 2 ^ k := Nat.two_pow_pos k
    simp only [inv3ModTwoPow]
    by_cases hmatch : (3 * inv3ModTwoPow k y) % 2 ^ (k + 1) = y % 2 ^ (k + 1)
    · rw [ite_eq_left hmatch]
      exact ⟨Nat.lt_of_lt_of_le ih.1 (by rw [hpow]; omega), hmatch⟩
    · rw [ite_eq_right hmatch]
      refine ⟨by rw [hpow]; omega, ?_⟩
      have hmul3 : 3 * (inv3ModTwoPow k y + 2 ^ k) =
          (3 * inv3ModTwoPow k y + 2 ^ k) + 2 ^ (k + 1) * 1 := by
        rw [hpow]; omega
      rw [hmul3, Nat.add_mul_mod_self_left, hpow]
      rw [hpow] at hmatch
      exact add_half_mod_two_mul hkpos ih.2 hmatch

/-- Constructive residue witness `r < 2 ^ v.length` realizing parity vector `v`. -/
def terrasVecWitness : List Bool → Nat
  | [] => 0
  | b :: bs =>
    let r' := terrasVecWitness bs
    if b then
      2 * inv3ModTwoPow bs.length (r' + (2 ^ bs.length - 2)) + 1
    else
      2 * r'

/-- Odd-head step verification for `terrasVecWitness`. -/
private theorem terrasVecWitness_true_step {k r' : Nat} (hr' : r' < 2 ^ k) :
    let x := inv3ModTwoPow k (r' + (2 ^ k - 2))
    2 * x + 1 < 2 ^ (k + 1) ∧ terrasStep (2 * x + 1) % 2 ^ k = r' := by
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
  have hinv := inv3ModTwoPow_spec k (r' + (2 ^ k - 2))
  let x := inv3ModTwoPow k (r' + (2 ^ k - 2))
  have hlt : 2 * x + 1 < 2 ^ (k + 1) := by rw [hpow]; omega
  have hodd : (2 * x + 1) % 2 = 1 := by omega
  have hstep : terrasStep (2 * x + 1) = 3 * x + 2 := by
    rw [terrasStep_odd hodd]; omega
  refine ⟨hlt, ?_⟩
  rw [hstep, Nat.add_mod, hinv.2, ← Nat.add_mod]
  cases k with
  | zero =>
    have h0 : r' = 0 := by simp at hr'; exact hr'
    simp [h0]
  | succ m =>
    have hge2 : 2 ≤ 2 ^ (m + 1) := by
      have : 0 < 2 ^ m := Nat.two_pow_pos m
      rw [Nat.pow_succ]; omega
    have heq : r' + (2 ^ (m + 1) - 2) + 2 = r' + 2 ^ (m + 1) * 1 := by omega
    rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr']

/-- Correctness of `terrasVecWitness`: `terrasVecWitness v < 2 ^ v.length` and
`terrasParityVec v.length (terrasVecWitness v) = v`. -/
theorem terrasVecWitness_spec (v : List Bool) :
    terrasVecWitness v < 2 ^ v.length ∧
      terrasParityVec v.length (terrasVecWitness v) = v := by
  induction v with
  | nil => simp [terrasVecWitness, terrasParityVec]
  | cons b bs ih =>
    have hpow : 2 ^ (bs.length + 1) = 2 * 2 ^ bs.length := by rw [Nat.pow_succ, Nat.mul_comm]
    cases b
    · simp only [terrasVecWitness, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      have hlt : 2 * terrasVecWitness bs < 2 ^ (bs.length + 1) := by rw [hpow]; omega
      have heven : (2 * terrasVecWitness bs) % 2 = 0 := by omega
      have hbool : ((2 * terrasVecWitness bs) % 2 == 1) = false := by
        cases h : ((2 * terrasVecWitness bs) % 2 == 1)
        · rfl
        · exfalso; have := beq_iff_eq.mp h; omega
      have hstep : terrasStep (2 * terrasVecWitness bs) = terrasVecWitness bs := by
        rw [terrasStep_even heven]; omega
      refine ⟨hlt, ?_⟩
      simp only [terrasParityVec, hbool, hstep, ih.2]
    · simp only [terrasVecWitness, ↓reduceIte, List.length_cons]
      have hst := terrasVecWitness_true_step ih.1
      have hodd : (2 * inv3ModTwoPow bs.length (terrasVecWitness bs + (2 ^ bs.length - 2)) + 1) % 2
          = 1 := by omega
      have hbool : ((2 * inv3ModTwoPow bs.length
          (terrasVecWitness bs + (2 ^ bs.length - 2)) + 1) % 2 == 1) = true :=
        beq_iff_eq.mpr hodd
      refine ⟨hst.1, ?_⟩
      simp only [terrasParityVec, hbool]
      rw [← terrasParityVec_mod_eq bs.length _, hst.2, ih.2]

/-- **Terras Fundamental Bijection — Surjectivity & Uniqueness mod `2^k` (`Terras 1976`):**
for every length-`k` Boolean parity vector `v`, there exists a unique residue `r < 2^k`
such that `terrasParityVec k r = v`. -/
theorem terrasParityVec_surj_mod_two_pow (k : Nat) (v : List Bool) (hv : v.length = k) :
    ∃ r : Nat, r < 2 ^ k ∧ terrasParityVec k r = v ∧
      ∀ r' : Nat, r' < 2 ^ k → terrasParityVec k r' = v → r' = r := by
  subst hv
  refine ⟨terrasVecWitness v, (terrasVecWitness_spec v).1, (terrasVecWitness_spec v).2, ?_⟩
  intro r' hr' hvec'
  exact terrasParityVec_inj_mod_two_pow hr' (terrasVecWitness_spec v).1
    (hvec'.trans (terrasVecWitness_spec v).2.symm)

/-! ### 5. Explicit `REF-002` Barrier: All-Odd Rising Trajectory mod `2^k` -/

/-- Exact parity vector of `2^k - 1`: all `k` compressed steps are odd (`true`). -/
theorem terrasParityVec_two_pow_sub_one (k : Nat) :
    terrasParityVec k (2 ^ k - 1) = List.replicate k true := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hkpos : 0 < 2 ^ k := Nat.two_pow_pos k
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hodd : (2 ^ (k + 1) - 1) % 2 = 1 := by omega
    have hbool : ((2 ^ (k + 1) - 1) % 2 == 1) = true := beq_iff_eq.mpr hodd
    have hstep : terrasStep (2 ^ (k + 1) - 1) = (2 ^ k - 1) + 2 ^ k * 2 := by
      rw [terrasStep_odd hodd, hpow]; omega
    simp only [terrasParityVec, hbool, hstep, (terrasParityVec_mod_two_pow k (2 ^ k - 1) 2).1,
      ih, List.replicate_succ]

/-- `countOnes (List.replicate k true) = k`. -/
private theorem countOnes_replicate_true (k : Nat) :
    countOnes (List.replicate k true) = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, countOnes, ih]; omega

/-- Exact `k`-th compressed iterate of `2^k - 1`: `terrasIter k (2^k - 1) = 3^k - 1`. -/
theorem terrasIter_two_pow_sub_one (k : Nat) :
    terrasIter k (2 ^ k - 1) = 3 ^ k - 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hkpos : 0 < 2 ^ k := Nat.two_pow_pos k
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hodd : (2 ^ (k + 1) - 1) % 2 = 1 := by omega
    have hstep : terrasStep (2 ^ (k + 1) - 1) = (2 ^ k - 1) + 2 ^ k * 2 := by
      rw [terrasStep_odd hodd, hpow]; omega
    have hcong := (terrasParityVec_mod_two_pow k (2 ^ k - 1) 2).2
    rw [terrasParityVec_two_pow_sub_one, countOnes_replicate_true, ih] at hcong
    have h3pos : 0 < 3 ^ k := Nat.pow_pos (by decide)
    have h3pow : 3 ^ (k + 1) = 3 ^ k * 3 := Nat.pow_succ 3 k
    calc terrasIter (k + 1) (2 ^ (k + 1) - 1)
        = terrasIter k (terrasStep (2 ^ (k + 1) - 1)) := rfl
      _ = terrasIter k ((2 ^ k - 1) + 2 ^ k * 2) := by rw [hstep]
      _ = (3 ^ k - 1) + 3 ^ k * 2 := hcong
      _ = 3 ^ (k + 1) - 1 := by rw [h3pow]; omega

/-- Strict exponential inequality `2 ^ j < 3 ^ j` for all `1 ≤ j`. -/
private theorem two_pow_lt_three_pow {j : Nat} (hj : 1 ≤ j) : 2 ^ j < 3 ^ j := by
  induction j with
  | zero => omega
  | succ j ih =>
    cases j with
    | zero => decide
    | succ j =>
      have hih := ih (by omega)
      have h2 : 0 < 2 ^ (j + 1) := Nat.two_pow_pos (j + 1)
      rw [Nat.pow_succ 2, Nat.pow_succ 3]
      omega

/-- Every `n ≡ 2^k - 1 (mod 2^k)` (`k ≥ 1`) satisfies `n % 2^j = 2^j - 1` for all `1 ≤ j ≤ k`. -/
private theorem mod_two_pow_sub_one_le {k j n : Nat} (hjk : j ≤ k)
    (hmod : n % 2 ^ k = 2 ^ k - 1) : n % 2 ^ j = 2 ^ j - 1 := by
  have hkpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hjpos : 0 < 2 ^ j := Nat.two_pow_pos j
  have hdecomp : n = (2 ^ k - 1) + 2 ^ k * (n / 2 ^ k) := by
    have h := (Nat.mod_add_div n (2 ^ k)).symm
    rw [hmod] at h
    exact h
  have hpowk : 2 ^ k = 2 ^ j * 2 ^ (k - j) := by
    conv => lhs; rw [(Nat.add_sub_of_le hjk).symm, Nat.pow_add]
  have h2kj : 0 < 2 ^ (k - j) := Nat.two_pow_pos (k - j)
  have hm_pos : 0 < 2 ^ (k - j) * (n / 2 ^ k + 1) := Nat.mul_pos h2kj (Nat.succ_pos _)
  have hmul : 2 ^ j ≤ 2 ^ j * (2 ^ (k - j) * (n / 2 ^ k + 1)) :=
    Nat.le_mul_of_pos_right _ hm_pos
  have hq : n = (2 ^ j - 1) + 2 ^ j * (2 ^ (k - j) * (n / 2 ^ k + 1) - 1) := by
    calc n = 2 ^ k * (n / 2 ^ k + 1) - 1 := by
            conv => lhs; rw [hdecomp]
            rw [Nat.mul_add, Nat.mul_one]; omega
      _ = 2 ^ j * (2 ^ (k - j) * (n / 2 ^ k + 1)) - 1 := by rw [hpowk, Nat.mul_assoc]
      _ = (2 ^ j - 1) + (2 ^ j * (2 ^ (k - j) * (n / 2 ^ k + 1)) - 2 ^ j) := by omega
      _ = (2 ^ j - 1) + 2 ^ j * (2 ^ (k - j) * (n / 2 ^ k + 1) - 1) := by
            rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  conv => lhs; rw [hq]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- Exact closed form and strict growth `n < terrasIter k n` whenever `n % 2^k = 2^k - 1`
and `1 ≤ k`. -/
private theorem terras_all_odd_step {k n : Nat} (hk : 1 ≤ k) (hmod : n % 2 ^ k = 2 ^ k - 1) :
    terrasParityVec k n = List.replicate k true ∧
      terrasIter k n = 3 ^ k * (n / 2 ^ k + 1) - 1 ∧ n < terrasIter k n := by
  have hkpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have h3pos : 0 < 3 ^ k := Nat.pow_pos (by decide)
  have hdecomp : n = (2 ^ k - 1) + 2 ^ k * (n / 2 ^ k) := by
    have h := (Nat.mod_add_div n (2 ^ k)).symm
    rw [hmod] at h
    exact h
  have hcong := terrasParityVec_mod_two_pow k (2 ^ k - 1) (n / 2 ^ k)
  rw [← hdecomp, terrasParityVec_two_pow_sub_one, countOnes_replicate_true,
    terrasIter_two_pow_sub_one] at hcong
  have hval : terrasIter k n = 3 ^ k * (n / 2 ^ k + 1) - 1 := by
    rw [hcong.2, Nat.mul_add, Nat.mul_one]; omega
  have hlt23 : 2 ^ k < 3 ^ k := two_pow_lt_three_pow hk
  have hmul_lt : 2 ^ k * (n / 2 ^ k + 1) < 3 ^ k * (n / 2 ^ k + 1) :=
    Nat.mul_lt_mul_of_pos_right hlt23 (Nat.succ_pos _)
  have hn_eq : n = 2 ^ k * (n / 2 ^ k + 1) - 1 := by
    conv => lhs; rw [hdecomp]
    rw [Nat.mul_add, Nat.mul_one]; omega
  have hle2 : 1 ≤ 2 ^ k * (n / 2 ^ k + 1) := Nat.mul_pos hkpos (Nat.succ_pos _)
  refine ⟨hcong.1, hval, by omega⟩

/-- Every `n ≡ 2^k - 1 (mod 2^k)` (`k ≥ 1`) executes `k` consecutive odd compressed steps,
reaching `3^k * (n / 2^k + 1) - 1` and strictly exceeding `n` at every step `1 ≤ j ≤ k`. -/
theorem terras_all_odd_rising {k n : Nat} (hk : 1 ≤ k) (hmod : n % 2 ^ k = 2 ^ k - 1) :
    terrasParityVec k n = List.replicate k true ∧
      terrasIter k n = 3 ^ k * (n / 2 ^ k + 1) - 1 ∧
      ∀ j : Nat, 1 ≤ j → j ≤ k → n < terrasIter j n := by
  have hk_res := terras_all_odd_step hk hmod
  refine ⟨hk_res.1, hk_res.2.1, fun j hj1 hjk => ?_⟩
  exact (terras_all_odd_step hj1 (mod_two_pow_sub_one_le hjk hmod)).2.2

/-- **Corollary (`REF-002` Modular Covering Barrier):**
1. Every length-`k` Boolean parity vector `v` is realized by an entire residue class
   `r + 2^k * q` (`r < 2^k`).
2. In particular, for any modulus `2^k` (`k ≥ 1`), the class `n ≡ 2^k - 1 (mod 2^k)` executes
   `k` consecutive odd steps, reaching `3^k * (n / 2^k + 1) - 1` and never dropping below `n`
   within steps `1 ≤ j ≤ k`. -/
theorem terras_every_vector_realized (k : Nat) :
    (∀ v : List Bool, v.length = k →
      ∃ r : Nat, r < 2 ^ k ∧ ∀ q : Nat, terrasParityVec k (r + 2 ^ k * q) = v) ∧
    (1 ≤ k → ∀ n : Nat, n % 2 ^ k = 2 ^ k - 1 →
      terrasParityVec k n = List.replicate k true ∧
        terrasIter k n = 3 ^ k * (n / 2 ^ k + 1) - 1 ∧
        ∀ j : Nat, 1 ≤ j → j ≤ k → n < terrasIter j n) := by
  refine ⟨fun v hv => ?_, fun hk n hmod => terras_all_odd_rising hk hmod⟩
  rcases terrasParityVec_surj_mod_two_pow k v hv with ⟨r, hr, hvec, _⟩
  exact ⟨r, hr, fun q => (terrasParityVec_mod_two_pow k r q).1.trans hvec⟩

end SolveCollatz
