/-
Copyright (c) 2026 The solve-collatz contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Collatz.Core.Syracuse
public import Collatz.Core.GeneralMaps

/-!
# `2`-adic Localization `ℤ_(2) ⊂ ℤ₂`, Syracuse Extension & Barrier 4 Witnesses (`CORE-004`)

Shared core infrastructure for Barrier 4 (`frontier/BARRIERS.md` and `review/barrier-check.md`):
- Odd-denominator rational type `OddDenomRat` representing `ℤ_(2) = { a / b ∈ ℚ : b odd } ⊂ ℤ₂`,
  with exact arithmetic (`add`, `mul`, `step3n1`, `divTwoPow`) and equivalence `OddDenomRat.Equiv`.
- Signed `2`-adic factorization (`valuation2Int`, `oddPartInt`) and well-defined extensions of
  the Syracuse map (`OddDenomRat.syracuseStep`, `OddDenomRat.syracuseVal`) and unaccelerated
  Collatz map (`OddDenomRat.collatzStep`) to `ℤ_(2)`, bridging to `Challenge.lean`,
  `Collatz/Core/GeneralMaps.lean`, and `Collatz/Core/Syracuse.lean`.
- Denominator `periodicPointDen v = 2 ^ paritySum v - 3 ^ v.length` proved always odd (hence
  invertible in `ℤ_(2) ⊂ ℤ₂` and nonzero) whenever `0 < paritySum v`.
- **Universal `2`-adic Periodic Point Theorem:** every valid parity vector `v` determines a
  unique `x = parityOffset v / (2 ^ S - 3 ^ k) ∈ ℤ_(2)` solving `2 ^ S * x = 3 ^ k * x + C(v)`
  that is genuinely periodic under both `syracuseIter` and `collatzIter` with halving vector `v`.
- Concrete **Barrier 4 witnesses:** `twoAdic_cycle_neg5` (`-5 / 1`),
  `twoAdic_cycle_neg19_over_11` (`-19 / 11`), and `twoAdic_cycle_211_over_13` (`211 / 13`).
-/

@[expose] public section

namespace SolveCollatz

/-- An odd-denominator rational `num / den` in the `2`-adic localization `ℤ_(2) ⊂ ℤ₂`.
Because `den % 2 = 1`, `0 < den` holds automatically and `den` is a `2`-adic unit. -/
structure OddDenomRat where
  /-- Integer numerator. -/
  num : Int
  /-- Odd positive denominator (`den % 2 = 1`). -/
  den : Nat
  /-- Proof that `den` is odd (hence positive and invertible in `ℤ₂`). -/
  den_odd : den % 2 = 1
deriving DecidableEq, Repr

/-! ### 1. Signed `2`-adic Factorization on `ℤ` -/

private theorem natCast_two : ((2 : Nat) : Int) = 2 := rfl
private theorem natCast_three : ((3 : Nat) : Int) = 3 := rfl

/-- Exact `2`-adic valuation `v₂(z)` on `ℤ` (with `valuation2Int 0 = 0`). -/
def valuation2Int (z : Int) : Nat := valuation2 z.natAbs

/-- Signed odd part of `z : Int`, stripping all factors of `2` while preserving sign. -/
def oddPartInt (z : Int) : Int :=
  if z < 0 then -(oddPart z.natAbs : Int) else (oddPart z.natAbs : Int)

/-- `((2 : Int) ^ e).natAbs = 2 ^ e`. -/
theorem int_two_pow_natAbs (e : Nat) : ((2 : Int) ^ e).natAbs = 2 ^ e := by
  induction e with
  | zero => rfl
  | succ e ih => rw [Int.pow_succ, Int.natAbs_mul, ih, Nat.pow_succ]; rfl

/-- Every power of `2` in `ℤ` is nonzero. -/
theorem int_two_pow_ne_zero (e : Nat) : (2 : Int) ^ e ≠ 0 := by
  induction e with
  | zero => decide
  | succ e ih => rw [Int.pow_succ]; omega

/-- Every power of `3` in `ℤ` is odd (`(3 : Int) ^ k % 2 = 1`). -/
theorem int_three_pow_mod_two (k : Nat) : (3 : Int) ^ k % 2 = 1 := by
  induction k with
  | zero => decide
  | succ k ih => rw [Int.pow_succ]; omega

/-- Every positive power of `2` in `ℤ` is even (`(2 : Int) ^ s % 2 = 0` for `0 < s`). -/
theorem int_two_pow_mod_two {s : Nat} (hs : 0 < s) : (2 : Int) ^ s % 2 = 0 := by
  cases s with
  | zero => exact absurd hs (Nat.lt_irrefl 0)
  | succ s => rw [Int.pow_succ]; omega

/-- Multiplying a natural number by an odd factor preserves `valuation2`. -/
theorem valuation2_mul_odd (n : Nat) {d : Nat} (hd : d % 2 = 1) :
    valuation2 (n * d) = valuation2 n := by
  by_cases hn : n = 0
  · subst hn; rw [Nat.zero_mul]
  · have hodd : (oddPart n * d) % 2 = 1 := by
      rw [Nat.mul_mod, oddPart_odd (Nat.pos_of_ne_zero hn), hd]
    calc valuation2 (n * d)
        = valuation2 ((oddPart n * 2 ^ valuation2 n) * d) := by rw [oddPart_mul_two_pow n]
      _ = valuation2 ((oddPart n * d) * 2 ^ valuation2 n) := by rw [Nat.mul_right_comm]
      _ = valuation2 n := valuation2_mul_two_pow hodd (valuation2 n)

/-- Every integer factors as `oddPartInt z * (2 : Int) ^ valuation2Int z = z`. -/
theorem oddPartInt_mul_two_pow (z : Int) :
    oddPartInt z * (2 : Int) ^ valuation2Int z = z := by
  have hnat : ((oddPart z.natAbs * 2 ^ valuation2 z.natAbs : Nat) : Int) = (z.natAbs : Int) := by
    rw [oddPart_mul_two_pow]
  rw [Int.natCast_mul, Int.natCast_pow, natCast_two] at hnat
  unfold oddPartInt valuation2Int
  by_cases hz : z < 0
  · rw [ite_eq_left hz, Int.neg_mul, hnat]; omega
  · rw [ite_eq_right hz, hnat]; omega

/-- The signed odd part of any nonzero integer is odd (`oddPartInt z % 2 = 1`). -/
theorem oddPartInt_odd {z : Int} (hz : z ≠ 0) : oddPartInt z % 2 = 1 := by
  have hodd : oddPart z.natAbs % 2 = 1 := oddPart_odd (by omega)
  unfold oddPartInt
  by_cases hneg : z < 0
  · rw [ite_eq_left hneg]; omega
  · rw [ite_eq_right hneg]; omega

/-- Multiplying an integer by an odd natural number preserves `valuation2Int`. -/
theorem valuation2Int_mul_odd (z : Int) {d : Nat} (hd : d % 2 = 1) :
    valuation2Int (z * (d : Int)) = valuation2Int z := by
  unfold valuation2Int
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  exact valuation2_mul_odd z.natAbs hd

/-- Uniqueness of `valuation2Int` on products `m * 2 ^ e` with `m` odd. -/
theorem valuation2Int_mul_two_pow {m : Int} (hm : m % 2 ≠ 0) (e : Nat) :
    valuation2Int (m * (2 : Int) ^ e) = e := by
  unfold valuation2Int
  rw [Int.natAbs_mul, int_two_pow_natAbs]
  exact valuation2_mul_two_pow (by omega) e

/-- Uniqueness of `oddPartInt` on products `m * 2 ^ e` with `m` odd. -/
theorem oddPartInt_mul_two_pow_eq {m : Int} (hm : m % 2 ≠ 0) (e : Nat) :
    oddPartInt (m * (2 : Int) ^ e) = m := by
  have hfac := oddPartInt_mul_two_pow (m * (2 : Int) ^ e)
  rw [valuation2Int_mul_two_pow hm e] at hfac
  exact Int.eq_of_mul_eq_mul_right (int_two_pow_ne_zero e) hfac

/-- The factor `(2 : Int) ^ valuation2Int z` always divides `z`. -/
theorem two_pow_valuation2Int_dvd (z : Int) : (2 : Int) ^ valuation2Int z ∣ z :=
  ⟨oddPartInt z, by rw [Int.mul_comm, oddPartInt_mul_two_pow]⟩

/-! ### 2. `OddDenomRat` Arithmetic, `ℤ_(2)` Equivalence, and Parity -/

namespace OddDenomRat

/-- Extensionality for `OddDenomRat`: equal numerators and denominators give equal values. -/
theorem ext {a b : OddDenomRat} (hnum : a.num = b.num) (hden : a.den = b.den) : a = b := by
  cases a; cases b; simp only at hnum hden; subst hnum; subst hden; rfl

/-- Fraction equality in `ℤ_(2) ⊂ ℚ`: `a / b = c / d` iff `a * d = c * b`. -/
def Equiv (a b : OddDenomRat) : Prop :=
  a.num * (b.den : Int) = b.num * (a.den : Int)

/-- Every `OddDenomRat` has a positive denominator. -/
theorem den_pos (a : OddDenomRat) : 0 < a.den := by have := a.den_odd; omega

/-- Every `OddDenomRat` has a nonzero integer-cast denominator. -/
theorem den_int_ne_zero (a : OddDenomRat) : (a.den : Int) ≠ 0 := by have := a.den_pos; omega

/-- Reflexivity of `OddDenomRat.Equiv`. -/
theorem Equiv.refl (a : OddDenomRat) : a.Equiv a := rfl

/-- Symmetry of `OddDenomRat.Equiv`. -/
theorem Equiv.symm {a b : OddDenomRat} (h : a.Equiv b) : b.Equiv a := Eq.symm h

/-- Transitivity of `OddDenomRat.Equiv`. -/
theorem Equiv.trans {a b c : OddDenomRat} (hab : a.Equiv b) (hbc : b.Equiv c) : a.Equiv c := by
  apply Int.eq_of_mul_eq_mul_right (den_int_ne_zero b)
  calc a.num * (c.den : Int) * (b.den : Int)
      = (a.num * (b.den : Int)) * (c.den : Int) := by rw [Int.mul_right_comm]
    _ = (b.num * (c.den : Int)) * (a.den : Int) := by rw [hab, Int.mul_right_comm]
    _ = c.num * (a.den : Int) * (b.den : Int) := by rw [hbc, Int.mul_right_comm]

/-- Canonical embedding of `ℤ` into `ℤ_(2)` (`n ↦ n / 1`). -/
def ofInt (n : Int) : OddDenomRat := ⟨n, 1, rfl⟩

/-- Canonical embedding of `ℕ` into `ℤ_(2)` (`n ↦ n / 1`). -/
def ofNat (n : Nat) : OddDenomRat := ⟨(n : Int), 1, rfl⟩

/-- Construct an `OddDenomRat` from integer numerator `n` and odd integer denominator `d`,
normalizing the sign of `d` into the numerator so the stored denominator is `d.natAbs`. -/
def ofIntFrac (n d : Int) (hd : d % 2 ≠ 0) : OddDenomRat :=
  ⟨if d < 0 then -n else n, d.natAbs, by omega⟩

/-- Cross-multiplication identity: `(ofIntFrac n d hd).num * d = n * (ofIntFrac n d hd).den`. -/
theorem ofIntFrac_mul_den (n d : Int) (hd : d % 2 ≠ 0) :
    (ofIntFrac n d hd).num * d = n * ((ofIntFrac n d hd).den : Int) := by
  unfold ofIntFrac
  by_cases hneg : d < 0
  · rw [ite_eq_left hneg, show (d.natAbs : Int) = -d by omega, Int.neg_mul, Int.mul_neg]
  · rw [ite_eq_right hneg, show (d.natAbs : Int) = d by omega]

/-- Criterion for equivalence to `ofIntFrac n d hd`: `a ≈ n / d` iff `a.num * d = n * a.den`. -/
theorem equiv_ofIntFrac_iff {a : OddDenomRat} {n d : Int} (hd : d % 2 ≠ 0) :
    a.Equiv (ofIntFrac n d hd) ↔ a.num * d = n * (a.den : Int) := by
  have hd_ne : d ≠ 0 := by omega
  have hden := ofIntFrac_mul_den n d hd
  constructor
  · intro h
    apply Int.eq_of_mul_eq_mul_right (den_int_ne_zero (ofIntFrac n d hd))
    calc a.num * d * ((ofIntFrac n d hd).den : Int)
        = (a.num * ((ofIntFrac n d hd).den : Int)) * d := by rw [Int.mul_right_comm]
      _ = ((ofIntFrac n d hd).num * d) * (a.den : Int) := by rw [h, Int.mul_right_comm]
      _ = n * (a.den : Int) * ((ofIntFrac n d hd).den : Int) := by rw [hden, Int.mul_right_comm]
  · intro h
    apply Int.eq_of_mul_eq_mul_right hd_ne
    calc a.num * ((ofIntFrac n d hd).den : Int) * d
        = (a.num * d) * ((ofIntFrac n d hd).den : Int) := by rw [Int.mul_right_comm]
      _ = (n * ((ofIntFrac n d hd).den : Int)) * (a.den : Int) := by rw [h, Int.mul_right_comm]
      _ = (ofIntFrac n d hd).num * (a.den : Int) * d := by rw [← hden, Int.mul_right_comm]

/-- Exact addition on `OddDenomRat` (`a / b + c / d = (ad + cb) / (bd)`). -/
def add (a b : OddDenomRat) : OddDenomRat :=
  ⟨a.num * (b.den : Int) + b.num * (a.den : Int), a.den * b.den,
    by rw [Nat.mul_mod, a.den_odd, b.den_odd]⟩

/-- Exact multiplication on `OddDenomRat` (`(a / b) * (c / d) = (ac) / (bd)`). -/
def mul (a b : OddDenomRat) : OddDenomRat :=
  ⟨a.num * b.num, a.den * b.den, by rw [Nat.mul_mod, a.den_odd, b.den_odd]⟩

/-- Denominator-preserving integer scaling `c * (num / den) = (c * num) / den`. -/
def scaleInt (c : Int) (a : OddDenomRat) : OddDenomRat := ⟨c * a.num, a.den, a.den_odd⟩

/-- Denominator-preserving affine odd step `x ↦ 3 * x + 1` on `ℤ_(2)`. -/
def step3n1 (a : OddDenomRat) : OddDenomRat := ⟨3 * a.num + (a.den : Int), a.den, a.den_odd⟩

/-- Exact division by `2 ^ e` when `(2 : Int) ^ e ∣ a.num`, preserving the odd denominator. -/
def divTwoPow (a : OddDenomRat) (e : Nat) (_h : (2 : Int) ^ e ∣ a.num) : OddDenomRat :=
  ⟨a.num / (2 : Int) ^ e, a.den, a.den_odd⟩

/-- `step3n1 a` is equivalent to `add (mul (ofInt 3) a) (ofInt 1)`. -/
theorem step3n1_equiv (a : OddDenomRat) :
    (step3n1 a).Equiv (add (mul (ofInt 3) a) (ofInt 1)) := by
  simp [Equiv, step3n1, add, mul, ofInt]

/-- Scaling `a.divTwoPow e h` back by `2 ^ e` recovers `a` identically. -/
theorem scaleInt_two_pow_divTwoPow (a : OddDenomRat) (e : Nat) (h : (2 : Int) ^ e ∣ a.num) :
    scaleInt ((2 : Int) ^ e) (a.divTwoPow e h) = a :=
  ext (Int.mul_ediv_cancel' h) rfl

/-- Multiplying `a.divTwoPow e h` by `ofNat (2 ^ e)` is equivalent to `a`. -/
theorem mul_two_pow_divTwoPow_equiv (a : OddDenomRat) (e : Nat) (h : (2 : Int) ^ e ∣ a.num) :
    (mul (ofNat (2 ^ e)) (a.divTwoPow e h)).Equiv a := by
  simp only [Equiv, mul, ofNat, divTwoPow, Nat.one_mul, Int.natCast_pow, natCast_two]
  rw [Int.mul_ediv_cancel' h]

/-- Addition respects `OddDenomRat.Equiv`. -/
theorem add_congr {a₁ a₂ b₁ b₂ : OddDenomRat} (ha : a₁.Equiv a₂) (hb : b₁.Equiv b₂) :
    (add a₁ b₁).Equiv (add a₂ b₂) := by
  unfold Equiv add
  rw [Int.natCast_mul, Int.natCast_mul, Int.add_mul, Int.add_mul]
  have h1 : a₁.num * (b₁.den : Int) * ((a₂.den : Int) * (b₂.den : Int)) =
      a₂.num * (b₂.den : Int) * ((a₁.den : Int) * (b₁.den : Int)) := by
    rw [Int.mul_assoc, Int.mul_left_comm (b₁.den : Int), ← Int.mul_assoc, ha,
      Int.mul_comm (b₁.den : Int), Int.mul_assoc, Int.mul_left_comm (a₁.den : Int), ← Int.mul_assoc]
  have h2 : b₁.num * (a₁.den : Int) * ((a₂.den : Int) * (b₂.den : Int)) =
      b₂.num * (a₂.den : Int) * ((a₁.den : Int) * (b₁.den : Int)) := by
    rw [Int.mul_assoc, Int.mul_comm (a₂.den : Int), Int.mul_left_comm (a₁.den : Int),
      ← Int.mul_assoc, hb, Int.mul_comm (a₁.den : Int), Int.mul_assoc,
      Int.mul_left_comm (b₁.den : Int), ← Int.mul_assoc, Int.mul_comm (b₁.den : Int)]
  rw [h1, h2]

/-- Multiplication respects `OddDenomRat.Equiv`. -/
theorem mul_congr {a₁ a₂ b₁ b₂ : OddDenomRat} (ha : a₁.Equiv a₂) (hb : b₁.Equiv b₂) :
    (mul a₁ b₁).Equiv (mul a₂ b₂) := by
  unfold Equiv mul
  rw [Int.natCast_mul, Int.natCast_mul, Int.mul_assoc, Int.mul_left_comm b₁.num (a₂.den : Int),
    ← Int.mul_assoc, ha, hb, Int.mul_assoc, Int.mul_left_comm (a₁.den : Int) b₂.num,
    ← Int.mul_assoc]

/-- `step3n1` respects `OddDenomRat.Equiv`. -/
theorem step3n1_congr {a b : OddDenomRat} (h : a.Equiv b) : a.step3n1.Equiv b.step3n1 := by
  unfold Equiv step3n1
  rw [Int.add_mul, Int.add_mul, Int.mul_assoc, Int.mul_assoc, h, Int.mul_comm (a.den : Int)]

/-- An element of `ℤ_(2)` is `2`-adically even iff its numerator is even. -/
def isEven (a : OddDenomRat) : Prop := a.num % 2 = 0

/-- An element of `ℤ_(2)` is `2`-adically odd (a unit in `ℤ_(2)`) iff its numerator is odd. -/
def isOdd (a : OddDenomRat) : Prop := a.num % 2 ≠ 0

/-- Exact `2`-adic valuation `v₂(a.num / a.den) = v₂(a.num)` on `ℤ_(2)`. -/
def val2 (a : OddDenomRat) : Nat := valuation2Int a.num

/-- Odd part of an element of `ℤ_(2)`: strips all factors of `2` from `a.num`. -/
def oddPart (a : OddDenomRat) : OddDenomRat := ⟨oddPartInt a.num, a.den, a.den_odd⟩

/-- `2`-adic evenness is invariant under `OddDenomRat.Equiv`. -/
theorem isEven_congr {a b : OddDenomRat} (h : a.Equiv b) : a.isEven ↔ b.isEven := by
  have ha : (a.den : Int) % 2 = 1 := by have := a.den_odd; omega
  have hb : (b.den : Int) % 2 = 1 := by have := b.den_odd; omega
  have hmod : (a.num * (b.den : Int)) % 2 = (b.num * (a.den : Int)) % 2 := by rw [h]
  unfold isEven
  rw [Int.mul_emod a.num, Int.mul_emod b.num, ha, hb] at hmod
  omega

/-- `2`-adic oddness is invariant under `OddDenomRat.Equiv`. -/
theorem isOdd_congr {a b : OddDenomRat} (h : a.Equiv b) : a.isOdd ↔ b.isOdd :=
  not_congr (isEven_congr h)

/-- `2`-adic valuation `val2` is invariant under `OddDenomRat.Equiv`. -/
theorem val2_congr {a b : OddDenomRat} (h : a.Equiv b) : a.val2 = b.val2 := by
  unfold val2
  calc valuation2Int a.num
      = valuation2Int (a.num * (b.den : Int)) := (valuation2Int_mul_odd a.num b.den_odd).symm
    _ = valuation2Int (b.num * (a.den : Int)) := by rw [h]
    _ = valuation2Int b.num := valuation2Int_mul_odd b.num a.den_odd

/-- Exact `2`-adic factorization on `OddDenomRat`: `2 ^ a.val2 * a.oddPart = a`. -/
theorem scaleInt_two_pow_oddPart (a : OddDenomRat) :
    scaleInt ((2 : Int) ^ a.val2) a.oddPart = a := by
  refine ext ?_ rfl
  simp only [scaleInt, oddPart, val2]
  rw [Int.mul_comm]
  exact oddPartInt_mul_two_pow a.num

/-- `oddPart` respects `OddDenomRat.Equiv`. -/
theorem oddPart_congr {a b : OddDenomRat} (h : a.Equiv b) : a.oddPart.Equiv b.oddPart := by
  have hv : a.val2 = b.val2 := val2_congr h
  apply Int.eq_of_mul_eq_mul_left (int_two_pow_ne_zero a.val2)
  unfold oddPart
  calc (2 : Int) ^ a.val2 * (oddPartInt a.num * (b.den : Int))
      = (oddPartInt a.num * (2 : Int) ^ valuation2Int a.num) * (b.den : Int) := by
          rw [← Int.mul_assoc, Int.mul_comm ((2 : Int) ^ a.val2)]; rfl
    _ = b.num * (a.den : Int) := by rw [oddPartInt_mul_two_pow, h]
    _ = (oddPartInt b.num * (2 : Int) ^ valuation2Int b.num) * (a.den : Int) := by
          rw [oddPartInt_mul_two_pow]
    _ = (2 : Int) ^ a.val2 * (oddPartInt b.num * (a.den : Int)) := by
          rw [hv]; unfold val2
          rw [← Int.mul_assoc, Int.mul_comm ((2 : Int) ^ valuation2Int b.num)]

/-! ### 3. Syracuse & Collatz Dynamics on `ℤ_(2)` (`OddDenomRat`) -/

/-- `2`-adic Syracuse halving exponent `v₂(3x + 1)` on `ℤ_(2)`. -/
def syracuseVal (a : OddDenomRat) : Nat := a.step3n1.val2

/-- One step of the accelerated Syracuse map `T(x) = oddPart (3x + 1)` on `ℤ_(2)`. -/
def syracuseStep (a : OddDenomRat) : OddDenomRat := a.step3n1.oddPart

/-- `syracuseVal` respects `OddDenomRat.Equiv`. -/
theorem syracuseVal_congr {a b : OddDenomRat} (h : a.Equiv b) : a.syracuseVal = b.syracuseVal :=
  val2_congr (step3n1_congr h)

/-- `syracuseStep` respects `OddDenomRat.Equiv`. -/
theorem syracuseStep_congr {a b : OddDenomRat} (h : a.Equiv b) :
    a.syracuseStep.Equiv b.syracuseStep :=
  oddPart_congr (step3n1_congr h)

/-- Exact one-step multiplicative Syracuse identity on `ℤ_(2)`:
`2 ^ a.syracuseVal * a.syracuseStep = a.step3n1`. -/
theorem scaleInt_two_pow_syracuseStep (a : OddDenomRat) :
    scaleInt ((2 : Int) ^ a.syracuseVal) a.syracuseStep = a.step3n1 :=
  scaleInt_two_pow_oddPart a.step3n1

/-- `a.syracuseStep` equals `a.step3n1.divTwoPow a.syracuseVal`. -/
theorem syracuseStep_eq_divTwoPow (a : OddDenomRat) :
    a.syracuseStep = a.step3n1.divTwoPow a.syracuseVal
      (two_pow_valuation2Int_dvd a.step3n1.num) := by
  refine ext ?_ rfl
  apply Int.eq_of_mul_eq_mul_left (int_two_pow_ne_zero a.syracuseVal)
  have h1 := congrArg OddDenomRat.num (scaleInt_two_pow_syracuseStep a)
  have h2 := congrArg OddDenomRat.num
    (scaleInt_two_pow_divTwoPow a.step3n1 a.syracuseVal (two_pow_valuation2Int_dvd a.step3n1.num))
  exact h1.trans h2.symm

/-- The `k`-th iterate of `OddDenomRat.syracuseStep`. -/
def syracuseIter : Nat → OddDenomRat → OddDenomRat
  | 0, a => a
  | k + 1, a => syracuseIter k a.syracuseStep

/-- Total halving exponent accumulated over `k` Syracuse steps in `ℤ_(2)`. -/
def syracuseTotalVal : Nat → OddDenomRat → Nat
  | 0, _ => 0
  | k + 1, a => a.syracuseVal + syracuseTotalVal k a.syracuseStep

/-- Affine offset `C(v)` accumulated over `k` Syracuse steps in `ℤ_(2)`. -/
def syracuseOffset : Nat → OddDenomRat → Nat
  | 0, _ => 0
  | k + 1, a => 3 ^ k + 2 ^ a.syracuseVal * syracuseOffset k a.syracuseStep

/-- Exact list of `k` halving exponents along a `ℤ_(2)` Syracuse orbit. -/
def syracuseValVec : Nat → OddDenomRat → List Nat
  | 0, _ => []
  | k + 1, a => a.syracuseVal :: syracuseValVec k a.syracuseStep

/-- `paritySum` of `OddDenomRat.syracuseValVec` equals `syracuseTotalVal`. -/
theorem paritySum_syracuseValVec (k : Nat) (a : OddDenomRat) :
    paritySum (syracuseValVec k a) = syracuseTotalVal k a := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => simp [syracuseValVec, paritySum, syracuseTotalVal, ih]

/-- `OddDenomRat.syracuseValVec k a` has length `k`. -/
theorem syracuseValVec_length (k : Nat) (a : OddDenomRat) : (syracuseValVec k a).length = k := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => simp [syracuseValVec, ih]

/-- `parityOffset` of `OddDenomRat.syracuseValVec` equals `syracuseOffset`. -/
theorem parityOffset_syracuseValVec (k : Nat) (a : OddDenomRat) :
    parityOffset (syracuseValVec k a) = syracuseOffset k a := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    simp [syracuseValVec, parityOffset, syracuseOffset, syracuseValVec_length, ih]

/-- `syracuseIter` preserves the stored odd denominator identically. -/
theorem syracuseIter_den (k : Nat) (a : OddDenomRat) : (syracuseIter k a).den = a.den := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => exact ih a.syracuseStep

/-- `syracuseIter` respects `OddDenomRat.Equiv`. -/
theorem syracuseIter_congr (k : Nat) {a b : OddDenomRat} (h : a.Equiv b) :
    (syracuseIter k a).Equiv (syracuseIter k b) := by
  induction k generalizing a b with
  | zero => exact h
  | succ k ih => exact ih (syracuseStep_congr h)

/-- Composition law for `OddDenomRat.syracuseIter`. -/
theorem syracuseIter_add (k m : Nat) (a : OddDenomRat) :
    syracuseIter m (syracuseIter k a) = syracuseIter (k + m) a := by
  induction k generalizing a with
  | zero => simp [syracuseIter]
  | succ k ih => simp only [syracuseIter, Nat.succ_add]; exact ih a.syracuseStep

/-- Fixed point `syracuseStep (ofInt 1) = ofInt 1` in `ℤ_(2)`. -/
theorem syracuseStep_ofInt_one : (ofInt 1).syracuseStep = ofInt 1 := by
  refine ext ?_ rfl
  simpa [syracuseStep, oddPart, step3n1, ofInt] using
    oddPartInt_mul_two_pow_eq (m := 1) (by decide) 2

/-- Every iterate of `ofInt 1` under `OddDenomRat.syracuseIter` equals `ofInt 1`. -/
theorem syracuseIter_ofInt_one (k : Nat) : syracuseIter k (ofInt 1) = ofInt 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [syracuseIter, syracuseStep_ofInt_one, ih]

/-- If a `ℤ_(2)` Syracuse cycle starts away from `1`, every iterate on the cycle avoids `1`. -/
theorem cycle_avoids_one {k : Nat} {a : OddDenomRat}
    (hcyc : syracuseIter k a = a) (hne : ¬ a.Equiv (ofInt 1)) :
    ∀ j : Nat, j < k → ¬ (syracuseIter j a).Equiv (ofInt 1) := by
  intro j hj heq
  apply hne
  have hback : (syracuseIter (k - j) (syracuseIter j a)).Equiv (ofInt 1) := by
    rw [← syracuseIter_ofInt_one (k - j)]
    exact syracuseIter_congr (k - j) heq
  rw [syracuseIter_add, Nat.add_sub_of_le (Nat.le_of_lt hj), hcyc] at hback
  exact hback

/-- **Main `ℤ_(2)` Affine Formula:** along any `k`-step Syracuse orbit in `ℤ_(2)`,
`2 ^ S * (syracuseIter k a).num = 3 ^ k * a.num + C * a.den`. -/
theorem syracuse_affine_num_eq (k : Nat) (a : OddDenomRat) :
    (2 : Int) ^ syracuseTotalVal k a * (syracuseIter k a).num =
      (3 : Int) ^ k * a.num + (syracuseOffset k a : Int) * (a.den : Int) := by
  induction k generalizing a with
  | zero => simp [syracuseTotalVal, syracuseIter, syracuseOffset]
  | succ k ih =>
    have hstep : (2 : Int) ^ a.syracuseVal * a.syracuseStep.num = 3 * a.num + (a.den : Int) :=
      congrArg OddDenomRat.num (scaleInt_two_pow_syracuseStep a)
    calc (2 : Int) ^ syracuseTotalVal (k + 1) a * (syracuseIter (k + 1) a).num
        = (2 : Int) ^ a.syracuseVal *
            ((2 : Int) ^ syracuseTotalVal k a.syracuseStep *
              (syracuseIter k a.syracuseStep).num) := by
            simp only [syracuseTotalVal, syracuseIter, Int.pow_add, Int.mul_assoc]
      _ = (3 : Int) ^ k * ((2 : Int) ^ a.syracuseVal * a.syracuseStep.num) +
            ((2 : Int) ^ a.syracuseVal * (syracuseOffset k a.syracuseStep : Int)) *
              (a.den : Int) := by
            rw [ih a.syracuseStep]
            simp only [syracuseStep, oddPart, step3n1] at *
            rw [Int.mul_add, Int.mul_left_comm ((2 : Int) ^ a.syracuseVal) ((3 : Int) ^ k),
              Int.mul_assoc]
      _ = (3 : Int) ^ (k + 1) * a.num + (syracuseOffset (k + 1) a : Int) * (a.den : Int) := by
            rw [hstep]
            simp only [syracuseOffset, Int.natCast_add, Int.natCast_mul,
              Int.natCast_pow, natCast_two, natCast_three]
            rw [Int.mul_add, ← Int.mul_assoc, ← Int.pow_succ, Int.add_assoc, ← Int.add_mul]

/-- Rational equivalence form of `syracuse_affine_num_eq` in `ℤ_(2)`. -/
theorem syracuse_affine_equiv (k : Nat) (a : OddDenomRat) :
    (mul (ofNat (2 ^ syracuseTotalVal k a)) (syracuseIter k a)).Equiv
      (add (mul (ofNat (3 ^ k)) a) (ofNat (syracuseOffset k a))) := by
  unfold Equiv mul add ofNat
  simp only [Nat.one_mul, Nat.mul_one, Int.natCast_one, Int.mul_one,
    Int.natCast_pow, natCast_two, natCast_three, syracuseIter_den]
  rw [syracuse_affine_num_eq k a]

/-- One step of the unaccelerated Collatz map on `ℤ_(2)`: halve if even, `3x + 1` if odd. -/
def collatzStep (a : OddDenomRat) : OddDenomRat :=
  if h : a.num % 2 = 0 then
    a.divTwoPow 1 (by simpa [Int.pow_one] using Int.dvd_of_emod_eq_zero h)
  else
    a.step3n1

/-- `collatzStep` respects `OddDenomRat.Equiv`. -/
theorem collatzStep_congr {a b : OddDenomRat} (h : a.Equiv b) :
    a.collatzStep.Equiv b.collatzStep := by
  have hev := isEven_congr h
  unfold collatzStep
  by_cases ha : a.num % 2 = 0
  · have hb : b.num % 2 = 0 := hev.mp ha
    rw [dite_eq_left ha, dite_eq_left hb]
    have hdA : (2 : Int) ^ 1 ∣ a.num := by simpa [Int.pow_one] using Int.dvd_of_emod_eq_zero ha
    have hdB : (2 : Int) ^ 1 ∣ b.num := by simpa [Int.pow_one] using Int.dvd_of_emod_eq_zero hb
    apply Int.eq_of_mul_eq_mul_left (int_two_pow_ne_zero 1)
    simp only [divTwoPow]
    rw [← Int.mul_assoc, ← Int.mul_assoc,
      Int.mul_ediv_cancel' hdA, Int.mul_ediv_cancel' hdB, h]
  · have hb : ¬ b.num % 2 = 0 := fun hb => ha (hev.mpr hb)
    rw [dite_eq_right ha, dite_eq_right hb]
    exact step3n1_congr h

/-- The `k`-th iterate of `OddDenomRat.collatzStep` on `ℤ_(2)`. -/
def collatzIter : Nat → OddDenomRat → OddDenomRat
  | 0, a => a
  | k + 1, a => collatzIter k a.collatzStep

/-- Composition law for `OddDenomRat.collatzIter`. -/
theorem collatzIter_add (k m : Nat) (a : OddDenomRat) :
    collatzIter m (collatzIter k a) = collatzIter (k + m) a := by
  induction k generalizing a with
  | zero => simp [collatzIter]
  | succ k ih => simp only [collatzIter, Nat.succ_add]; exact ih a.collatzStep

/-- On `ofInt n`, `OddDenomRat.collatzStep` agrees identically with `Barriers.genStep 3 1 n`. -/
theorem collatzStep_ofInt (n : Int) :
    collatzStep (ofInt n) = ofInt (Barriers.genStep 3 1 n) := by
  unfold collatzStep Barriers.genStep ofInt
  by_cases h : n % 2 = 0
  · simp [dite_eq_left h, ite_eq_left h, divTwoPow]
  · simp [dite_eq_right h, ite_eq_right h, step3n1]

/-- On `ofInt n`, `OddDenomRat.collatzIter` agrees identically with `Barriers.genIter 3 1`. -/
theorem collatzIter_ofInt (k : Nat) (n : Int) :
    collatzIter k (ofInt n) = ofInt (Barriers.genIter 3 1 k n) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp only [collatzIter, Barriers.genIter, collatzStep_ofInt]; exact ih _

/-- On `ofNat n`, `OddDenomRat.collatzStep` agrees identically with frozen `collatzStep`. -/
theorem collatzStep_ofNat (n : Nat) :
    collatzStep (ofNat n) = ofNat (SolveCollatz.collatzStep n) := by
  unfold collatzStep SolveCollatz.collatzStep ofNat
  by_cases h : n % 2 = 0
  · have h' : (n : Int) % 2 = 0 := by omega
    rw [dite_eq_left h', ite_eq_left h]
    exact ext (by simp only [divTwoPow, Int.pow_one]; omega) rfl
  · have h' : ¬ (n : Int) % 2 = 0 := by omega
    rw [dite_eq_right h', ite_eq_right h]
    exact ext (by simp only [step3n1]; omega) rfl

/-- On `ofNat n`, `OddDenomRat.collatzIter` agrees identically with frozen `collatzIter`. -/
theorem collatzIter_ofNat (k n : Nat) :
    collatzIter k (ofNat n) = ofNat (SolveCollatz.collatzIter k n) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp only [collatzIter, SolveCollatz.collatzIter, collatzStep_ofNat]; exact ih _

/-- Applying `e` halving steps to `scaleInt (2 ^ e) a` recovers `a`. -/
theorem collatzIter_scaleInt_two_pow (e : Nat) (a : OddDenomRat) :
    collatzIter e (scaleInt ((2 : Int) ^ e) a) = a := by
  induction e with
  | zero => exact ext (by simp [collatzIter, scaleInt]) rfl
  | succ e ih =>
    have hmul : (2 : Int) ^ (e + 1) * a.num = ((2 : Int) ^ e * a.num) * 2 := by
      rw [Int.pow_succ, Int.mul_right_comm]
    have hev : (scaleInt ((2 : Int) ^ (e + 1)) a).num % 2 = 0 := by
      simp only [scaleInt, hmul]; omega
    have hstep : collatzStep (scaleInt ((2 : Int) ^ (e + 1)) a) =
        scaleInt ((2 : Int) ^ e) a := by
      unfold collatzStep
      rw [dite_eq_left hev]
      exact ext (by simp only [divTwoPow, scaleInt, Int.pow_one, hmul]; omega) rfl
    rw [collatzIter, hstep]; exact ih

/-- Stripping `a.val2` Collatz halvings from `a` reaches `a.oddPart`. -/
theorem collatzIter_val2 (a : OddDenomRat) : collatzIter a.val2 a = a.oddPart := by
  have h := collatzIter_scaleInt_two_pow a.val2 a.oddPart
  rwa [scaleInt_two_pow_oddPart a] at h

/-- **One-Step `ℤ_(2)` Bridge:** on any odd `a : OddDenomRat`, one Syracuse step equals
`a.syracuseVal + 1` unaccelerated Collatz steps. -/
theorem collatzIter_eq_syracuseStep {a : OddDenomRat} (ha : a.isOdd) :
    collatzIter (a.syracuseVal + 1) a = a.syracuseStep := by
  have hstep : a.collatzStep = a.step3n1 := by unfold collatzStep; exact dite_eq_right ha
  rw [collatzIter, hstep]
  exact collatzIter_val2 a.step3n1

/-- **Iterated `ℤ_(2)` Orbit Bridge:** if every Syracuse iterate `0 ≤ i < k` is odd, then
`k` Syracuse steps equal `syracuseTotalVal k a + k` unaccelerated Collatz steps. -/
theorem collatzIter_eq_syracuseIter (k : Nat) {a : OddDenomRat}
    (hodd : ∀ i : Nat, i < k → (syracuseIter i a).isOdd) :
    collatzIter (syracuseTotalVal k a + k) a = syracuseIter k a := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    have h0 : a.isOdd := hodd 0 (Nat.succ_pos k)
    have hrest : ∀ i : Nat, i < k → (syracuseIter i a.syracuseStep).isOdd := fun i hi =>
      hodd (i + 1) (Nat.succ_lt_succ hi)
    have hsplit : syracuseTotalVal (k + 1) a + (k + 1) =
        (a.syracuseVal + 1) + (syracuseTotalVal k a.syracuseStep + k) := by
      simp only [syracuseTotalVal]; omega
    rw [hsplit, ← collatzIter_add, collatzIter_eq_syracuseStep h0]
    exact ih hrest

end OddDenomRat

/-! ### 4. Parity-Vector Periodic Points & Universal `2`-adic Periodic Point Theorem -/

/-- Exact integer denominator `2 ^ S(v) - 3 ^ k` of the unique `2`-adic periodic point
associated with parity vector `v`. -/
def periodicPointDen (v : List Nat) : Int :=
  (2 ^ paritySum v : Int) - (3 ^ v.length : Int)

/-- Whenever `0 < paritySum v`, `2 ^ S(v) - 3 ^ k` is always odd (`% 2 ≠ 0`, hence invertible in
`ℤ_(2) ⊂ ℤ₂` and automatically nonzero). -/
theorem periodicPointDen_odd {v : List Nat} (hS : 0 < paritySum v) :
    periodicPointDen v % 2 ≠ 0 := by
  unfold periodicPointDen
  have h2 : (2 : Int) ^ paritySum v % 2 = 0 := int_two_pow_mod_two hS
  have h3 : (3 : Int) ^ v.length % 2 = 1 := int_three_pow_mod_two v.length
  omega

/-- Whenever `0 < paritySum v`, `2 ^ S(v) ≠ 3 ^ k` (`periodicPointDen v ≠ 0`). -/
theorem periodicPointDen_ne_zero {v : List Nat} (hS : 0 < paritySum v) :
    periodicPointDen v ≠ 0 := by
  have := periodicPointDen_odd hS; omega

/-- A valid Syracuse parity vector is non-empty with every halving exponent positive (`e ≥ 1`). -/
def IsValidParityVec (v : List Nat) : Prop :=
  v ≠ [] ∧ ∀ e, e ∈ v → 0 < e

/-- Every valid parity vector has positive total halving sum (`0 < paritySum v`). -/
theorem paritySum_pos_of_valid {v : List Nat} (hv : IsValidParityVec v) : 0 < paritySum v := by
  cases v with
  | nil => exact absurd rfl hv.1
  | cons e es => have := hv.2 e (List.Mem.head es); simp only [paritySum]; omega

/-- Every valid parity vector has an odd affine numerator `parityOffset v`. -/
theorem parityOffset_odd_of_valid {v : List Nat} (hv : IsValidParityVec v) :
    parityOffset v % 2 = 1 := by
  cases v with
  | nil => exact absurd rfl hv.1
  | cons e es =>
    have he : 0 < e := hv.2 e (List.Mem.head es)
    have h2 : (2 ^ e) % 2 = 0 := by
      cases e with | zero => exact absurd he (Nat.lt_irrefl 0) | succ _ => rw [Nat.pow_succ]; omega
    have h3 : (3 ^ es.length) % 2 = 1 := by
      have h := int_three_pow_mod_two es.length
      rw [← natCast_three, ← Int.natCast_pow] at h; omega
    simp only [parityOffset]; rw [Nat.add_mod, Nat.mul_mod, h2, h3]; omega

/-- The unique odd-denominator rational `x(v) = C(v) / (2 ^ S(v) - 3 ^ k) ∈ ℤ_(2) ⊂ ℤ₂`. -/
def periodicPoint (v : List Nat) (hS : 0 < paritySum v) : OddDenomRat :=
  OddDenomRat.ofIntFrac (parityOffset v : Int) (periodicPointDen v) (periodicPointDen_odd hS)

/-- For any valid parity vector `v`, `periodicPoint v` is `2`-adically odd (a unit in `ℤ_(2)`). -/
theorem periodicPoint_isOdd {v : List Nat} (hv : IsValidParityVec v) :
    (periodicPoint v (paritySum_pos_of_valid hv)).isOdd := by
  have hC : (parityOffset v : Int) % 2 = 1 := by have := parityOffset_odd_of_valid hv; omega
  simp only [OddDenomRat.isOdd, periodicPoint, OddDenomRat.ofIntFrac]
  by_cases hneg : periodicPointDen v < 0
  · rw [ite_eq_left hneg]; omega
  · rw [ite_eq_right hneg]; omega

/-- `periodicPoint v` satisfies the exact rational Syracuse periodic equation
`2 ^ S(v) * x = 3 ^ k * x + C(v)` in `ℤ_(2)`. -/
theorem periodicPoint_equation {v : List Nat} (hS : 0 < paritySum v) :
    (OddDenomRat.mul (OddDenomRat.ofNat (2 ^ paritySum v)) (periodicPoint v hS)).Equiv
      (OddDenomRat.add
        (OddDenomRat.mul (OddDenomRat.ofNat (3 ^ v.length)) (periodicPoint v hS))
        (OddDenomRat.ofNat (parityOffset v))) := by
  have hsub : (periodicPoint v hS).num * ((2 : Int) ^ paritySum v - (3 : Int) ^ v.length) =
      (parityOffset v : Int) * ((periodicPoint v hS).den : Int) :=
    OddDenomRat.ofIntFrac_mul_den _ _ (periodicPointDen_odd hS)
  rw [Int.mul_sub, Int.mul_comm ((periodicPoint v hS).num),
    Int.mul_comm ((periodicPoint v hS).num)] at hsub
  simp only [OddDenomRat.Equiv, OddDenomRat.mul, OddDenomRat.add, OddDenomRat.ofNat,
    Nat.one_mul, Nat.mul_one, Int.natCast_one, Int.mul_one, Int.natCast_pow, natCast_two,
    natCast_three]
  rw [show (2 : Int) ^ paritySum v * (periodicPoint v hS).num =
    (3 : Int) ^ v.length * (periodicPoint v hS).num +
      (parityOffset v : Int) * ((periodicPoint v hS).den : Int) by omega]

/-- **Uniqueness in `ℤ_(2)`:** any odd-denominator rational solving
`2 ^ S(v) * y = 3 ^ k * y + C(v)` is equivalent to `periodicPoint v`. -/
theorem periodicPoint_unique {v : List Nat} (hS : 0 < paritySum v) {y : OddDenomRat}
    (heq : (OddDenomRat.mul (OddDenomRat.ofNat (2 ^ paritySum v)) y).Equiv
      (OddDenomRat.add
        (OddDenomRat.mul (OddDenomRat.ofNat (3 ^ v.length)) y)
        (OddDenomRat.ofNat (parityOffset v)))) :
    y.Equiv (periodicPoint v hS) := by
  simp only [OddDenomRat.Equiv, OddDenomRat.mul, OddDenomRat.add, OddDenomRat.ofNat,
    Nat.one_mul, Nat.mul_one, Int.natCast_one, Int.mul_one, Int.natCast_pow, natCast_two,
    natCast_three] at heq
  have hmain := Int.eq_of_mul_eq_mul_right (OddDenomRat.den_int_ne_zero y) heq
  rw [periodicPoint, OddDenomRat.equiv_ofIntFrac_iff]
  unfold periodicPointDen
  rw [Int.mul_sub, Int.mul_comm y.num, Int.mul_comm y.num]; omega

/-- Left cyclic rotation of a parity vector by `r` steps. -/
def rotateLeft : Nat → List Nat → List Nat
  | 0, v => v
  | _, [] => []
  | r + 1, e :: es => rotateLeft r (es ++ [e])

/-- Cyclic rotation preserves list length. -/
theorem rotateLeft_length (r : Nat) (v : List Nat) : (rotateLeft r v).length = v.length := by
  induction r generalizing v with
  | zero => rfl
  | succ r ih => cases v with | nil => rfl | cons e es => simp [rotateLeft, ih]

/-- Cyclic rotation preserves `paritySum`. -/
theorem rotateLeft_paritySum (r : Nat) (v : List Nat) :
    paritySum (rotateLeft r v) = paritySum v := by
  induction r generalizing v with
  | zero => rfl
  | succ r ih =>
    cases v with
    | nil => rfl
    | cons e es => simp only [rotateLeft, ih, paritySum_append, paritySum]; omega

/-- Cyclic rotation preserves `periodicPointDen`. -/
theorem rotateLeft_periodicPointDen (r : Nat) (v : List Nat) :
    periodicPointDen (rotateLeft r v) = periodicPointDen v := by
  simp only [periodicPointDen, rotateLeft_paritySum, rotateLeft_length]

/-- Cyclic rotation preserves `IsValidParityVec`. -/
theorem rotateLeft_valid (r : Nat) {v : List Nat} (hv : IsValidParityVec v) :
    IsValidParityVec (rotateLeft r v) := by
  induction r generalizing v with
  | zero => exact hv
  | succ r ih =>
    cases v with
    | nil => exact absurd rfl hv.1
    | cons e es =>
      apply ih
      refine ⟨by simp, fun a ha => ?_⟩
      rcases List.mem_append.mp ha with h1 | h2
      · exact hv.2 a (List.Mem.tail e h1)
      · simp only [List.mem_singleton] at h2; subst h2; exact hv.2 a (List.Mem.head es)

/-- Rotating `u ++ w` left by `u.length` yields `w ++ u`. -/
theorem rotateLeft_append (u w : List Nat) : rotateLeft u.length (u ++ w) = w ++ u := by
  induction u generalizing w with
  | nil => simp [rotateLeft]
  | cons e es ih =>
    simp only [List.length_cons, List.cons_append, rotateLeft]
    rw [List.append_assoc, ih (w ++ [e]), List.append_assoc]; rfl

/-- Rotating a list left by its full length returns the original list. -/
theorem rotateLeft_full (v : List Nat) : rotateLeft v.length v = v := by
  simpa using rotateLeft_append v []

/-- **Exact One-Step Cocycle Identity:**
`3 * C(e :: es) + (2 ^ S - 3 ^ k) = 2 ^ e * C(es ++ [e])`. -/
theorem parityOffset_rotate_identity (e : Nat) (es : List Nat) :
    3 * (parityOffset (e :: es) : Int) + periodicPointDen (e :: es) =
      (2 : Int) ^ e * (parityOffset (es ++ [e]) : Int) := by
  have happ : parityOffset (es ++ [e]) = 3 * parityOffset es + 2 ^ paritySum es := by
    rw [parityOffset_append]; simp [parityOffset]
  have hcons : parityOffset (e :: es) = 3 ^ es.length + 2 ^ e * parityOffset es := rfl
  unfold periodicPointDen
  simp only [paritySum, List.length_cons, hcons, happ, Int.natCast_add, Int.natCast_mul,
    Int.natCast_pow, natCast_two, natCast_three, Int.pow_add, Int.pow_succ]
  rw [Int.mul_add, Int.mul_add, Int.mul_comm 3 ((3 : Int) ^ es.length),
    Int.mul_left_comm 3 ((2 : Int) ^ e)]
  omega

/-- Exact `step3n1` numerator on `periodicPoint (e :: es)`:
`(periodicPoint (e :: es)).step3n1.num = (periodicPoint (es ++ [e])).num * 2 ^ e`. -/
theorem step3n1_periodicPoint_cons_num {e : Nat} {es : List Nat}
    (hv : IsValidParityVec (e :: es)) :
    (periodicPoint (e :: es) (paritySum_pos_of_valid hv)).step3n1.num =
      (periodicPoint (es ++ [e]) (paritySum_pos_of_valid (rotateLeft_valid 1 hv))).num *
        (2 : Int) ^ e := by
  have hD : periodicPointDen (es ++ [e]) = periodicPointDen (e :: es) :=
    rotateLeft_periodicPointDen 1 (e :: es)
  have hid := parityOffset_rotate_identity e es
  unfold OddDenomRat.step3n1 periodicPoint OddDenomRat.ofIntFrac
  simp only [hD]
  by_cases hneg : periodicPointDen (e :: es) < 0
  · rw [ite_eq_left hneg, ite_eq_left hneg,
      show ((periodicPointDen (e :: es)).natAbs : Int) = -periodicPointDen (e :: es) by omega,
      Int.mul_neg, Int.neg_mul, Int.mul_comm _ ((2 : Int) ^ e)]
    omega
  · rw [ite_eq_right hneg, ite_eq_right hneg,
      show ((periodicPointDen (e :: es)).natAbs : Int) = periodicPointDen (e :: es) by omega,
      Int.mul_comm _ ((2 : Int) ^ e)]
    exact hid

/-- One Syracuse step on `periodicPoint (e :: es)` has exact halving exponent `e`. -/
theorem syracuseVal_periodicPoint_cons {e : Nat} {es : List Nat}
    (hv : IsValidParityVec (e :: es)) :
    (periodicPoint (e :: es) (paritySum_pos_of_valid hv)).syracuseVal = e := by
  have hodd := periodicPoint_isOdd (rotateLeft_valid 1 hv)
  unfold OddDenomRat.syracuseVal OddDenomRat.val2
  rw [step3n1_periodicPoint_cons_num hv]
  exact valuation2Int_mul_two_pow hodd e

/-- One Syracuse step on `periodicPoint (e :: es)` shifts the parity vector cyclically to
`periodicPoint (es ++ [e])`. -/
theorem syracuseStep_periodicPoint_cons {e : Nat} {es : List Nat}
    (hv : IsValidParityVec (e :: es)) :
    (periodicPoint (e :: es) (paritySum_pos_of_valid hv)).syracuseStep =
      periodicPoint (es ++ [e]) (paritySum_pos_of_valid (rotateLeft_valid 1 hv)) := by
  have hodd := periodicPoint_isOdd (rotateLeft_valid 1 hv)
  have hD : periodicPointDen (es ++ [e]) = periodicPointDen (e :: es) :=
    rotateLeft_periodicPointDen 1 (e :: es)
  apply OddDenomRat.ext
  · unfold OddDenomRat.syracuseStep OddDenomRat.oddPart
    rw [step3n1_periodicPoint_cons_num hv]
    exact oddPartInt_mul_two_pow_eq hodd e
  · simp [OddDenomRat.syracuseStep, OddDenomRat.oddPart, OddDenomRat.step3n1,
      periodicPoint, OddDenomRat.ofIntFrac, hD]

/-- Iterated Syracuse orbit of `periodicPoint v` after `r` steps is
`periodicPoint (rotateLeft r v)`. -/
theorem syracuseIter_periodicPoint (r : Nat) {v : List Nat} (hv : IsValidParityVec v) :
    OddDenomRat.syracuseIter r (periodicPoint v (paritySum_pos_of_valid hv)) =
      periodicPoint (rotateLeft r v) (paritySum_pos_of_valid (rotateLeft_valid r hv)) := by
  induction r generalizing v with
  | zero => rfl
  | succ r ih =>
    cases v with
    | nil => exact absurd rfl hv.1
    | cons e es =>
      simp only [OddDenomRat.syracuseIter, rotateLeft]
      rw [syracuseStep_periodicPoint_cons hv]
      exact ih (rotateLeft_valid 1 hv)

/-- Prefix halving-exponent vector of `periodicPoint (u ++ w)` along `u.length` steps is `u`. -/
theorem syracuseValVec_periodicPoint_append (u w : List Nat)
    (hv : IsValidParityVec (u ++ w)) :
    OddDenomRat.syracuseValVec u.length
      (periodicPoint (u ++ w) (paritySum_pos_of_valid hv)) = u := by
  induction u generalizing w with
  | nil => rfl
  | cons e es ih =>
    have hv' : IsValidParityVec (e :: (es ++ w)) := hv
    have hvNext : IsValidParityVec (es ++ (w ++ [e])) := by
      simpa [rotateLeft, List.append_assoc] using rotateLeft_valid 1 hv'
    simp only [List.length_cons, List.cons_append, OddDenomRat.syracuseValVec]
    rw [syracuseVal_periodicPoint_cons hv', syracuseStep_periodicPoint_cons hv']
    have hstep :
        periodicPoint ((es ++ w) ++ [e]) (paritySum_pos_of_valid (rotateLeft_valid 1 hv')) =
          periodicPoint (es ++ (w ++ [e])) (paritySum_pos_of_valid hvNext) := by
      simp [List.append_assoc]
    rw [hstep, ih (w ++ [e]) hvNext]

/-- Exact `v.length`-step Syracuse halving vector of `periodicPoint v` is `v` itself. -/
theorem syracuseValVec_periodicPoint {v : List Nat} (hv : IsValidParityVec v) :
    OddDenomRat.syracuseValVec v.length (periodicPoint v (paritySum_pos_of_valid hv)) = v := by
  have hv' : IsValidParityVec (v ++ []) := by simpa using hv
  simpa using syracuseValVec_periodicPoint_append v [] hv'

/-- **Universal `2`-adic Periodic Point Theorem (`CORE-004`, Barrier 4):**
For every valid parity vector `v`, `x = C(v) / (2 ^ S(v) - 3 ^ k)` is an odd unit in `ℤ_(2) ⊂ ℤ₂`
that uniquely solves `2 ^ S(v) * x = 3 ^ k * x + C(v)`, realizes `v` as its exact Syracuse
halving vector, and is genuinely periodic under both `syracuseIter` (period `v.length`) and
unaccelerated `collatzIter` (period `paritySum v + v.length`). -/
theorem universal_twoAdic_periodicPoint {v : List Nat} (hv : IsValidParityVec v) :
    let x := periodicPoint v (paritySum_pos_of_valid hv)
    x.isOdd ∧
    (OddDenomRat.mul (OddDenomRat.ofNat (2 ^ paritySum v)) x).Equiv
      (OddDenomRat.add
        (OddDenomRat.mul (OddDenomRat.ofNat (3 ^ v.length)) x)
        (OddDenomRat.ofNat (parityOffset v))) ∧
    OddDenomRat.syracuseIter v.length x = x ∧
    OddDenomRat.syracuseValVec v.length x = v ∧
    OddDenomRat.collatzIter (paritySum v + v.length) x = x ∧
    ∀ y : OddDenomRat,
      (OddDenomRat.mul (OddDenomRat.ofNat (2 ^ paritySum v)) y).Equiv
        (OddDenomRat.add
          (OddDenomRat.mul (OddDenomRat.ofNat (3 ^ v.length)) y)
          (OddDenomRat.ofNat (parityOffset v))) →
      y.Equiv x := by
  intro x
  have hcyc : OddDenomRat.syracuseIter v.length x = x := by
    rw [syracuseIter_periodicPoint v.length hv]; simp only [x, rotateLeft_full]
  have hvec : OddDenomRat.syracuseValVec v.length x = v := syracuseValVec_periodicPoint hv
  have hoddAll : ∀ i : Nat, i < v.length → (OddDenomRat.syracuseIter i x).isOdd := fun i _ => by
    rw [syracuseIter_periodicPoint i hv]; exact periodicPoint_isOdd (rotateLeft_valid i hv)
  have htot : OddDenomRat.syracuseTotalVal v.length x = paritySum v := by
    rw [← OddDenomRat.paritySum_syracuseValVec, hvec]
  have hcol : OddDenomRat.collatzIter (paritySum v + v.length) x = x := by
    rw [← htot, OddDenomRat.collatzIter_eq_syracuseIter v.length hoddAll, hcyc]
  exact ⟨periodicPoint_isOdd hv, periodicPoint_equation (paritySum_pos_of_valid hv),
    hcyc, hvec, hcol, fun y hy => periodicPoint_unique (paritySum_pos_of_valid hv) hy⟩

/-- **Bridge to `CORE-003` (`Syracuse.lean`):** every positive-length `ℕ` Syracuse cycle
`syracuseIter k n = n` embeds into `ℤ_(2)` as the unique `2`-adic periodic point of its own
parity vector `v = syracuseValVec k n`. -/
theorem nat_syracuse_cycle_equiv_periodicPoint {k n : Nat}
    (hk : 0 < k) (hcyc : syracuseIter k n = n) :
    ∃ hS : 0 < paritySum (syracuseValVec k n),
      (OddDenomRat.ofNat n).Equiv (periodicPoint (syracuseValVec k n) hS) := by
  have hodd : n % 2 = 1 := by rw [← hcyc]; exact syracuseIter_odd hk n
  have hge : k ≤ syracuseTotalVal k n := syracuseTotalVal_ge k hodd
  have hS : 0 < paritySum (syracuseValVec k n) := by rw [paritySum_syracuseValVec]; omega
  refine ⟨hS, periodicPoint_unique hS ?_⟩
  have hmul := syracuse_cycle_mul_eq hcyc
  unfold OddDenomRat.Equiv OddDenomRat.mul OddDenomRat.add OddDenomRat.ofNat
  simp only [Nat.mul_one, Int.natCast_one, Int.mul_one,
    paritySum_syracuseValVec, syracuseValVec_length, parityOffset_syracuseValVec]
  have hcast : ((2 ^ syracuseTotalVal k n * n : Nat) : Int) =
      ((3 ^ k * n + syracuseOffset k n : Nat) : Int) := congrArg Int.ofNat hmul
  simpa [Int.natCast_add, Int.natCast_mul] using hcast

/-! ### 5. Concrete Barrier 4 Witnesses -/

/-- **Barrier 4 Witness 1 (`v = [1, 2] ↦ -5 / 1`):** recovers the negative integer cycle
`-5 → -14 → -7 → -20 → -10 → -5` (`Barriers.neg_int_cycle_neg5`) as the `2`-adic periodic point
of `[1, 2]`. -/
theorem twoAdic_cycle_neg5 :
    let v := [1, 2]
    let x := periodicPoint v (by decide)
    x = OddDenomRat.ofInt (-5) ∧
    OddDenomRat.syracuseIter 2 x = x ∧
    OddDenomRat.syracuseValVec 2 x = v ∧
    OddDenomRat.collatzIter 5 x = x ∧
    Barriers.genIter 3 1 5 (-5) = -5 := by
  have hv : IsValidParityVec [1, 2] := by simp [IsValidParityVec]
  rcases universal_twoAdic_periodicPoint hv with ⟨_, _, hcyc, hvec, hcol, _⟩
  have hx : periodicPoint [1, 2] (by decide) = OddDenomRat.ofInt (-5) := by decide
  have hgen : Barriers.genIter 3 1 5 (-5) = -5 := by
    have h := hcol; rw [hx, OddDenomRat.collatzIter_ofInt] at h
    exact congrArg OddDenomRat.num h
  exact ⟨hx, hcyc, hvec, hcol, hgen⟩

/-- Whenever `0 < periodicPointDen v`, `periodicPoint v` has strictly positive numerator. -/
theorem periodicPoint_num_pos {v : List Nat} (hv : IsValidParityVec v)
    (hD : 0 < periodicPointDen v) :
    0 < (periodicPoint v (paritySum_pos_of_valid hv)).num := by
  have hodd := parityOffset_odd_of_valid hv
  simp only [periodicPoint, OddDenomRat.ofIntFrac,
    ite_eq_right (by omega : ¬ periodicPointDen v < 0)]
  omega

/-- **Barrier 4 Witness 2 (`v = [1, 1, 2] ↦ -19 / 11`):** matches `search/barrier_redteam.py`
Barrier 4 — a non-integral periodic orbit in `ℤ_(2) \ ℤ` avoiding `1`
(`-19/11 → -23/11 → -29/11 → -19/11`). -/
theorem twoAdic_cycle_neg19_over_11 :
    let v := [1, 1, 2]
    let x := periodicPoint v (by decide)
    x = ⟨-19, 11, by decide⟩ ∧
    OddDenomRat.syracuseIter 3 x = x ∧
    OddDenomRat.syracuseValVec 3 x = v ∧
    OddDenomRat.collatzIter 7 x = x ∧
    (¬ ∃ m : Int, x.Equiv (OddDenomRat.ofInt m)) ∧
    ∀ j : Nat, j < 3 → ¬ (OddDenomRat.syracuseIter j x).Equiv (OddDenomRat.ofInt 1) := by
  have hv : IsValidParityVec [1, 1, 2] := by simp [IsValidParityVec]
  rcases universal_twoAdic_periodicPoint hv with ⟨_, _, hcyc, hvec, hcol, _⟩
  have hx : periodicPoint [1, 1, 2] (by decide) = ⟨-19, 11, by decide⟩ := by decide
  have hnotInt :
      ¬ ∃ m : Int, (periodicPoint [1, 1, 2] (by decide)).Equiv (OddDenomRat.ofInt m) := by
    rintro ⟨m, hm⟩; rw [hx] at hm
    unfold OddDenomRat.Equiv OddDenomRat.ofInt at hm; simp only at hm; omega
  exact ⟨hx, hcyc, hvec, hcol, hnotInt,
    OddDenomRat.cycle_avoids_one hcyc (fun h1 => hnotInt ⟨1, h1⟩)⟩

/-- **Barrier 4 Witness 3 (`v = [1, 1, 1, 1, 4] ↦ 211 / 13`):** the closest positive `1`-circuit
rational near-miss (`211/13 → 323/13 → 491/13 → 743/13 → 1121/13 → 211/13`), showing `3n + 1`
admits strictly positive non-trivial cycles in `ℤ_(2) ∩ ℚ_{>0}` so any Track A proof must use
global integrality in `ℕ⁺`, not just positivity and `2`-adic arithmetic. -/
theorem twoAdic_cycle_211_over_13 :
    let v := [1, 1, 1, 1, 4]
    let x := periodicPoint v (by decide)
    x = ⟨211, 13, by decide⟩ ∧
    0 < x.num ∧
    OddDenomRat.syracuseIter 5 x = x ∧
    OddDenomRat.syracuseValVec 5 x = v ∧
    OddDenomRat.collatzIter 13 x = x ∧
    (¬ ∃ m : Int, x.Equiv (OddDenomRat.ofInt m)) ∧
    ∀ j : Nat, j < 5 →
      0 < (OddDenomRat.syracuseIter j x).num ∧
      ¬ (OddDenomRat.syracuseIter j x).Equiv (OddDenomRat.ofInt 1) := by
  have hv : IsValidParityVec [1, 1, 1, 1, 4] := by simp [IsValidParityVec]
  rcases universal_twoAdic_periodicPoint hv with ⟨_, _, hcyc, hvec, hcol, _⟩
  have hx : periodicPoint [1, 1, 1, 1, 4] (by decide) = ⟨211, 13, by decide⟩ := by decide
  have hnotInt :
      ¬ ∃ m : Int, (periodicPoint [1, 1, 1, 1, 4] (by decide)).Equiv (OddDenomRat.ofInt m) := by
    rintro ⟨m, hm⟩; rw [hx] at hm
    unfold OddDenomRat.Equiv OddDenomRat.ofInt at hm; simp only at hm; omega
  have havoid := OddDenomRat.cycle_avoids_one hcyc (fun h1 => hnotInt ⟨1, h1⟩)
  refine ⟨hx, by rw [hx]; decide, hcyc, hvec, hcol, hnotInt, fun j hj => ⟨?_, havoid j hj⟩⟩
  rw [syracuseIter_periodicPoint j hv]
  exact periodicPoint_num_pos (rotateLeft_valid j hv)
    (by rw [rotateLeft_periodicPointDen]; decide)

end SolveCollatz
