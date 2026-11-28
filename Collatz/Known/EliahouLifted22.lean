/-
Copyright (c) 2026 The solve-collatz contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Collatz.Known.EliahouLifted

/-!
# Lifted Unconditional Eliahou Cycle Bounds to `2^22` (`KNOWN-003` Phase 4)

Formalization in pure Lean 4 core (zero Mathlib, zero `sorry`, zero `native_decide`):
1. Kernel-fast 4-step affine table (`step4`) and 8-step chained Terras descent checker (`drop4x2`)
   via primitive `Bool.casesOn` and `Nat.rec`, with full soundness (`step4_eq`, `drop4x2_sound`).
2. Split dyadic modular descent tree (`checkTop`, `checkMid`, `checkMid20`, `checkLeaf21`)
   filtering mod-`4096` buckets at `k = 12`, skipping `[2, 2^20)` via
   `EliahouLifted.small_lt_1048576_finiteStoppingTime`, and certifying all surviving numbers in
   `[2^20, 2^22)` across 8 balanced mod-`4096` buckets purely in Lean's kernel (`by decide`).
3. **Unconditional Small-`n` Completion up to `2^22 = 4,194,304`:**
   `HasFiniteStoppingTime n` for all `2 ≤ n < 4194304`, lifting `4194304 ≤ C.n_min`.
4. **Flagship Unconditional Cycle-Length Lower Bounds (ZERO external hypotheses):**
   every non-trivial positive `SyracuseCycle` (`m` arbitrary) satisfies `4194304 ≤ C.n_min`,
   `7621 ≤ C.k`, `12079 ≤ C.totalVal`, and `19700 ≤ C.k + C.totalVal` (`2.57x` leap over `2^20`),
   proved via Eliahou's continued-fraction semiconvergent chain (`c = 4..10`, `11025 / 6956`)
   and bridged directly to frozen `Challenge.HasNontrivialCycle`.
5. Explicit **Barrier 1–5 separations** (`3n - 1`, `5n + 1`, `ℤ_{<0}`, `ℤ₂`, Conway horizon).
-/

@[expose] public section

namespace SolveCollatz

/-! ### 1. Kernel-Fast 4-Step Affine Table (`step4`) & 8-Step Descent (`drop4x2`) -/

/-- 4-step Terras transition `step4 c = terrasIter 4 c` via `c / 16` and `c % 16`. -/
def step4 (c : Nat) : Nat :=
  let q := Nat.div c 16
  let r := Nat.mod c 16
  Bool.casesOn (Nat.ble r 7)
    (Bool.casesOn (Nat.ble r 11)
      (Bool.casesOn (Nat.ble r 13)
        (Bool.casesOn (Nat.beq r 15) (Nat.add (Nat.mul 27 q) 26) (Nat.add (Nat.mul 81 q) 80))
        (Nat.add (Nat.mul 9 q) 8))
      (Bool.casesOn (Nat.ble r 9)
        (Bool.casesOn (Nat.beq r 11) (Nat.add (Nat.mul 3 q) 2) (Nat.add (Nat.mul 27 q) 20))
        (Bool.casesOn (Nat.beq r 9) (Nat.add (Nat.mul 3 q) 2) (Nat.add (Nat.mul 27 q) 17))))
    (Bool.casesOn (Nat.ble r 3)
      (Bool.casesOn (Nat.ble r 5)
        (Bool.casesOn (Nat.beq r 7) (Nat.add (Nat.mul 9 q) 4) (Nat.add (Nat.mul 27 q) 13))
        (Nat.add (Nat.mul 3 q) 1))
      (Bool.casesOn (Nat.ble r 1)
        (Nat.add (Nat.mul 9 q) 2)
        (Bool.casesOn (Nat.beq r 1) q (Nat.add (Nat.mul 9 q) 1))))

/-- Equivalence of `step4`'s affine table with `terrasIter 4 r + 3^c * q` for `r < 16`. -/
private theorem step4_eq_aux (r : Nat) (hr : r < 16) (q : Nat) :
    Bool.casesOn (Nat.ble r 7)
      (Bool.casesOn (Nat.ble r 11)
        (Bool.casesOn (Nat.ble r 13)
          (Bool.casesOn (Nat.beq r 15) (Nat.add (Nat.mul 27 q) 26) (Nat.add (Nat.mul 81 q) 80))
          (Nat.add (Nat.mul 9 q) 8))
        (Bool.casesOn (Nat.ble r 9)
          (Bool.casesOn (Nat.beq r 11) (Nat.add (Nat.mul 3 q) 2) (Nat.add (Nat.mul 27 q) 20))
          (Bool.casesOn (Nat.beq r 9) (Nat.add (Nat.mul 3 q) 2) (Nat.add (Nat.mul 27 q) 17))))
      (Bool.casesOn (Nat.ble r 3)
        (Bool.casesOn (Nat.ble r 5)
          (Bool.casesOn (Nat.beq r 7) (Nat.add (Nat.mul 9 q) 4) (Nat.add (Nat.mul 27 q) 13))
          (Nat.add (Nat.mul 3 q) 1))
        (Bool.casesOn (Nat.ble r 1)
          (Nat.add (Nat.mul 9 q) 2)
          (Bool.casesOn (Nat.beq r 1) q (Nat.add (Nat.mul 9 q) 1)))) =
      terrasIter 4 r + 3 ^ countOnes (terrasParityVec 4 r) * q := by
  match r with
  | 0 => change q = 0 + 1 * q; omega
  | 1 => change 9 * q + 1 = 1 + 9 * q; omega
  | 2 => change 9 * q + 2 = 2 + 9 * q; omega
  | 3 => change 9 * q + 2 = 2 + 9 * q; omega
  | 4 => change 3 * q + 1 = 1 + 3 * q; omega
  | 5 => change 3 * q + 1 = 1 + 3 * q; omega
  | 6 => change 9 * q + 4 = 4 + 9 * q; omega
  | 7 => change 27 * q + 13 = 13 + 27 * q; omega
  | 8 => change 3 * q + 2 = 2 + 3 * q; omega
  | 9 => change 27 * q + 17 = 17 + 27 * q; omega
  | 10 => change 3 * q + 2 = 2 + 3 * q; omega
  | 11 => change 27 * q + 20 = 20 + 27 * q; omega
  | 12 => change 9 * q + 8 = 8 + 9 * q; omega
  | 13 => change 9 * q + 8 = 8 + 9 * q; omega
  | 14 => change 27 * q + 26 = 26 + 27 * q; omega
  | 15 => change 81 * q + 80 = 80 + 81 * q; omega
  | _ + 16 => omega

/-- Exact equivalence `step4 c = terrasIter 4 c`. -/
theorem step4_eq (c : Nat) : step4 c = terrasIter 4 c := by
  have h := step4_eq_aux (c % 16) (Nat.mod_lt c (by decide)) (c / 16)
  change Bool.casesOn (Nat.ble (c % 16) 7) _ _ = terrasIter 4 c
  rw [terrasIter_mod_eq 4 c, ← terrasParityVec_mod_eq 4 c]
  exact h

/-- 8-step chained Terras descent checker (`2 × step4` per iteration) using `Bool.casesOn`. -/
def drop4x2 (target fuel cur : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => false)
    (fun _ ih c =>
      let c4 := step4 c
      Bool.casesOn (Nat.ble target c4) true
        (let c8 := step4 c4
         Bool.casesOn (Nat.ble target c8) true (ih c8)))
    fuel cur

/-- Helper extracting `HasFiniteStoppingTime n` from `Nat.ble n (terrasIter j n) = false`. -/
private theorem stop_of_ble_false {n j : Nat} (hj : 0 < j)
    (hb : Nat.ble n (terrasIter j n) = false) : HasFiniteStoppingTime n := by
  have hlt : terrasIter j n < n := by
    have hnot : ¬ n ≤ terrasIter j n := fun hle => by
      rw [Nat.ble_eq.mpr hle] at hb; exact absurd hb (by decide)
    omega
  exact hasFiniteStoppingTime_of_terras_lt hj hlt

/-- Soundness of `drop4x2`: `drop4x2 n fuel (terrasIter j n) = true` implies
`HasFiniteStoppingTime n`. -/
theorem drop4x2_sound {n : Nat} (fuel j : Nat)
    (h : drop4x2 n fuel (terrasIter j n) = true) : HasFiniteStoppingTime n := by
  induction fuel generalizing j with
  | zero => exact absurd h Bool.false_ne_true
  | succ fuel ih =>
    have h4 : step4 (terrasIter j n) = terrasIter (j + 4) n := by
      rw [step4_eq, terrasIter_add]
    have h8 : step4 (terrasIter (j + 4) n) = terrasIter (j + 8) n := by
      rw [step4_eq, terrasIter_add]
    unfold drop4x2 at h; dsimp only at h
    rw [h4] at h
    cases hb4 : Nat.ble n (terrasIter (j + 4) n)
    · exact stop_of_ble_false (by omega) hb4
    · rw [hb4] at h; dsimp only at h; rw [h8] at h
      cases hb8 : Nat.ble n (terrasIter (j + 8) n)
      · exact stop_of_ble_false (by omega) hb8
      · rw [hb8] at h; dsimp only at h
        exact ih (j + 8) h

/-! ### 2. Split Dyadic Modular Descent Tree (`checkTop` / `checkMid`) & Soundness -/

/-- Modular affine pruning guard: `p3 < p2` and `cur + p3 < r + p2`. -/
def isPruned (r cur p3 p2 : Nat) : Bool :=
  Bool.casesOn (Nat.ble (Nat.add p3 1) p2) false
    (Nat.ble (Nat.add (Nat.add cur p3) 1) (Nat.add r p2))

/-- Equivalence of `isPruned r cur p3 p2 = true` with `p3 < p2 ∧ cur + p3 < r + p2`. -/
theorem isPruned_iff (r cur p3 p2 : Nat) :
    isPruned r cur p3 p2 = true ↔ p3 < p2 ∧ cur + p3 < r + p2 := by
  unfold isPruned
  cases hb : Nat.ble (Nat.add p3 1) p2
  · simp only [Bool.false_eq_true, false_iff]
    intro ⟨h1, _⟩
    have hle : Nat.ble (Nat.add p3 1) p2 = true := Nat.ble_eq.mpr (by change p3 + 1 ≤ p2; omega)
    rw [hb] at hle; exact absurd hle Bool.false_ne_true
  · have h32 : p3 < p2 := by
      rw [Nat.ble_eq] at hb; change p3 + 1 ≤ p2 at hb; omega
    simp only [Nat.ble_eq]
    change cur + p3 + 1 ≤ r + p2 ↔ p3 < p2 ∧ cur + p3 < r + p2
    omega

/-- Branching step expanding a non-pruned residue `(r, cur, p3, p2)` to its two children. -/
def stepChildren (ih : Nat → Nat → Nat → Nat → Bool) (r cur p3 p2 : Nat) : Bool :=
  Bool.casesOn (isPruned r cur p3 p2)
    (let p2' := Nat.mul 2 p2
     let cp3 := Nat.add cur p3
     let rp2 := Nat.add r p2
     Bool.casesOn (Nat.beq (Nat.mod cur 2) 0)
       (Bool.casesOn (ih r (Nat.div (Nat.add (Nat.mul 3 cur) 1) 2) (Nat.mul 3 p3) p2')
         false (ih rp2 (Nat.div cp3 2) p3 p2'))
       (Bool.casesOn (ih r (Nat.div cur 2) p3 p2')
         false (ih rp2 (Nat.div (Nat.add (Nat.mul 3 cp3) 1) 2) (Nat.mul 3 p3) p2')))
    true

/-- Leaf checker at `k = 21` covering shell `[2^21, 2^22)`. -/
def checkLeaf (fuel r cur p3 p2 : Nat) : Bool :=
  Bool.casesOn (isPruned r cur p3 p2)
    (drop4x2 (Nat.add r p2) fuel (Nat.add cur p3))
    true

/-- Shell checker at `k = 20` covering `[2^20, 2^21)` and descending to `checkLeaf`. -/
def checkMid20 (fuel r cur p3 p2 : Nat) : Bool :=
  Bool.casesOn (isPruned r cur p3 p2)
    (Bool.casesOn (drop4x2 (Nat.add r p2) fuel (Nat.add cur p3)) false
      (stepChildren (checkLeaf fuel) r cur p3 p2))
    true

/-- Middle tree walker from `k = 12` to `k = 20` (`rem = 8`). -/
def checkMid (fuel rem r cur p3 p2 : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Bool)
    (checkMid20 fuel) (fun _ ih => stepChildren ih) rem r cur p3 p2

/-- Top tree walker from `k = 1` to `k = 12` (`rem = 11`), filtering `[lo, hi) mod 4096`. -/
def checkTop (lo hi fuel rem r cur p3 p2 : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Bool)
    (fun r cur p3 p2 =>
      Bool.casesOn (Nat.ble lo r) true
        (Bool.casesOn (Nat.ble (Nat.add r 1) hi) true (checkMid fuel 8 r cur p3 p2)))
    (fun _ ih => stepChildren ih) rem r cur p3 p2

/-- Pruned residue class soundness: `0 < k`, `3^c < 2^k`, and `terrasIter k r + 3^c < r + 2^k`
forces `HasFiniteStoppingTime n` for every `n ≥ 2^k` with `n % 2^k = r`. -/
theorem terras_drop_of_pruned {k r n : Nat} (hk : 0 < k) (hmod : n % 2 ^ k = r)
    (hn : 2 ^ k ≤ n) (hp : 3 ^ countOnes (terrasParityVec k r) < 2 ^ k)
    (hdrop : terrasIter k r + 3 ^ countOnes (terrasParityVec k r) < r + 2 ^ k) :
    HasFiniteStoppingTime n := by
  let q := n / 2 ^ k
  have hq : 1 ≤ q := Nat.div_pos hn (Nat.two_pow_pos k)
  have hiter : terrasIter k n =
      terrasIter k r + 3 ^ countOnes (terrasParityVec k r) * q := by
    rw [terrasIter_mod_eq k n, ← terrasParityVec_mod_eq k n, hmod]
  have hmul : 3 ^ countOnes (terrasParityVec k r) * (q - 1) ≤ 2 ^ k * (q - 1) :=
    Nat.mul_le_mul_right (q - 1) (Nat.le_of_lt hp)
  have hlt : terrasIter k n < n := by
    have hdecomp : r + 2 ^ k * q = n := by rw [← hmod]; exact Nat.mod_add_div n (2 ^ k)
    rw [hiter, ← hdecomp, show q = 1 + (q - 1) by omega, Nat.mul_add, Nat.mul_one,
      Nat.mul_add, Nat.mul_one]
    omega
  exact hasFiniteStoppingTime_of_terras_lt hk hlt

/-- Exact shell identity: for `2^k ≤ n < 2^(k + 1)` with `n % 2^k = r`, we have
`n = r + 2^k` and `terrasIter k n = terrasIter k r + 3^c`. -/
theorem terras_shell_eq {k r n : Nat} (hmod : n % 2 ^ k = r)
    (hlo : 2 ^ k ≤ n) (hhi : n < 2 ^ (k + 1)) :
    n = r + 2 ^ k ∧ terrasIter k n = terrasIter k r + 3 ^ countOnes (terrasParityVec k r) := by
  have hkpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
  have hq : n / 2 ^ k = 1 := by
    have h1 : 1 ≤ n / 2 ^ k := Nat.div_pos hlo hkpos
    have h2 : n / 2 ^ k < 2 := (Nat.div_lt_iff_lt_mul hkpos).mpr (by rw [← hpow]; exact hhi)
    omega
  have hn_eq : n = r + 2 ^ k := by
    have hd := (Nat.mod_add_div n (2 ^ k)).symm
    rw [hmod, hq, Nat.mul_one] at hd; exact hd
  have hiter : terrasIter k n = terrasIter k r + 3 ^ countOnes (terrasParityVec k r) := by
    rw [terrasIter_mod_eq k n, ← terrasParityVec_mod_eq k n, hmod, hq, Nat.mul_one]
  exact ⟨hn_eq, hiter⟩

/-- Left-child parity/iterate update for `r` at depth `k + 1`. -/
theorem terras_child_left (k r : Nat) :
    (terrasIter k r % 2 = 0 →
      terrasIter (k + 1) r = terrasIter k r / 2 ∧
      3 ^ countOnes (terrasParityVec (k + 1) r) = 3 ^ countOnes (terrasParityVec k r)) ∧
    (terrasIter k r % 2 ≠ 0 →
      terrasIter (k + 1) r = (3 * terrasIter k r + 1) / 2 ∧
      3 ^ countOnes (terrasParityVec (k + 1) r) = 3 * 3 ^ countOnes (terrasParityVec k r)) := by
  have hvec : terrasParityVec (k + 1) r =
      terrasParityVec k r ++ [(terrasIter k r % 2 == 1)] := by
    simpa [terrasParityVec] using terrasParityVec_add k 1 r
  constructor
  · intro heven
    have hbool : (terrasIter k r % 2 == 1) = false := by
      cases hb : (terrasIter k r % 2 == 1)
      · rfl
      · exact absurd (beq_iff_eq.mp hb) (by omega)
    rw [terrasIter_succ_right, terrasStep_even heven, hvec, countOnes_append, hbool]
    simp [countOnes]
  · intro hne
    have hodd : terrasIter k r % 2 = 1 := by omega
    have hbool : (terrasIter k r % 2 == 1) = true := beq_iff_eq.mpr hodd
    rw [terrasIter_succ_right, terrasStep_odd hodd, hvec, countOnes_append, hbool]
    simp [countOnes, Nat.pow_succ, Nat.mul_comm]

/-- Right-child parity/iterate update for `r + 2^k` at depth `k + 1`. -/
theorem terras_child_right (k r : Nat) :
    let cp3 := terrasIter k r + 3 ^ countOnes (terrasParityVec k r)
    let p3 := 3 ^ countOnes (terrasParityVec k r)
    (terrasIter k r % 2 = 0 →
      terrasIter (k + 1) (r + 2 ^ k) = (3 * cp3 + 1) / 2 ∧
      3 ^ countOnes (terrasParityVec (k + 1) (r + 2 ^ k)) = 3 * p3) ∧
    (terrasIter k r % 2 ≠ 0 →
      terrasIter (k + 1) (r + 2 ^ k) = cp3 / 2 ∧
      3 ^ countOnes (terrasParityVec (k + 1) (r + 2 ^ k)) = p3) := by
  have hcong := terrasParityVec_mod_two_pow k r 1
  rw [Nat.mul_one] at hcong
  have h3odd : (3 ^ countOnes (terrasParityVec k r)) % 2 = 1 := by
    induction countOnes (terrasParityVec k r) with
    | zero => rfl
    | succ c ih => rw [Nat.pow_succ]; omega
  have hvec : terrasParityVec (k + 1) (r + 2 ^ k) =
      terrasParityVec k (r + 2 ^ k) ++ [(terrasIter k (r + 2 ^ k) % 2 == 1)] := by
    simpa [terrasParityVec] using terrasParityVec_add k 1 (r + 2 ^ k)
  constructor
  · intro heven
    have hodd : terrasIter k (r + 2 ^ k) % 2 = 1 := by rw [hcong.2]; omega
    have hbool : (terrasIter k (r + 2 ^ k) % 2 == 1) = true := beq_iff_eq.mpr hodd
    rw [terrasIter_succ_right, terrasStep_odd hodd, hcong.2, hvec, countOnes_append,
      hcong.1, hbool]
    simp [countOnes, Nat.pow_succ, Nat.mul_comm]
  · intro hne
    have heven' : terrasIter k (r + 2 ^ k) % 2 = 0 := by rw [hcong.2]; omega
    have hbool : (terrasIter k (r + 2 ^ k) % 2 == 1) = false := by
      cases hb : (terrasIter k (r + 2 ^ k) % 2 == 1)
      · rfl
      · exact absurd (beq_iff_eq.mp hb) (by omega)
    rw [terrasIter_succ_right, terrasStep_even heven', hcong.2, hvec, countOnes_append,
      hcong.1, hbool]
    simp [countOnes]

/-- Helper unpacking `n % 2^(k + 1)` into `n % 2^k` or `n % 2^k + 2^k`. -/
theorem mod_two_pow_succ_split (n k : Nat) :
    n % 2 ^ (k + 1) = n % 2 ^ k ∨ n % 2 ^ (k + 1) = n % 2 ^ k + 2 ^ k := by
  have hkpos := Nat.two_pow_pos k
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
  have hd := (Nat.mod_add_div n (2 ^ k)).symm
  have hd2 := (Nat.mod_add_div (n / 2 ^ k) 2).symm
  have hlt := Nat.mod_lt n hkpos
  rw [hpow]
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ k) with h0 | h1
  · left
    have heq : n = n % 2 ^ k + (2 * 2 ^ k) * (n / 2 ^ k / 2) := by
      conv => lhs; rw [hd, hd2, h0, Nat.zero_add, Nat.mul_left_comm (2 ^ k) 2, ← Nat.mul_assoc]
    conv => lhs; rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  · right
    have heq : n = (n % 2 ^ k + 2 ^ k) + (2 * 2 ^ k) * (n / 2 ^ k / 2) := by
      conv => lhs; rw [hd, hd2, h1, Nat.mul_add, Nat.mul_one, Nat.mul_left_comm (2 ^ k) 2,
        ← Nat.mul_assoc, ← Nat.add_assoc]
    conv => lhs; rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- Soundness of `stepChildren` when `isPruned = false`. -/
theorem stepChildren_children_sound (ih : Nat → Nat → Nat → Nat → Bool) (k r : Nat)
    (hbranch : (let p2' := Nat.mul 2 (2 ^ k)
      let cp3 := Nat.add (terrasIter k r) (3 ^ countOnes (terrasParityVec k r))
      let rp2 := Nat.add r (2 ^ k)
      Bool.casesOn (Nat.beq (Nat.mod (terrasIter k r) 2) 0)
        (Bool.casesOn (ih r (Nat.div (Nat.add (Nat.mul 3 (terrasIter k r)) 1) 2)
            (Nat.mul 3 (3 ^ countOnes (terrasParityVec k r))) p2')
          false (ih rp2 (Nat.div cp3 2) (3 ^ countOnes (terrasParityVec k r)) p2'))
        (Bool.casesOn (ih r (Nat.div (terrasIter k r) 2)
            (3 ^ countOnes (terrasParityVec k r)) p2')
          false (ih rp2 (Nat.div (Nat.add (Nat.mul 3 cp3) 1) 2)
            (Nat.mul 3 (3 ^ countOnes (terrasParityVec k r))) p2'))) = true) :
    ih r (terrasIter (k + 1) r) (3 ^ countOnes (terrasParityVec (k + 1) r)) (2 ^ (k + 1)) = true ∧
    ih (r + 2 ^ k) (terrasIter (k + 1) (r + 2 ^ k))
      (3 ^ countOnes (terrasParityVec (k + 1) (r + 2 ^ k))) (2 ^ (k + 1)) = true := by
  have h2pow : Nat.mul 2 (2 ^ k) = 2 ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_comm]; rfl
  by_cases hev : terrasIter k r % 2 = 0
  · have hbeq : Nat.beq (Nat.mod (terrasIter k r) 2) 0 = true := Nat.beq_eq.mpr hev
    rw [hbeq] at hbranch; dsimp only at hbranch
    cases hL : ih r (Nat.div (terrasIter k r) 2)
        (3 ^ countOnes (terrasParityVec k r)) (Nat.mul 2 (2 ^ k))
    · rw [hL] at hbranch; exact absurd hbranch Bool.false_ne_true
    · rw [hL] at hbranch; dsimp only at hbranch
      rcases (terras_child_left k r).1 hev with ⟨h1, h2⟩
      rcases (terras_child_right k r).1 hev with ⟨h3, h4⟩
      rw [h1, h2, h3, h4, ← h2pow]; exact ⟨hL, hbranch⟩
  · have hbeq : Nat.beq (Nat.mod (terrasIter k r) 2) 0 = false := by
      cases hq : Nat.beq (Nat.mod (terrasIter k r) 2) 0
      · rfl
      · exact absurd (Nat.beq_eq.mp hq) hev
    rw [hbeq] at hbranch; dsimp only at hbranch
    cases hL : ih r (Nat.div (Nat.add (Nat.mul 3 (terrasIter k r)) 1) 2)
        (Nat.mul 3 (3 ^ countOnes (terrasParityVec k r))) (Nat.mul 2 (2 ^ k))
    · rw [hL] at hbranch; exact absurd hbranch Bool.false_ne_true
    · rw [hL] at hbranch; dsimp only at hbranch
      rcases (terras_child_left k r).2 hev with ⟨h1, h2⟩
      rcases (terras_child_right k r).2 hev with ⟨h3, h4⟩
      rw [h1, h2, h3, h4, ← h2pow]; exact ⟨hL, hbranch⟩

/-- Full soundness of `stepChildren` for `0 < k` and `n ≥ 2^(k + 1)` with invariant `P`. -/
theorem stepChildren_sound (M : Nat) (P : Nat → Prop) (ih : Nat → Nat → Nat → Nat → Bool)
    {k : Nat} (hih : ∀ r' : Nat, r' < 2 ^ (k + 1) →
      ih r' (terrasIter (k + 1) r')
        (3 ^ countOnes (terrasParityVec (k + 1) r')) (2 ^ (k + 1)) = true →
      ∀ n : Nat, P n → 2 ^ (k + 1) ≤ n → n < M → n % 2 ^ (k + 1) = r' →
        HasFiniteStoppingTime n)
    (hk : 0 < k) (r : Nat) (hr : r < 2 ^ k)
    (hstep : stepChildren ih r (terrasIter k r)
      (3 ^ countOnes (terrasParityVec k r)) (2 ^ k) = true) :
    ∀ n : Nat, P n → 2 ^ (k + 1) ≤ n → n < M → n % 2 ^ k = r →
      HasFiniteStoppingTime n := by
  intro n hPn hnk1 hnM hmod
  unfold stepChildren at hstep
  cases hp : isPruned r (terrasIter k r) (3 ^ countOnes (terrasParityVec k r)) (2 ^ k)
  · rw [hp] at hstep; dsimp only at hstep
    rcases stepChildren_children_sound ih k r hstep with ⟨hL, hR⟩
    have hpow1 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    rcases mod_two_pow_succ_split n k with hleft | hright
    · rw [hmod] at hleft
      exact hih r (by omega) hL n hPn hnk1 hnM hleft
    · rw [hmod] at hright
      exact hih (r + 2 ^ k) (by omega) hR n hPn hnk1 hnM hright
  · rcases (isPruned_iff _ _ _ _).mp hp with ⟨h32, hlt⟩
    have hnk : 2 ^ k ≤ n := Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hnk1
    exact terras_drop_of_pruned hk hmod hnk h32 hlt

/-- Soundness of `checkLeaf` on `[2^k, 2^(k + 1))`. -/
theorem checkLeaf_sound (fuel k r : Nat) (hk : 0 < k)
    (hchk : checkLeaf fuel r (terrasIter k r)
      (3 ^ countOnes (terrasParityVec k r)) (2 ^ k) = true) :
    ∀ n : Nat, 2 ^ k ≤ n → n < 2 ^ (k + 1) → n % 2 ^ k = r → HasFiniteStoppingTime n := by
  intro n hnk hnk1 hmod
  unfold checkLeaf at hchk
  cases hp : isPruned r (terrasIter k r) (3 ^ countOnes (terrasParityVec k r)) (2 ^ k)
  · rw [hp] at hchk; dsimp only at hchk
    rcases terras_shell_eq hmod hnk hnk1 with ⟨hn_eq, hiter⟩
    have hn_eq' : Nat.add r (2 ^ k) = n := hn_eq.symm
    have hiter' : Nat.add (terrasIter k r) (3 ^ countOnes (terrasParityVec k r)) =
        terrasIter k n := hiter.symm
    rw [hn_eq', hiter'] at hchk
    exact drop4x2_sound fuel k hchk
  · rcases (isPruned_iff _ _ _ _).mp hp with ⟨h32, hlt⟩
    exact terras_drop_of_pruned hk hmod hnk h32 hlt

/-- Soundness of `checkMid20` on `[2^k, 2^(k + 2))`. -/
private theorem checkMid20_sound (fuel k r : Nat) (hk : 0 < k) (hr : r < 2 ^ k)
    (hchk : checkMid20 fuel r (terrasIter k r)
      (3 ^ countOnes (terrasParityVec k r)) (2 ^ k) = true) :
    ∀ n : Nat, 2 ^ k ≤ n → n < 2 ^ (k + 2) → n % 2 ^ k = r → HasFiniteStoppingTime n := by
  intro n hnk hnk2 hmod
  unfold checkMid20 at hchk
  cases hp : isPruned r (terrasIter k r) (3 ^ countOnes (terrasParityVec k r)) (2 ^ k)
  · rw [hp] at hchk; dsimp only at hchk
    cases hdrop : drop4x2 (Nat.add r (2 ^ k)) fuel
        (Nat.add (terrasIter k r) (3 ^ countOnes (terrasParityVec k r)))
    · rw [hdrop] at hchk; exact absurd hchk Bool.false_ne_true
    · rw [hdrop] at hchk; dsimp only at hchk
      by_cases hlt1 : n < 2 ^ (k + 1)
      · rcases terras_shell_eq hmod hnk hlt1 with ⟨hn_eq, hiter⟩
        have hn_eq' : Nat.add r (2 ^ k) = n := hn_eq.symm
        have hiter' : Nat.add (terrasIter k r) (3 ^ countOnes (terrasParityVec k r)) =
            terrasIter k n := hiter.symm
        rw [hn_eq', hiter'] at hdrop
        exact drop4x2_sound fuel k hdrop
      · have hge1 : 2 ^ (k + 1) ≤ n := Nat.le_of_not_lt hlt1
        exact stepChildren_sound (2 ^ (k + 2)) (fun _ => True) (checkLeaf fuel)
          (fun r' _ h' n' _ h1 h2 hm =>
            checkLeaf_sound fuel (k + 1) r' (by omega) h' n' h1 h2 hm)
          hk r hr hchk n True.intro hge1 hnk2 hmod
  · rcases (isPruned_iff _ _ _ _).mp hp with ⟨h32, hlt⟩
    exact terras_drop_of_pruned hk hmod hnk h32 hlt

/-- Soundness of `checkMid` on `[2^(k + rem), 2^(k + rem + 2))` (`0 < k`). -/
private theorem checkMid_sound (fuel rem : Nat) :
    ∀ k r : Nat, 0 < k → r < 2 ^ k →
      checkMid fuel rem r (terrasIter k r)
        (3 ^ countOnes (terrasParityVec k r)) (2 ^ k) = true →
      ∀ n : Nat, 2 ^ (k + rem) ≤ n → n < 2 ^ (k + rem + 2) → n % 2 ^ k = r →
        HasFiniteStoppingTime n := by
  induction rem with
  | zero =>
    intro k r hk hr hchk n hn1 hn2 hmod
    exact checkMid20_sound fuel k r hk hr hchk n hn1 hn2 hmod
  | succ rem ih =>
    intro k r hk hr hchk n hn1 hn2 hmod
    have hnk1 : 2 ^ (k + 1) ≤ n :=
      Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hn1
    have h1 : 2 ^ (k + 1 + rem) ≤ n := by simpa [Nat.add_assoc, Nat.add_comm 1 rem] using hn1
    have h2 : n < 2 ^ (k + 1 + rem + 2) := by
      simpa [Nat.add_assoc, Nat.add_comm 1 rem] using hn2
    exact stepChildren_sound (2 ^ (k + rem.succ + 2)) (fun m => 2 ^ (k + rem.succ) ≤ m)
      (checkMid fuel rem)
      (fun r' hr' h' n' hP _ hn2' hm =>
        ih (k + 1) r' (by omega) hr' h' n'
          (by simpa [Nat.add_assoc, Nat.add_comm 1 rem] using hP)
          (by simpa [Nat.add_assoc, Nat.add_comm 1 rem] using hn2') hm)
      hk r hr hchk n hn1 hnk1 hn2 hmod

/-- Soundness of `checkTop` from `k = 12 - rem` (`k + rem = 12`, `0 < k`) for bucket `[lo, hi)`. -/
private theorem checkTop_sound (lo hi fuel rem : Nat) :
    ∀ k r : Nat, 0 < k → k + rem = 12 → r < 2 ^ k →
      checkTop lo hi fuel rem r (terrasIter k r)
        (3 ^ countOnes (terrasParityVec k r)) (2 ^ k) = true →
      ∀ n : Nat, 2 ^ 20 ≤ n → n < 2 ^ 22 → n % 2 ^ k = r →
        lo ≤ n % 4096 → n % 4096 < hi → HasFiniteStoppingTime n := by
  induction rem with
  | zero =>
    intro k r _ hsum hr hchk n hn20 hn22 hmod hn_lo hn_hi
    have hk12 : k = 12 := by omega
    subst hk12
    have h4096 : (2 ^ 12 : Nat) = 4096 := by decide
    rw [h4096] at hmod
    change Bool.casesOn (Nat.ble lo r) true (Bool.casesOn (Nat.ble (Nat.add r 1) hi) true
      (checkMid fuel 8 r (terrasIter 12 r)
        (3 ^ countOnes (terrasParityVec 12 r)) (2 ^ 12))) = true at hchk
    have hb1 : Nat.ble lo r = true := Nat.ble_eq.mpr (by omega)
    have hb2 : Nat.ble (Nat.add r 1) hi = true := Nat.ble_eq.mpr (by change r + 1 ≤ hi; omega)
    rw [hb1, hb2] at hchk; dsimp only at hchk
    rw [← h4096] at hmod
    exact checkMid_sound fuel 8 12 r (by decide) hr hchk n hn20 hn22 hmod
  | succ rem ih =>
    intro k r hk hsum hr hchk n hn20 hn22 hmod hn_lo hn_hi
    have hnk1 : 2 ^ (k + 1) ≤ n :=
      Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hn20
    exact stepChildren_sound (2 ^ 22) (fun m => 2 ^ 20 ≤ m ∧ lo ≤ m % 4096 ∧ m % 4096 < hi)
      (checkTop lo hi fuel rem)
      (fun r' hr' h' n' hP _ hn22' hm =>
        ih (k + 1) r' (by omega) (by omega) hr' h' n' hP.1 hn22' hm hP.2.1 hP.2.2)
      hk r hr hchk n ⟨hn20, hn_lo, hn_hi⟩ hnk1 hn22 hmod

/-! ### 3. Kernel Certificates up to `2^22 = 4,194,304` & Unconditional `n_min ≥ 4194304` -/

private theorem shell22_b0 : checkTop    0  496 35 11 1 2 3 2 = true := by decide
private theorem shell22_b1 : checkTop  496 1024 35 11 1 2 3 2 = true := by decide
private theorem shell22_b2 : checkTop 1024 1536 35 11 1 2 3 2 = true := by decide
private theorem shell22_b3 : checkTop 1536 2140 35 11 1 2 3 2 = true := by decide
private theorem shell22_b4 : checkTop 2140 2688 35 11 1 2 3 2 = true := by decide
private theorem shell22_b5 : checkTop 2688 3184 35 11 1 2 3 2 = true := by decide
private theorem shell22_b6 : checkTop 3184 3688 35 11 1 2 3 2 = true := by decide
private theorem shell22_b7 : checkTop 3688 4096 35 11 1 2 3 2 = true := by decide

/-- Helper applying `checkTop_sound` at root `(k = 1, r = 1, rem = 11)` for bucket `[lo, hi)`. -/
private theorem shell22_bucket_sound (lo hi : Nat)
    (hchk : checkTop lo hi 35 11 1 2 3 2 = true) {n : Nat} (hodd : n % 2 = 1)
    (hlo : 1048576 ≤ n) (hhi : n < 4194304) (hbl : lo ≤ n % 4096) (hbh : n % 4096 < hi) :
    HasFiniteStoppingTime n :=
  checkTop_sound lo hi 35 11 1 1 (by decide) (by decide) (by decide)
    (by simpa [terrasIter, terrasStep, terrasParityVec, countOnes] using hchk)
    n (by simpa using hlo) (by simpa using hhi) (by simpa using hodd) hbl hbh

/-- **Unconditional Small-`n` Completion (`2 ≤ n < 4194304 = 2^22`):**
every integer `2 ≤ n < 4194304` has finite Terras stopping time (reusing `EliahouLifted` for
`< 2^20` and pure kernel `decide` across 8 mod-`4096` buckets for `[2^20, 2^22)`). -/
theorem small_lt_4194304_finiteStoppingTime {n : Nat} (hn2 : 2 ≤ n) (hn22 : n < 4194304) :
    HasFiniteStoppingTime n := by
  by_cases hlt : n < 1048576
  · exact small_lt_1048576_finiteStoppingTime hn2 hlt
  · by_cases hev : n % 2 = 0
    · have h1 : terrasIter 1 n = n / 2 := by simp [terrasIter, terrasStep, hev]
      exact hasFiniteStoppingTime_of_terras_lt (k := 1) (by decide) (by rw [h1]; omega)
    · have h1m : 1048576 ≤ n := by omega
      have hodd : n % 2 = 1 := by omega
      have hm : n % 4096 < 4096 := Nat.mod_lt n (by decide)
      by_cases h1 : n % 4096 < 496
      · exact shell22_bucket_sound 0 496 shell22_b0 hodd h1m hn22 (Nat.zero_le _) h1
      · by_cases h2 : n % 4096 < 1024
        · exact shell22_bucket_sound 496 1024 shell22_b1 hodd h1m hn22 (by omega) h2
        · by_cases h3 : n % 4096 < 1536
          · exact shell22_bucket_sound 1024 1536 shell22_b2 hodd h1m hn22 (by omega) h3
          · by_cases h4 : n % 4096 < 2140
            · exact shell22_bucket_sound 1536 2140 shell22_b3 hodd h1m hn22 (by omega) h4
            · by_cases h5 : n % 4096 < 2688
              · exact shell22_bucket_sound 2140 2688 shell22_b4 hodd h1m hn22 (by omega) h5
              · by_cases h6 : n % 4096 < 3184
                · exact shell22_bucket_sound 2688 3184 shell22_b5 hodd h1m hn22 (by omega) h6
                · by_cases h7 : n % 4096 < 3688
                  · exact shell22_bucket_sound 3184 3688 shell22_b6 hodd h1m hn22 (by omega) h7
                  · exact shell22_bucket_sound 3688 4096 shell22_b7 hodd h1m hn22 (by omega) hm

/-- **Unconditional Minimal-Element Lower Bound (`M = 2^22`):**
every non-trivial positive `SyracuseCycle` satisfies `4194304 ≤ C.n_min`. -/
theorem no_nontrivial_syracuseCycle_min_lt_4194304 (C : SyracuseCycle) : 4194304 ≤ C.n_min :=
  syracuseCycle_min_ge_of_stopping 4194304
    (fun _ hn2 hlt => small_lt_4194304_finiteStoppingTime hn2 hlt) C

/-- **Unconditional Cycle-Element Lower Bound (`Challenge.lean`, `M = 2^22`):**
every element `n` on a non-trivial positive Collatz cycle satisfies `4194304 ≤ n`. -/
theorem no_nontrivial_collatzCycle_min_lt_4194304 {n L : Nat} (hn : 0 < n) (hL : 0 < L)
    (hcyc : collatzIter L n = n) (hne : ∀ j : Nat, j < L → collatzIter j n ≠ 1) :
    4194304 ≤ n :=
  collatz_cycle_elem_ge_of_stopping 4194304
    (fun _ hn2 hlt => small_lt_4194304_finiteStoppingTime hn2 hlt) hn hL hcyc hne

/-! ### 4. Eliahou CF Semiconvergent Chain (`c = 4..10`) & Flagship Unconditional Bounds -/

/-- Certified `fastPow` witness for `M = 4194304` (`c = 10`, `pU/qU = 11025 / 6956`, `K ≥ 7621`). -/
private theorem cf_witness_4194304 :
    3 ^ 6956 < 2 ^ 11025 ∧
    6956 * 2 ^ 11025 ≤ (3 * 4194304 - (6956 + 665)) * (2 ^ 11025 - 3 ^ 6956) ∧
    2 ^ 12078 ≤ 3 ^ 7621 := by
  have h :
      fastPow 3 6956 < fastPow 2 11025 ∧
      6956 * fastPow 2 11025 ≤
          (3 * 4194304 - (6956 + 665)) * (fastPow 2 11025 - fastPow 3 6956) ∧
      fastPow 2 12078 ≤ fastPow 3 7621 := by decide
  rwa [fastPow_eq 3 6956 (by decide), fastPow_eq 2 11025 (by decide),
    fastPow_eq 2 12078 (by decide), fastPow_eq 3 7621 (by decide)] at h

/-- **Sharp Conditional Eliahou Bound (`M = 2^22 = 4194304`):** `4194304 ≤ C.n_min` forces
`7621 ≤ C.k`, `12079 ≤ C.totalVal`, and `19700 ≤ C.k + C.totalVal`. -/
theorem eliahou_cf_bounds_of_ge_4194304 (C : SyracuseCycle) (hM : 4194304 ≤ C.n_min) :
    7621 ≤ C.k ∧ 12079 ≤ C.totalVal ∧ 19700 ≤ C.k + C.totalVal := by
  have hk := eliahou_cf_elimination 4194304 1054 665 11025 6956 (by decide) (by decide)
    log2ThreeCF_lower_exps.2.2.2.2 cf_witness_4194304.1 (by decide) (by decide)
    cf_witness_4194304.2.1 C hM
  have hs := totalVal_ge_of_k_ge C 7621 12078 hk cf_witness_4194304.2.2
  have hl := collatzLen_ge_of_k_ge C 7621 12078 hk cf_witness_4194304.2.2
  exact ⟨hk, hs, by simpa [SyracuseCycle.collatzLen, Nat.add_comm] using hl⟩

/-- **Flagship Unconditional Combined Cycle-Length Bounds (ZERO hypotheses, `M = 2^22`):**
every non-trivial positive `SyracuseCycle` (`m` arbitrary) satisfies `4194304 ≤ C.n_min`,
`7621 ≤ C.k`, `12079 ≤ C.totalVal`, and `19700 ≤ C.k + C.totalVal`. -/
theorem unconditional_syracuseCycle_bounds_lifted22 (C : SyracuseCycle) :
    4194304 ≤ C.n_min ∧ 7621 ≤ C.k ∧ 12079 ≤ C.totalVal ∧ 19700 ≤ C.k + C.totalVal := by
  have hM := no_nontrivial_syracuseCycle_min_lt_4194304 C
  have hcf := eliahou_cf_bounds_of_ge_4194304 C hM
  exact ⟨hM, hcf.1, hcf.2.1, hcf.2.2⟩

/-- **Eliahou Semiconvergent Chain (`c = 4..10` for `M = 2^22`):** explicit unconditional odd-step
progression `3631..7621 ≤ C.k` along `(c * 1054 + 485)/(c * 665 + 306)` with Farey adjacency
`pU * 665 = 1054 * qU + 1`. -/
theorem eliahou_semiconvergent_chain_lifted22 (C : SyracuseCycle) :
    (∀ c : Nat, (c * 1054 + 485) * 665 = 1054 * (c * 665 + 306) + 1) ∧
    3631 ≤ C.k ∧ 4296 ≤ C.k ∧ 4961 ≤ C.k ∧ 5626 ≤ C.k ∧
    6291 ≤ C.k ∧ 6956 ≤ C.k ∧ 7621 ≤ C.k := by
  have hk := (unconditional_syracuseCycle_bounds_lifted22 C).2.1
  refine ⟨fun c => cf_semiconvergent_det (prev := (485, 306)) (cur := (1054, 665)) c (by decide),
    by omega, by omega, by omega, by omega, by omega, by omega, hk⟩

/-- **Flagship Unconditional Odd-Step Bound (`K ≥ 7621`, ZERO hypotheses):** -/
theorem unconditional_syracuseCycle_odd_length_ge_7621 (C : SyracuseCycle) : 7621 ≤ C.k :=
  (unconditional_syracuseCycle_bounds_lifted22 C).2.1

/-- **Flagship Unconditional Halving Bound (`S ≥ 12079`, ZERO hypotheses):** -/
theorem unconditional_syracuseCycle_halvings_ge_12079 (C : SyracuseCycle) : 12079 ≤ C.totalVal :=
  (unconditional_syracuseCycle_bounds_lifted22 C).2.2.1

/-- **Flagship Unconditional Total-Length Bound (`L ≥ 19700`, ZERO hypotheses):** -/
theorem unconditional_syracuseCycle_collatzLen_ge_19700 (C : SyracuseCycle) :
    19700 ≤ C.collatzLen := by
  have h := (unconditional_syracuseCycle_bounds_lifted22 C).2.2.2
  simpa [SyracuseCycle.collatzLen, Nat.add_comm] using h

/-- **Flagship Unconditional Bridge to Frozen `Challenge.lean` (`L ≥ 19700`):** -/
theorem unconditional_collatzCycle_length_ge_19700 {n L : Nat} (hn : 0 < n) (hL : 0 < L)
    (hcyc : collatzIter L n = n) (hne : ∀ j : Nat, j < L → collatzIter j n ≠ 1) :
    19700 ≤ L := by
  rcases exists_syracuseCycle_of_collatz_cycle hn hL hcyc hne with ⟨C, hlen⟩
  have h19700 := unconditional_syracuseCycle_collatzLen_ge_19700 C
  omega

/-- **Unconditional Decomposition Theorem for Frozen `HasNontrivialCycle` (`M = 2^22`):**
any `HasNontrivialCycle` witness yields `(n, K, S)` with `4194304 ≤ n`, `7621 ≤ K`,
`12079 ≤ S`, `19700 ≤ K + S`, and `collatzIter (K + S) n = n` avoiding `1`. -/
theorem unconditional_challenge_cycle_bounds_lifted22 (h : HasNontrivialCycle) :
    ∃ n K S : Nat, 4194304 ≤ n ∧ 7621 ≤ K ∧ 12079 ≤ S ∧ 19700 ≤ K + S ∧
      collatzIter (K + S) n = n ∧ ∀ j : Nat, j < K + S → collatzIter j n ≠ 1 := by
  rcases h with ⟨n, L, hn, hL, hcyc, hne⟩
  rcases exists_syracuseCycle_of_collatz_cycle hn hL hcyc hne with ⟨C, hlen⟩
  have h4m := no_nontrivial_collatzCycle_min_lt_4194304 hn hL hcyc hne
  have hbd := unconditional_syracuseCycle_bounds_lifted22 C
  have hsum : C.k + C.totalVal = L := by
    simpa [SyracuseCycle.collatzLen, Nat.add_comm] using hlen
  refine ⟨n, C.k, C.totalVal, h4m, hbd.2.1, hbd.2.2.1, by omega, ?_, ?_⟩
  · simpa [hsum] using hcyc
  · intro j hj; exact hne j (by omega)

/-! ### 5. Explicit Barrier Separations (`Barriers 1–5`) -/

/-- **Barrier 1 Separation (`3n - 1` on `ℕ⁺`):** `n = 5` forms a non-trivial positive `3n - 1`
cycle of odd length `2 < 7621`, halving count `3 < 12079`, and Collatz length `5 < 19700`,
violating `3 ^ K < 2 ^ S` (`¬ (3 ^ 2 < 2 ^ 3)`). -/
theorem barrier1_eliahou_lifted22_three_n_minus_one :
    Barriers.genIter 3 (-1) 5 5 = 5 ∧
    (∀ j : Nat, j < 5 → Barriers.genIter 3 (-1) j 5 ≠ 1) ∧
    2 < 7621 ∧ 3 < 12079 ∧ 5 < 19700 ∧ ¬ (3 ^ 2 < 2 ^ 3) :=
  ⟨Barriers.three_n_minus_one_cycle_5.1, Barriers.three_n_minus_one_cycle_5.2,
    by decide, by decide, by decide, by decide⟩

/-- **Barrier 2 Separation (`5n + 1` on `ℕ⁺`):** `n = 13` forms a non-trivial positive `5n + 1`
cycle of odd length `3 < 7621`, halving count `7 < 12079`, and Collatz length `10 < 19700`, even
though `3 ^ 3 < 2 ^ 7` and `5 ^ 3 < 2 ^ 7` hold, because `5n + 1` violates `(3n + 1)` stopping
time (`13 < 4194304`) and `(3 * M + 1) ^ K` drift. -/
theorem barrier2_eliahou_lifted22_five_n_plus_one :
    Barriers.genIter 5 1 10 13 = 13 ∧
    (∀ j : Nat, j < 10 → Barriers.genIter 5 1 j 13 ≠ 1) ∧
    3 < 7621 ∧ 7 < 12079 ∧ 10 < 19700 ∧ 5 ^ 3 < 2 ^ 7 ∧ 3 ^ 3 < 2 ^ 7 :=
  ⟨Barriers.five_n_plus_one_cycle_13.1, Barriers.five_n_plus_one_cycle_13.2,
    by decide, by decide, by decide, by decide, by decide⟩

/-- **Barrier 3 Separation (`3n + 1` on `ℤ_{<0}`):** `n = -5` forms a non-trivial negative cycle
of odd length `2 < 7621`, halving count `3 < 12079`, and Collatz length `5 < 19700`, escaping
archimedean positivity `1 < n_min` and `3 ^ 2 < 2 ^ 3`. -/
theorem barrier3_eliahou_lifted22_neg_int :
    Barriers.genIter 3 1 5 (-5) = -5 ∧
    (∀ j : Nat, j < 5 → Barriers.genIter 3 1 j (-5) ≠ 1) ∧
    2 < 7621 ∧ 3 < 12079 ∧ 5 < 19700 ∧ ¬ (3 ^ 2 < 2 ^ 3) :=
  ⟨Barriers.neg_int_cycle_neg5.1, Barriers.neg_int_cycle_neg5.2,
    by decide, by decide, by decide, by decide⟩

/-- **Barrier 4 Separation (`ℤ₂` rational cycles):** `1927 / 295 ∈ ℤ_(2) \ ℤ` (`K = 6 < 7621`,
`S = 10 < 12079`, `L = 16 < 19700`) and `211 / 13 ∈ ℤ_(2) \ ℤ` (`K = 5 < 7621`, `S = 8 < 12079`,
`L = 13 < 19700`) are genuine positive `2`-adic periodic orbits satisfying `3 ^ K < 2 ^ S` yet
violating global integrality in `ℕ⁺`. -/
theorem barrier4_eliahou_lifted22_twoAdic :
    let v := [2, 2, 1, 2, 1, 2]
    let x := periodicPoint v (by decide)
    (x = ⟨1927, 295, by decide⟩ ∧ OddDenomRat.syracuseIter 6 x = x ∧
      3 ^ 6 < 2 ^ 10 ∧ 6 < 7621 ∧ 10 < 12079 ∧ 16 < 19700 ∧
      (¬ ∃ m : Int, x.Equiv (OddDenomRat.ofInt m))) ∧
    (periodicPoint [1, 1, 1, 1, 4] (by decide) = ⟨211, 13, by decide⟩ ∧
      OddDenomRat.syracuseIter 5 (periodicPoint [1, 1, 1, 1, 4] (by decide)) =
        periodicPoint [1, 1, 1, 1, 4] (by decide) ∧
      3 ^ 5 < 2 ^ 8 ∧ 5 < 7621 ∧ 8 < 12079 ∧ 13 < 19700) := by
  have hx : periodicPoint [2, 2, 1, 2, 1, 2] (by decide) = ⟨1927, 295, by decide⟩ := by decide
  have hb4 := barrier4_eliahou_twoAdic
  refine ⟨⟨hx, hb4.1.2.1, hb4.1.2.2.1, by decide, by decide, by decide, hb4.1.2.2.2.2.2.2⟩,
    ⟨hb4.2.1, hb4.2.2.1, hb4.2.2.2.1, by decide, by decide, by decide⟩⟩

/-- **Barrier 5 Separation (Conway 1972 / Finite Verification Horizon):** unconditional kernel
verification up to `2^22 = 4194304` lifts the unconditional cycle bound to `K ≥ 7621, L ≥ 19700`,
while higher bounds (`10^7 → K ≥ 10946`, `3 * 10^8 → K ≥ 16266`) remain contingent on further
finite stopping-time verification and global Diophantine / Baker bounds. -/
theorem barrier5_eliahou_lifted22_conway_horizon :
    (∀ C : SyracuseCycle, 4194304 ≤ C.n_min ∧ 7621 ≤ C.k ∧ 19700 ≤ C.collatzLen) ∧
    ((∀ n : Nat, 2 ≤ n → n < 10000000 → HasFiniteStoppingTime n) →
      ∀ C : SyracuseCycle, 10946 ≤ C.k ∧ 28295 ≤ C.collatzLen) ∧
    ((∀ n : Nat, 2 ≤ n → n < 300000000 → HasFiniteStoppingTime n) →
      ∀ C : SyracuseCycle, 16266 ≤ C.k ∧ 42048 ≤ C.collatzLen) :=
  ⟨fun C => ⟨(unconditional_syracuseCycle_bounds_lifted22 C).1,
      (unconditional_syracuseCycle_bounds_lifted22 C).2.1,
      unconditional_syracuseCycle_collatzLen_ge_19700 C⟩,
    fun h C => ⟨(eliahou_cf_bounds_of_stopping_1e7 h C).1,
      (eliahou_cf_bounds_of_stopping_1e7 h C).2.2⟩,
    fun h C => ⟨(eliahou_cf_bounds_of_stopping_3e8 h C).1,
      (eliahou_cf_bounds_of_stopping_3e8 h C).2.2⟩⟩

end SolveCollatz
