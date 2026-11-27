/-
Copyright (c) 2026 The solve-collatz contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Collatz.Known.EliahouConvergents

/-!
# Lifted Unconditional Eliahou Cycle Bounds via Modular Descent (`KNOWN-003` Phase 3)

Formalization in pure Lean 4 core (zero Mathlib, zero `sorry`, zero `native_decide`):
1. Kernel-fast 2-step unrolled chained Terras descent checker (`dropChunk2Step`, `dropChunk3`)
   avoiding typeclass/match overhead, with full soundness (`dropChunk3_sound`).
2. Dyadic modular descent tree checker (`checkShellD`) pruning residue classes `r mod 2^k`
   whenever `3^c < 2^k` and `terrasIter k r + 3^c < r + 2^k`, and certifying surviving elements
   in each dyadic shell `[2^k, 2^(k+1))` (`12 ≤ k < 20`).
3. **Unconditional Small-`n` Completion up to `2^20 = 1,048,576`:** 8 balanced `mod 256` bucket
   certificates verified purely in Lean's kernel (`by decide`), proving `HasFiniteStoppingTime n`
   for all `2 ≤ n < 1048576` (`32x` beyond `32768`) and `1048576 ≤ C.n_min`.
4. **Flagship Unconditional Cycle-Length Lower Bounds (ZERO external hypotheses):**
   every non-trivial positive `SyracuseCycle` satisfies `1048576 ≤ C.n_min`, `2966 ≤ C.k`,
   `4701 ≤ C.totalVal`, and `7667 ≤ C.collatzLen` (`~9.7x` jump over `K ≥ 306`, `L ≥ 791`),
   bridged directly to frozen `Challenge.HasNontrivialCycle`.
5. Explicit **Barrier 1–5 separations** (`3n - 1`, `5n + 1`, `ℤ_{<0}`, `ℤ₂`, Conway horizon).
-/

@[expose] public section

namespace SolveCollatz

/-! ### 1. Kernel-Fast Chained Terras Descent Checker & Soundness -/

/-- One step of `terrasStep` using direct primitive operations for fast kernel reduction. -/
def terrasStepFast (c : Nat) : Nat :=
  cond (Nat.beq (Nat.mod c 2) 0) (Nat.div c 2) (Nat.div (Nat.add (Nat.mul 3 c) 1) 2)

/-- Equivalence between `terrasStepFast` and `TerrasParity.terrasStep`. -/
theorem terrasStepFast_eq (c : Nat) : terrasStepFast c = terrasStep c := by
  unfold terrasStepFast terrasStep
  by_cases h : c % 2 = 0
  · have hb : Nat.beq (Nat.mod c 2) 0 = true := Nat.beq_eq.mpr h
    change cond (Nat.beq (Nat.mod c 2) 0) (c / 2) ((3 * c + 1) / 2) = _
    rw [hb]; simp [h]
  · have hb : Nat.beq (Nat.mod c 2) 0 = false := by
      cases hq : Nat.beq (Nat.mod c 2) 0
      · rfl
      · exact absurd (Nat.beq_eq.mp hq) h
    change cond (Nat.beq (Nat.mod c 2) 0) (c / 2) ((3 * c + 1) / 2) = _
    rw [hb]; simp [h]

/-- 2-step unrolled Terras descent loop returning `0` on drop below `target`. -/
def dropChunk2Step (target fuel cur : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun c => c)
    (fun _ ih c =>
      let c1 := cond (Nat.beq (Nat.mod c 2) 0)
        (Nat.div c 2) (Nat.div (Nat.add (Nat.mul 3 c) 1) 2)
      cond (Nat.ble target c1)
        (let c2 := cond (Nat.beq (Nat.mod c1 2) 0)
           (Nat.div c1 2) (Nat.div (Nat.add (Nat.mul 3 c1) 1) 2)
         cond (Nat.ble target c2) (ih c2) 0)
        0)
    fuel cur

/-- Single-step helper for `dropChunk2Step_spec`. -/
private theorem drop_step_case {n j : Nat} :
    (Nat.ble n (terrasIter (j + 1) n) = false → HasFiniteStoppingTime n) ∧
    (Nat.ble n (terrasIter (j + 1) n) = true → n ≤ terrasIter (j + 1) n) := by
  constructor
  · intro hf
    have hlt : terrasIter (j + 1) n < n := by
      have hnot : ¬ n ≤ terrasIter (j + 1) n := fun hle => by
        rw [Nat.ble_eq.mpr hle] at hf; exact absurd hf (by decide)
      omega
    exact hasFiniteStoppingTime_of_terras_lt (Nat.succ_pos j) hlt
  · intro ht; exact Nat.ble_eq.mp ht

/-- Specification of `dropChunk2Step` starting at `terrasIter j n` (`0 < n`). -/
theorem dropChunk2Step_spec {n : Nat} (hn : 0 < n) (fuel j : Nat) :
    (dropChunk2Step n fuel (terrasIter j n) = 0 → HasFiniteStoppingTime n) ∧
    (dropChunk2Step n fuel (terrasIter j n) ≠ 0 →
      ∃ m : Nat, dropChunk2Step n fuel (terrasIter j n) = terrasIter (j + m) n) := by
  induction fuel generalizing j with
  | zero =>
    have hpos : 0 < terrasIter j n := terrasIter_pos j hn
    change (terrasIter j n = 0 → HasFiniteStoppingTime n) ∧
      (terrasIter j n ≠ 0 → ∃ m : Nat, terrasIter j n = terrasIter (j + m) n)
    exact ⟨fun h0 => absurd h0 (by omega), fun _ => ⟨0, rfl⟩⟩
  | succ fuel ih =>
    have h1 : cond (Nat.beq (Nat.mod (terrasIter j n) 2) 0) (Nat.div (terrasIter j n) 2)
        (Nat.div (Nat.add (Nat.mul 3 (terrasIter j n)) 1) 2) = terrasIter (j + 1) n := by
      simpa [terrasStepFast, terrasIter_succ_right] using terrasStepFast_eq (terrasIter j n)
    have h2 : cond (Nat.beq (Nat.mod (terrasIter (j + 1) n) 2) 0)
        (Nat.div (terrasIter (j + 1) n) 2)
        (Nat.div (Nat.add (Nat.mul 3 (terrasIter (j + 1) n)) 1) 2) = terrasIter (j + 2) n := by
      simpa [terrasStepFast, terrasIter_succ_right, Nat.add_assoc] using
        terrasStepFast_eq (terrasIter (j + 1) n)
    unfold dropChunk2Step; dsimp only; rw [h1]
    cases hb1 : Nat.ble n (terrasIter (j + 1) n)
    · simp only [Bool.cond_false]
      exact ⟨fun _ => drop_step_case.1 hb1, fun hne => absurd rfl hne⟩
    · simp only [Bool.cond_true]; rw [h2]
      cases hb2 : Nat.ble n (terrasIter (j + 2) n)
      · simp only [Bool.cond_false]
        exact ⟨fun _ => drop_step_case.1 hb2, fun hne => absurd rfl hne⟩
      · simp only [Bool.cond_true]
        rcases ih (j + 2) with ⟨ih0, ihne⟩
        refine ⟨ih0, fun hne => ?_⟩
        rcases ihne hne with ⟨m, hm⟩
        exact ⟨m + 2, by
          change dropChunk2Step n fuel (terrasIter (j + 2) n) = terrasIter (j + (m + 2)) n
          simpa [Nat.add_assoc, Nat.add_comm 2 m] using hm⟩

/-- Chained 3-stage descent checker covering up to `210` Terras steps (`3 * 70`). -/
def dropChunk3 (target cur : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun p1 _ => Nat.rec (motive := fun _ => Nat) 0
      (fun p2 _ => dropChunk2Step target 35 (Nat.add p2 1))
      (dropChunk2Step target 35 (Nat.add p1 1)))
    (dropChunk2Step target 35 cur)

/-- Soundness of `dropChunk3`: `dropChunk3 n (terrasIter j n) = 0` yields
`HasFiniteStoppingTime n`. -/
theorem dropChunk3_sound {n j : Nat} (hn : 0 < n)
    (h : dropChunk3 n (terrasIter j n) = 0) : HasFiniteStoppingTime n := by
  unfold dropChunk3 at h
  cases hc1 : dropChunk2Step n 35 (terrasIter j n) with
  | zero => exact (dropChunk2Step_spec hn 35 j).1 hc1
  | succ p1 =>
    rcases (dropChunk2Step_spec hn 35 j).2 (by rw [hc1]; omega) with ⟨m1, hm1⟩
    rw [hc1] at h; dsimp only at h
    have hp1 : Nat.add p1 1 = terrasIter (j + m1) n := by rw [← hm1, hc1]
    rw [hp1] at h
    cases hc2 : dropChunk2Step n 35 (terrasIter (j + m1) n) with
    | zero => exact (dropChunk2Step_spec hn 35 (j + m1)).1 hc2
    | succ p2 =>
      rcases (dropChunk2Step_spec hn 35 (j + m1)).2 (by rw [hc2]; omega) with ⟨m2, hm2⟩
      rw [hc2] at h; dsimp only at h
      have hp2 : Nat.add p2 1 = terrasIter (j + m1 + m2) n := by rw [← hm2, hc2]
      rw [hp2] at h
      exact (dropChunk2Step_spec hn 35 (j + m1 + m2)).1 h

/-! ### 2. Dyadic Modular Descent Tree (`checkShellD`) & Soundness -/

/-- Dyadic modular descent tree checker over `rem` depth levels, restricted at `k = 8` to
residue bucket `[lo, hi)` mod `256` and checking elements in shells `12 ≤ k`. -/
def checkShellD (lo hi rem k r cur p3 p2 : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Bool)
    (fun k r cur p3 p2 =>
      cond (Nat.ble 12 k)
        (cond (and (Nat.ble 1 k) (and (Nat.ble (Nat.add p3 1) p2)
          (Nat.ble (Nat.add (Nat.add cur p3) 1) (Nat.add r p2))))
          true
          (Nat.beq (dropChunk3 (Nat.add r p2) (Nat.add cur p3)) 0))
        true)
    (fun _ ih k r cur p3 p2 =>
      cond (and (Nat.ble 1 k) (and (Nat.ble (Nat.add p3 1) p2)
        (Nat.ble (Nat.add (Nat.add cur p3) 1) (Nat.add r p2))))
        true
        (cond (and (Nat.beq k 8) (or (Nat.ble (Nat.add r 1) lo) (Nat.ble hi r)))
          true
          (let k' := Nat.add k 1
           let p2' := Nat.mul 2 p2
           let cp3 := Nat.add cur p3
           let rp2 := Nat.add r p2
           let okSelf := cond (Nat.ble 12 k) (Nat.beq (dropChunk3 rp2 cp3) 0) true
           cond okSelf
             (cond (Nat.beq (Nat.mod cur 2) 0)
               (and (ih k' r (Nat.div cur 2) p3 p2')
                    (ih k' rp2 (Nat.div (Nat.add (Nat.mul 3 cp3) 1) 2) (Nat.mul 3 p3) p2'))
               (and (ih k' r (Nat.div (Nat.add (Nat.mul 3 cur) 1) 2) (Nat.mul 3 p3) p2')
                    (ih k' rp2 (Nat.div cp3 2) p3 p2')))
             false)))
    rem k r cur p3 p2

/-- Pruned residue class soundness: `0 < k`, `3^c < 2^k`, and `terrasIter k r + 3^c < r + 2^k`
forces `HasFiniteStoppingTime n` for every `n ≥ 2^k` with `n % 2^k = r`. -/
private theorem terras_drop_of_pruned {k r n : Nat} (hk : 0 < k) (hmod : n % 2 ^ k = r)
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
private theorem terras_shell_eq {k r n : Nat} (hmod : n % 2 ^ k = r)
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
private theorem terras_child_left (k r : Nat) :
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
private theorem terras_child_right (k r : Nat) :
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

/-- Helper unpacking the pruning guard `and (Nat.ble 1 k) ... = true`. -/
private theorem unpack_prune_guard {k r cur p3 p2 : Nat}
    (h : and (Nat.ble 1 k) (and (Nat.ble (Nat.add p3 1) p2)
      (Nat.ble (Nat.add (Nat.add cur p3) 1) (Nat.add r p2))) = true) :
    0 < k ∧ p3 < p2 ∧ cur + p3 < r + p2 := by
  simp only [Bool.and_eq_true, Nat.ble_eq] at h
  change 1 ≤ k ∧ p3 + 1 ≤ p2 ∧ cur + p3 + 1 ≤ r + p2 at h
  omega

/-- Helper unpacking `n % 2^(k + 1)` into `n % 2^k` or `n % 2^k + 2^k`. -/
private theorem mod_two_pow_succ_split (n k : Nat) :
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

/-- Helper: `2^12 ≤ n < 2^(k + 1)` forces `12 ≤ k`. -/
private theorem pow12_le_of_lt {k n : Nat} (hn12 : 2 ^ 12 ≤ n) (hlt : n < 2 ^ (k + 1)) :
    12 ≤ k := by
  by_cases h : 12 ≤ k
  · exact h
  · have : 2 ^ (k + 1) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (by omega)
    omega

/-- Base case (`rem = 0`) soundness of `checkShellD`. -/
private theorem checkShellD_zero_sound (lo hi k r : Nat)
    (hchk : checkShellD lo hi 0 k r (terrasIter k r)
      (3 ^ countOnes (terrasParityVec k r)) (2 ^ k) = true) :
    ∀ n : Nat, 2 ^ 12 ≤ n → 2 ^ k ≤ n → n < 2 ^ (k + 1) → n % 2 ^ k = r →
      HasFiniteStoppingTime n := by
  intro n hn12 hnk hn_hi hmod
  change cond (Nat.ble 12 k)
    (cond (and (Nat.ble 1 k) (and (Nat.ble (Nat.add (3 ^ countOnes (terrasParityVec k r)) 1)
      (2 ^ k)) (Nat.ble (Nat.add (Nat.add (terrasIter k r)
        (3 ^ countOnes (terrasParityVec k r))) 1) (Nat.add r (2 ^ k)))))
      true
      (Nat.beq (dropChunk3 (Nat.add r (2 ^ k))
        (Nat.add (terrasIter k r) (3 ^ countOnes (terrasParityVec k r)))) 0))
    true = true at hchk
  rw [Nat.ble_eq.mpr (pow12_le_of_lt hn12 hn_hi), Bool.cond_true] at hchk
  rcases terras_shell_eq hmod hnk hn_hi with ⟨hn_eq, hiter⟩
  cases hp : and (Nat.ble 1 k) (and (Nat.ble (Nat.add (3 ^ countOnes (terrasParityVec k r)) 1)
      (2 ^ k)) (Nat.ble (Nat.add (Nat.add (terrasIter k r)
        (3 ^ countOnes (terrasParityVec k r))) 1) (Nat.add r (2 ^ k))))
  · rw [hp, Bool.cond_false] at hchk
    have hdrop0 : dropChunk3 (r + 2 ^ k)
        (terrasIter k r + 3 ^ countOnes (terrasParityVec k r)) = 0 := Nat.beq_eq.mp hchk
    rw [← hn_eq, ← hiter] at hdrop0
    exact dropChunk3_sound (by omega) hdrop0
  · rcases unpack_prune_guard hp with ⟨hk0, h32, hlt⟩
    exact terras_drop_of_pruned hk0 hmod hnk h32 hlt

/-- Bucket filter contradiction at `k = 8` when `lo ≤ n % 256 < hi`. -/
private theorem checkShellD_bucket_absurd {lo hi k r n : Nat}
    (hmod : n % 2 ^ k = r) (hlo : lo ≤ n % 256) (hhi : n % 256 < hi)
    (hb : and (Nat.beq k 8) (or (Nat.ble (Nat.add r 1) lo) (Nat.ble hi r)) = true) : False := by
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, Nat.ble_eq] at hb
  rcases hb with ⟨hk8, hside⟩
  subst hk8
  have h256 : (2 ^ 8 : Nat) = 256 := by decide
  rw [h256] at hmod
  change r + 1 ≤ lo ∨ hi ≤ r at hside
  omega

/-- Left-child branch of `checkShellD_succ_sound` (`n % 2^(k+1) = r`). -/
private theorem checkShellD_left_child (lo hi rem k r : Nat)
    (hbranch : (let k' := Nat.add k 1; let p2' := Nat.mul 2 (2 ^ k)
      let cp3 := Nat.add (terrasIter k r) (3 ^ countOnes (terrasParityVec k r))
      let rp2 := Nat.add r (2 ^ k)
      cond (Nat.beq (Nat.mod (terrasIter k r) 2) 0)
        (and (checkShellD lo hi rem k' r (Nat.div (terrasIter k r) 2)
               (3 ^ countOnes (terrasParityVec k r)) p2')
             (checkShellD lo hi rem k' rp2 (Nat.div (Nat.add (Nat.mul 3 cp3) 1) 2)
               (Nat.mul 3 (3 ^ countOnes (terrasParityVec k r))) p2'))
        (and (checkShellD lo hi rem k' r
               (Nat.div (Nat.add (Nat.mul 3 (terrasIter k r)) 1) 2)
               (Nat.mul 3 (3 ^ countOnes (terrasParityVec k r))) p2')
             (checkShellD lo hi rem k' rp2 (Nat.div cp3 2)
               (3 ^ countOnes (terrasParityVec k r)) p2'))) = true) :
    checkShellD lo hi rem (k + 1) r (terrasIter (k + 1) r)
      (3 ^ countOnes (terrasParityVec (k + 1) r)) (2 ^ (k + 1)) = true := by
  have h2pow : Nat.mul 2 (2 ^ k) = 2 ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_comm]; rfl
  by_cases hev : terrasIter k r % 2 = 0
  · have hbeq : Nat.beq (Nat.mod (terrasIter k r) 2) 0 = true := Nat.beq_eq.mpr hev
    rw [hbeq, Bool.cond_true, Bool.and_eq_true] at hbranch
    rcases (terras_child_left k r).1 hev with ⟨hiter', hp3⟩
    rw [show k + 1 = Nat.add k 1 from rfl, hiter', hp3, ← h2pow]; exact hbranch.1
  · have hbeq : Nat.beq (Nat.mod (terrasIter k r) 2) 0 = false := by
      cases hq : Nat.beq (Nat.mod (terrasIter k r) 2) 0
      · rfl
      · exact absurd (Nat.beq_eq.mp hq) hev
    rw [hbeq, Bool.cond_false, Bool.and_eq_true] at hbranch
    rcases (terras_child_left k r).2 hev with ⟨hiter', hp3⟩
    rw [show k + 1 = Nat.add k 1 from rfl, hiter', hp3, ← h2pow]; exact hbranch.1

/-- Right-child branch of `checkShellD_succ_sound` (`n % 2^(k+1) = r + 2^k`). -/
private theorem checkShellD_right_child (lo hi rem k r : Nat)
    (hbranch : (let k' := Nat.add k 1; let p2' := Nat.mul 2 (2 ^ k)
      let cp3 := Nat.add (terrasIter k r) (3 ^ countOnes (terrasParityVec k r))
      let rp2 := Nat.add r (2 ^ k)
      cond (Nat.beq (Nat.mod (terrasIter k r) 2) 0)
        (and (checkShellD lo hi rem k' r (Nat.div (terrasIter k r) 2)
               (3 ^ countOnes (terrasParityVec k r)) p2')
             (checkShellD lo hi rem k' rp2 (Nat.div (Nat.add (Nat.mul 3 cp3) 1) 2)
               (Nat.mul 3 (3 ^ countOnes (terrasParityVec k r))) p2'))
        (and (checkShellD lo hi rem k' r
               (Nat.div (Nat.add (Nat.mul 3 (terrasIter k r)) 1) 2)
               (Nat.mul 3 (3 ^ countOnes (terrasParityVec k r))) p2')
             (checkShellD lo hi rem k' rp2 (Nat.div cp3 2)
               (3 ^ countOnes (terrasParityVec k r)) p2'))) = true) :
    checkShellD lo hi rem (k + 1) (r + 2 ^ k) (terrasIter (k + 1) (r + 2 ^ k))
      (3 ^ countOnes (terrasParityVec (k + 1) (r + 2 ^ k))) (2 ^ (k + 1)) = true := by
  have h2pow : Nat.mul 2 (2 ^ k) = 2 ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_comm]; rfl
  by_cases hev : terrasIter k r % 2 = 0
  · have hbeq : Nat.beq (Nat.mod (terrasIter k r) 2) 0 = true := Nat.beq_eq.mpr hev
    rw [hbeq, Bool.cond_true, Bool.and_eq_true] at hbranch
    rcases (terras_child_right k r).1 hev with ⟨hiter', hp3⟩
    rw [show k + 1 = Nat.add k 1 from rfl, hiter', hp3, ← h2pow]; exact hbranch.2
  · have hbeq : Nat.beq (Nat.mod (terrasIter k r) 2) 0 = false := by
      cases hq : Nat.beq (Nat.mod (terrasIter k r) 2) 0
      · rfl
      · exact absurd (Nat.beq_eq.mp hq) hev
    rw [hbeq, Bool.cond_false, Bool.and_eq_true] at hbranch
    rcases (terras_child_right k r).2 hev with ⟨hiter', hp3⟩
    rw [show k + 1 = Nat.add k 1 from rfl, hiter', hp3, ← h2pow]; exact hbranch.2

/-- Inductive step (`rem + 1`) soundness of `checkShellD`. -/
private theorem checkShellD_succ_sound (lo hi rem : Nat)
    (ih : ∀ k r : Nat, r < 2 ^ k → checkShellD lo hi rem k r (terrasIter k r)
      (3 ^ countOnes (terrasParityVec k r)) (2 ^ k) = true →
      ∀ n : Nat, 2 ^ 12 ≤ n → 2 ^ k ≤ n → n < 2 ^ (k + rem + 1) →
        n % 2 ^ k = r → lo ≤ n % 256 → n % 256 < hi → HasFiniteStoppingTime n)
    (k r : Nat) (hr : r < 2 ^ k)
    (hchk : checkShellD lo hi (rem + 1) k r (terrasIter k r)
      (3 ^ countOnes (terrasParityVec k r)) (2 ^ k) = true) :
    ∀ n : Nat, 2 ^ 12 ≤ n → 2 ^ k ≤ n → n < 2 ^ (k + (rem + 1) + 1) →
      n % 2 ^ k = r → lo ≤ n % 256 → n % 256 < hi → HasFiniteStoppingTime n := by
  intro n hn12 hnk hn_hi hmod hn_lo hn_hi256
  unfold checkShellD at hchk; dsimp only at hchk
  cases hp : and (Nat.ble 1 k) (and (Nat.ble (Nat.add (3 ^ countOnes (terrasParityVec k r)) 1)
      (2 ^ k)) (Nat.ble (Nat.add (Nat.add (terrasIter k r)
        (3 ^ countOnes (terrasParityVec k r))) 1) (Nat.add r (2 ^ k))))
  · rw [hp, Bool.cond_false] at hchk
    cases hb : and (Nat.beq k 8) (or (Nat.ble (Nat.add r 1) lo) (Nat.ble hi r))
    · rw [hb, Bool.cond_false] at hchk
      cases hok : cond (Nat.ble 12 k) (Nat.beq (dropChunk3 (Nat.add r (2 ^ k))
          (Nat.add (terrasIter k r) (3 ^ countOnes (terrasParityVec k r)))) 0) true
      · rw [hok, Bool.cond_false] at hchk; exact absurd hchk (by decide)
      · rw [hok, Bool.cond_true] at hchk
        by_cases hlt_shell : n < 2 ^ (k + 1)
        · rw [Nat.ble_eq.mpr (pow12_le_of_lt hn12 hlt_shell), Bool.cond_true] at hok
          rcases terras_shell_eq hmod hnk hlt_shell with ⟨hn_eq, hiter⟩
          have hdrop0 : dropChunk3 (r + 2 ^ k)
              (terrasIter k r + 3 ^ countOnes (terrasParityVec k r)) = 0 := Nat.beq_eq.mp hok
          rw [← hn_eq, ← hiter] at hdrop0
          exact dropChunk3_sound (by omega) hdrop0
        · have hnk1 : 2 ^ (k + 1) ≤ n := Nat.le_of_not_lt hlt_shell
          have hn_hi' : n < 2 ^ ((k + 1) + rem + 1) := by
            simpa [Nat.add_assoc, Nat.add_comm 1 rem] using hn_hi
          have hpow1 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
          rcases mod_two_pow_succ_split n k with hleft | hright
          · rw [hmod] at hleft
            exact ih (k + 1) r (by omega) (checkShellD_left_child lo hi rem k r hchk)
              n hn12 hnk1 hn_hi' hleft hn_lo hn_hi256
          · rw [hmod] at hright
            exact ih (k + 1) (r + 2 ^ k) (by omega) (checkShellD_right_child lo hi rem k r hchk)
              n hn12 hnk1 hn_hi' hright hn_lo hn_hi256
    · exact absurd (checkShellD_bucket_absurd hmod hn_lo hn_hi256 hb) False.elim
  · rcases unpack_prune_guard hp with ⟨hk0, h32, hlt⟩
    exact terras_drop_of_pruned hk0 hmod hnk h32 hlt

/-- **Soundness of `checkShellD`:** any `n` with `2^12 ≤ n < 2^(k + rem + 1)` matching `r mod 2^k`
in bucket `[lo, hi) mod 256` satisfies `HasFiniteStoppingTime n`. -/
theorem checkShellD_sound (lo hi rem k r : Nat) (hr : r < 2 ^ k)
    (hchk : checkShellD lo hi rem k r (terrasIter k r)
      (3 ^ countOnes (terrasParityVec k r)) (2 ^ k) = true) :
    ∀ n : Nat, 2 ^ 12 ≤ n → 2 ^ k ≤ n → n < 2 ^ (k + rem + 1) → n % 2 ^ k = r →
      lo ≤ n % 256 → n % 256 < hi → HasFiniteStoppingTime n := by
  induction rem generalizing k r with
  | zero =>
    intro n hn12 hnk hn_hi hmod _ _
    exact checkShellD_zero_sound lo hi k r hchk n hn12 hnk hn_hi hmod
  | succ rem ih =>
    exact checkShellD_succ_sound lo hi rem ih k r hr hchk

/-! ### 3. Kernel Certificates up to `2^20 = 1,048,576` & Unconditional `n_min ≥ 1048576` -/

private theorem shell20_b0 : checkShellD   0  32 19 0 0 0 1 1 = true := by decide
private theorem shell20_b1 : checkShellD  32  96 19 0 0 0 1 1 = true := by decide
private theorem shell20_b2 : checkShellD  96 112 19 0 0 0 1 1 = true := by decide
private theorem shell20_b3 : checkShellD 112 144 19 0 0 0 1 1 = true := by decide
private theorem shell20_b4 : checkShellD 144 160 19 0 0 0 1 1 = true := by decide
private theorem shell20_b5 : checkShellD 160 224 19 0 0 0 1 1 = true := by decide
private theorem shell20_b6 : checkShellD 224 240 19 0 0 0 1 1 = true := by decide
private theorem shell20_b7 : checkShellD 240 256 19 0 0 0 1 1 = true := by decide

/-- Helper applying `checkShellD_sound` at root `(k = 0, rem = 19)` for bucket `[lo, hi)`. -/
private theorem shell20_bucket_sound (lo hi : Nat)
    (hchk : checkShellD lo hi 19 0 0 0 1 1 = true) {n : Nat}
    (hlo : 4096 ≤ n) (hhi : n < 1048576) (hbl : lo ≤ n % 256) (hbh : n % 256 < hi) :
    HasFiniteStoppingTime n :=
  checkShellD_sound lo hi 19 0 0 (by decide)
    (by simpa [terrasIter, terrasParityVec, countOnes] using hchk)
    n (by simpa using hlo) (by omega) (by simpa using hhi) (Nat.mod_one n) hbl hbh

/-- **Unconditional Small-`n` Completion (`2 ≤ n < 1048576 = 2^20`):**
every integer `2 ≤ n < 1048576` has finite Terras stopping time (pure kernel `decide`). -/
theorem small_lt_1048576_finiteStoppingTime {n : Nat} (hn2 : 2 ≤ n) (hn20 : n < 1048576) :
    HasFiniteStoppingTime n := by
  by_cases hlt : n < 4096
  · exact small_lt_4096_finiteStoppingTime hn2 hlt
  · have h4096 : 4096 ≤ n := by omega
    have hm : n % 256 < 256 := Nat.mod_lt n (by decide)
    by_cases h1 : n % 256 < 32
    · exact shell20_bucket_sound 0 32 shell20_b0 h4096 hn20 (Nat.zero_le _) h1
    · by_cases h2 : n % 256 < 96
      · exact shell20_bucket_sound 32 96 shell20_b1 h4096 hn20 (by omega) h2
      · by_cases h3 : n % 256 < 112
        · exact shell20_bucket_sound 96 112 shell20_b2 h4096 hn20 (by omega) h3
        · by_cases h4 : n % 256 < 144
          · exact shell20_bucket_sound 112 144 shell20_b3 h4096 hn20 (by omega) h4
          · by_cases h5 : n % 256 < 160
            · exact shell20_bucket_sound 144 160 shell20_b4 h4096 hn20 (by omega) h5
            · by_cases h6 : n % 256 < 224
              · exact shell20_bucket_sound 160 224 shell20_b5 h4096 hn20 (by omega) h6
              · by_cases h7 : n % 256 < 240
                · exact shell20_bucket_sound 224 240 shell20_b6 h4096 hn20 (by omega) h7
                · exact shell20_bucket_sound 240 256 shell20_b7 h4096 hn20 (by omega) hm

/-- **Unconditional Minimal-Element Lower Bound (`M = 2^20`):**
every non-trivial positive `SyracuseCycle` satisfies `1048576 ≤ C.n_min`. -/
theorem no_nontrivial_syracuseCycle_min_lt_1048576 (C : SyracuseCycle) : 1048576 ≤ C.n_min :=
  syracuseCycle_min_ge_of_stopping 1048576
    (fun _ hn2 hlt => small_lt_1048576_finiteStoppingTime hn2 hlt) C

/-- **Unconditional Cycle-Element Lower Bound (`Challenge.lean`, `M = 2^20`):**
every element `n` on a non-trivial positive Collatz cycle satisfies `1048576 ≤ n`. -/
theorem no_nontrivial_collatzCycle_min_lt_1048576 {n L : Nat} (hn : 0 < n) (hL : 0 < L)
    (hcyc : collatzIter L n = n) (hne : ∀ j : Nat, j < L → collatzIter j n ≠ 1) :
    1048576 ≤ n :=
  collatz_cycle_elem_ge_of_stopping 1048576
    (fun _ hn2 hlt => small_lt_1048576_finiteStoppingTime hn2 hlt) hn hL hcyc hne

/-! ### 4. Flagship Unconditional Lifted Eliahou Cycle-Length Lower Bounds -/

/-- **Flagship Unconditional Combined Cycle-Length Bounds (ZERO hypotheses):**
every non-trivial positive `SyracuseCycle` satisfies `1048576 ≤ C.n_min`, `2966 ≤ C.k`,
`4701 ≤ C.totalVal`, and `7667 ≤ C.collatzLen`. -/
theorem unconditional_syracuseCycle_lifted_bounds (C : SyracuseCycle) :
    1048576 ≤ C.n_min ∧ 2966 ≤ C.k ∧ 4701 ≤ C.totalVal ∧ 7667 ≤ C.collatzLen := by
  have hM : 1048576 ≤ C.n_min := no_nontrivial_syracuseCycle_min_lt_1048576 C
  have hcf := eliahou_cf_bounds_of_ge_1e6 C (by omega)
  exact ⟨hM, hcf.1, hcf.2.1, hcf.2.2⟩

/-- **Flagship Unconditional Odd-Step Bound (`K ≥ 2966`, ZERO hypotheses):**
every non-trivial positive `SyracuseCycle` has odd length `2966 ≤ C.k`. -/
theorem unconditional_syracuseCycle_odd_length_ge_2966 (C : SyracuseCycle) : 2966 ≤ C.k :=
  (unconditional_syracuseCycle_lifted_bounds C).2.1

/-- **Flagship Unconditional Halving Bound (`S ≥ 4701`, ZERO hypotheses):**
every non-trivial positive `SyracuseCycle` has total halvings `4701 ≤ C.totalVal`. -/
theorem unconditional_syracuseCycle_halvings_ge_4701 (C : SyracuseCycle) : 4701 ≤ C.totalVal :=
  (unconditional_syracuseCycle_lifted_bounds C).2.2.1

/-- **Flagship Unconditional Total-Length Bound (`L ≥ 7667`, ZERO hypotheses):**
every non-trivial positive `SyracuseCycle` has Collatz length `7667 ≤ C.collatzLen`. -/
theorem unconditional_syracuseCycle_collatzLen_ge_7667 (C : SyracuseCycle) :
    7667 ≤ C.collatzLen :=
  (unconditional_syracuseCycle_lifted_bounds C).2.2.2

/-- **Flagship Unconditional Bridge to Frozen `Challenge.lean` (`L ≥ 7667`):**
every non-trivial positive Collatz cycle `(n, L)` has total length `7667 ≤ L`
(with `2966 ≤ K`, `4701 ≤ S`, `K + S = L`, and `1048576 ≤ n`). -/
theorem unconditional_collatzCycle_length_ge_7667 {n L : Nat} (hn : 0 < n) (hL : 0 < L)
    (hcyc : collatzIter L n = n) (hne : ∀ j : Nat, j < L → collatzIter j n ≠ 1) :
    7667 ≤ L := by
  rcases exists_syracuseCycle_of_collatz_cycle hn hL hcyc hne with ⟨C, hlen⟩
  have h7667 := unconditional_syracuseCycle_collatzLen_ge_7667 C
  omega

/-- **Unconditional Decomposition Theorem for Frozen `HasNontrivialCycle` (`M = 2^20`):**
any `HasNontrivialCycle` witness yields `(n, K, S)` with `1048576 ≤ n`, `2966 ≤ K`,
`4701 ≤ S`, `7667 ≤ K + S`, and `collatzIter (K + S) n = n` avoiding `1`. -/
theorem unconditional_hasNontrivialCycle_lifted_bounds (h : HasNontrivialCycle) :
    ∃ n K S : Nat, 1048576 ≤ n ∧ 2966 ≤ K ∧ 4701 ≤ S ∧ 7667 ≤ K + S ∧
      collatzIter (K + S) n = n ∧ ∀ j : Nat, j < K + S → collatzIter j n ≠ 1 := by
  rcases h with ⟨n, L, hn, hL, hcyc, hne⟩
  rcases exists_syracuseCycle_of_collatz_cycle hn hL hcyc hne with ⟨C, hlen⟩
  have h1m := no_nontrivial_collatzCycle_min_lt_1048576 hn hL hcyc hne
  have hbd := unconditional_syracuseCycle_lifted_bounds C
  have hsum : C.k + C.totalVal = L := by
    simpa [SyracuseCycle.collatzLen, Nat.add_comm] using hlen
  refine ⟨n, C.k, C.totalVal, h1m, hbd.2.1, hbd.2.2.1, by omega, ?_, ?_⟩
  · simpa [hsum] using hcyc
  · intro j hj; exact hne j (by omega)

/-! ### 5. Explicit Barrier Separations (`Barriers 1–5`) -/

/-- **Barrier 1 Separation (`3n - 1` on `ℕ⁺`):** `n = 5` forms a non-trivial positive `3n - 1`
cycle of odd length `2 < 2966`, halving count `3 < 4701`, and Collatz length `5 < 7667`, violating
`3 ^ K < 2 ^ S` (`¬ (3 ^ 2 < 2 ^ 3)`). -/
theorem barrier1_eliahou_lifted_three_n_minus_one :
    Barriers.genIter 3 (-1) 5 5 = 5 ∧
    (∀ j : Nat, j < 5 → Barriers.genIter 3 (-1) j 5 ≠ 1) ∧
    2 < 2966 ∧ 3 < 4701 ∧ 5 < 7667 ∧ ¬ (3 ^ 2 < 2 ^ 3) :=
  ⟨Barriers.three_n_minus_one_cycle_5.1, Barriers.three_n_minus_one_cycle_5.2,
    by decide, by decide, by decide, by decide⟩

/-- **Barrier 2 Separation (`5n + 1` on `ℕ⁺`):** `n = 13` forms a non-trivial positive `5n + 1`
cycle of odd length `3 < 2966`, halving count `7 < 4701`, and Collatz length `10 < 7667`, even
though `3 ^ 3 < 2 ^ 7` and `5 ^ 3 < 2 ^ 7` hold, because `5n + 1` violates `(3n + 1)` stopping
time (`13 < 1048576`) and `(3 * M + 1) ^ K` drift. -/
theorem barrier2_eliahou_lifted_five_n_plus_one :
    Barriers.genIter 5 1 10 13 = 13 ∧
    (∀ j : Nat, j < 10 → Barriers.genIter 5 1 j 13 ≠ 1) ∧
    3 < 2966 ∧ 7 < 4701 ∧ 10 < 7667 ∧ 5 ^ 3 < 2 ^ 7 ∧ 3 ^ 3 < 2 ^ 7 :=
  ⟨Barriers.five_n_plus_one_cycle_13.1, Barriers.five_n_plus_one_cycle_13.2,
    by decide, by decide, by decide, by decide, by decide⟩

/-- **Barrier 3 Separation (`3n + 1` on `ℤ_{<0}`):** `n = -5` forms a non-trivial negative cycle
of odd length `2 < 2966`, halving count `3 < 4701`, and Collatz length `5 < 7667`, escaping
archimedean positivity `1 < n_min` and `3 ^ 2 < 2 ^ 3`. -/
theorem barrier3_eliahou_lifted_neg_int :
    Barriers.genIter 3 1 5 (-5) = -5 ∧
    (∀ j : Nat, j < 5 → Barriers.genIter 3 1 j (-5) ≠ 1) ∧
    2 < 2966 ∧ 3 < 4701 ∧ 5 < 7667 ∧ ¬ (3 ^ 2 < 2 ^ 3) :=
  ⟨Barriers.neg_int_cycle_neg5.1, Barriers.neg_int_cycle_neg5.2,
    by decide, by decide, by decide, by decide⟩

/-- **Barrier 4 Separation (`ℤ₂` rational cycles):** `1927 / 295 ∈ ℤ_(2) \ ℤ` (`K = 6 < 2966`,
`S = 10 < 4701`, `L = 16 < 7667`) and `211 / 13 ∈ ℤ_(2) \ ℤ` (`K = 5 < 2966`, `S = 8 < 4701`,
`L = 13 < 7667`) are genuine positive `2`-adic periodic orbits satisfying `3 ^ K < 2 ^ S` yet
violating global integrality in `ℕ⁺`. -/
theorem barrier4_eliahou_lifted_twoAdic :
    let v := [2, 2, 1, 2, 1, 2]
    let x := periodicPoint v (by decide)
    (x = ⟨1927, 295, by decide⟩ ∧ OddDenomRat.syracuseIter 6 x = x ∧
      3 ^ 6 < 2 ^ 10 ∧ 6 < 2966 ∧ 10 < 4701 ∧ 16 < 7667 ∧
      (¬ ∃ m : Int, x.Equiv (OddDenomRat.ofInt m))) ∧
    (periodicPoint [1, 1, 1, 1, 4] (by decide) = ⟨211, 13, by decide⟩ ∧
      OddDenomRat.syracuseIter 5 (periodicPoint [1, 1, 1, 1, 4] (by decide)) =
        periodicPoint [1, 1, 1, 1, 4] (by decide) ∧
      3 ^ 5 < 2 ^ 8 ∧ 5 < 2966 ∧ 8 < 4701 ∧ 13 < 7667) := by
  have hx : periodicPoint [2, 2, 1, 2, 1, 2] (by decide) = ⟨1927, 295, by decide⟩ := by decide
  have hb4 := barrier4_eliahou_twoAdic
  refine ⟨⟨hx, hb4.1.2.1, hb4.1.2.2.1, by decide, by decide, by decide, hb4.1.2.2.2.2.2.2⟩,
    ⟨hb4.2.1, hb4.2.2.1, hb4.2.2.2.1, by decide, by decide, by decide⟩⟩

/-- **Barrier 5 Separation (Conway 1972 / Finite Verification Horizon):** unconditional kernel
verification up to `2^20 = 1048576` lifts the unconditional cycle bound to `K ≥ 2966, L ≥ 7667`,
while higher bounds (`10^7 → K ≥ 10946`, `3 * 10^8 → K ≥ 16266`) remain contingent on further
finite stopping-time verification and global Diophantine / Baker bounds. -/
theorem barrier5_eliahou_lifted_conway_horizon :
    (∀ C : SyracuseCycle, 1048576 ≤ C.n_min ∧ 2966 ≤ C.k ∧ 7667 ≤ C.collatzLen) ∧
    ((∀ n : Nat, 2 ≤ n → n < 10000000 → HasFiniteStoppingTime n) →
      ∀ C : SyracuseCycle, 10946 ≤ C.k ∧ 28295 ≤ C.collatzLen) ∧
    ((∀ n : Nat, 2 ≤ n → n < 300000000 → HasFiniteStoppingTime n) →
      ∀ C : SyracuseCycle, 16266 ≤ C.k ∧ 42048 ≤ C.collatzLen) :=
  ⟨fun C => ⟨(unconditional_syracuseCycle_lifted_bounds C).1,
      (unconditional_syracuseCycle_lifted_bounds C).2.1,
      (unconditional_syracuseCycle_lifted_bounds C).2.2.2⟩,
    fun h C => ⟨(eliahou_cf_bounds_of_stopping_1e7 h C).1,
      (eliahou_cf_bounds_of_stopping_1e7 h C).2.2⟩,
    fun h C => ⟨(eliahou_cf_bounds_of_stopping_3e8 h C).1,
      (eliahou_cf_bounds_of_stopping_3e8 h C).2.2⟩⟩

end SolveCollatz
