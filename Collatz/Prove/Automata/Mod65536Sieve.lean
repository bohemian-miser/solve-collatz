/-
Copyright (c) 2026 The solve-collatz contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Collatz.Prove.Automata.SieveObstruction
public import Collatz.Known.EliahouLifted

/-!
# Kernel-Verified Mod-2^16 & Mod-2^18 Dyadic Covering (`PROVE-C1` Phase 3)
Pure Lean 4 core formalization extending `SieveObstruction`: parameterized dyadic sieve
`genDyadicUncovered` + `dyadicStrongCheck` (`EliahouLifted` `< 2^20`), `by decide` covering at
`mod 2^16` (`63,422 / 65,536`, `96.7743%`) & `mod 2^18` (`254,649 / 262,144`, `97.1409%`),
supermultiplicative survivor bounds (`7495^m <= uncoveredCount (18*m)`), `-65/49` `Z_2` tower,
and Barrier 1-5 separations (`3n-1`, `5n+1` mod-65536 collapse, `Z_<0`, `Z_2`, `REF-002`). -/

@[expose] public section
namespace SolveCollatz

/-! ### 1. Unified Dyadic Affine Covering Tree & Exact Counting Soundness -/
/-- Compressed `mul * n + 1` step on `Nat` (`mul = 3` gives `terrasStep`, `mul = 5` gives
`fiveStep`). -/
def mulStep (mul n : Nat) : Nat := if n % 2 = 0 then n / 2 else (mul * n + 1) / 2
/-- `k`-th iterate of `mulStep mul`. -/
def mulIter (mul : Nat) : Nat → Nat → Nat
  | 0, n => n | k + 1, n => mulIter mul k (mulStep mul n)
/-- Length-`k` parity vector under `mulStep mul`. -/
def mulParityVec (mul : Nat) : Nat → Nat → List Bool
  | 0, _ => [] | k + 1, n => (n % 2 == 1) :: mulParityVec mul k (mulStep mul n)
/-- Fast incremental loop checking `mul ^ c < 2 ^ k` over `1 <= k <= rem`. -/
def mulDropsLoop (mul rem cur pmul p2 : Nat) : Bool :=
  match rem with
  | 0 => false
  | rem + 1 =>
    let pm' := if cur % 2 == 1 then mul * pmul else pmul; let p2' := 2 * p2
    if pm' < p2' then true else mulDropsLoop mul rem (mulStep mul cur) pm' p2'
/-- Parameterized dyadic sieve counting surviving leaves at depth `k + rem` for `mul * n + 1`. -/
def genDyadicUncovered (mul rem k cur pmul p2 : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat)
    (fun k _ pmul p2 => cond (and (Nat.ble 1 k) (Nat.ble (Nat.add pmul 1) p2)) 0 1)
    (fun _ ih k cur pmul p2 =>
      cond (and (Nat.ble 1 k) (Nat.ble (Nat.add pmul 1) p2)) 0
        (let k' := Nat.add k 1; let p2' := Nat.mul 2 p2; let cpm := Nat.add cur pmul
         cond (Nat.beq (Nat.mod cur 2) 0)
           (Nat.add (ih k' (Nat.div cur 2) pmul p2')
                    (ih k' (Nat.div (Nat.add (Nat.mul mul cpm) 1) 2) (Nat.mul mul pmul) p2'))
           (Nat.add (ih k' (Nat.div (Nat.add (Nat.mul mul cur) 1) 2) (Nat.mul mul pmul) p2')
                    (ih k' (Nat.div cpm 2) pmul p2'))))
    rem k cur pmul p2
/-- Recursive dyadic checker verifying `cur + p3 < r + p2` at every pruned node for `3n + 1`. -/
def dyadicStrongCheck (rem k r cur p3 p2 : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Bool)
    (fun k r cur p3 p2 =>
      cond (and (Nat.ble 1 k) (Nat.ble (Nat.add p3 1) p2))
        (Nat.ble (Nat.add (Nat.add cur p3) 1) (Nat.add r p2)) true)
    (fun _ ih k r cur p3 p2 =>
      cond (and (Nat.ble 1 k) (Nat.ble (Nat.add p3 1) p2))
        (Nat.ble (Nat.add (Nat.add cur p3) 1) (Nat.add r p2))
        (let k' := Nat.add k 1; let p2' := Nat.mul 2 p2
         let cp3 := Nat.add cur p3; let rp2 := Nat.add r p2
         cond (Nat.beq (Nat.mod cur 2) 0)
           (and (ih k' r (Nat.div cur 2) p3 p2')
                (ih k' rp2 (Nat.div (Nat.add (Nat.mul 3 cp3) 1) 2) (Nat.mul 3 p3) p2'))
           (and (ih k' r (Nat.div (Nat.add (Nat.mul 3 cur) 1) 2) (Nat.mul 3 p3) p2')
                (ih k' rp2 (Nat.div cp3 2) p3 p2'))))
    rem k r cur p3 p2
private theorem countBelow_two_mul (p : Nat → Bool) (m : Nat) : countBelow p (2 * m) =
    countBelow (fun q => p (2 * q)) m + countBelow (fun q => p (2 * q + 1)) m := by
  induction m with | zero => rfl | succ m ih =>
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, countBelow, countBelow, countBelow,
      countBelow, ih]; omega
private theorem countPow2_split_parity (p : Nat → Bool) (d : Nat) : countPow2 p (d + 1) 0 =
    countPow2 (fun q => p (2 * q)) d 0 + countPow2 (fun q => p (2 * q + 1)) d 0 := by
  have h1 := countBelow_add_two_pow p (d + 1) 0
  have h2 := countBelow_add_two_pow (fun q => p (2 * q)) d 0
  have h3 := countBelow_add_two_pow (fun q => p (2 * q + 1)) d 0
  simp only [Nat.zero_add, countBelow] at h1 h2 h3
  rw [← h1, ← h2, ← h3, Nat.pow_succ, Nat.mul_comm (2 ^ d) 2, countBelow_two_mul]
private theorem countPow2_zero_of_all_false (p : Nat → Bool) (d lo : Nat)
    (h : ∀ q : Nat, p q = false) : countPow2 p d lo = 0 := by
  induction d generalizing lo with
  | zero => simp [countPow2, h lo] | succ _ ih => simp [countPow2, ih lo, ih (lo + 2 ^ _)]
private theorem mulIter_add (mul k m n : Nat) :
    mulIter mul m (mulIter mul k n) = mulIter mul (k + m) n := by
  induction k generalizing n with | zero => simp [mulIter] | succ _ ih =>
    simp only [mulIter, Nat.succ_add]; exact ih (mulStep mul n)
private theorem mulParityVec_add (mul k m n : Nat) : mulParityVec mul (k + m) n =
    mulParityVec mul k n ++ mulParityVec mul m (mulIter mul k n) := by
  induction k generalizing n with | zero => simp [mulParityVec, mulIter] | succ _ ih =>
    simp only [Nat.succ_add, mulParityVec, mulIter, List.cons_append]; rw [ih]
private theorem mulParityVec_mod_two_pow {mul : Nat} (_hmul : mul % 2 = 1) (k n q : Nat) :
    mulParityVec mul k (n + 2 ^ k * q) = mulParityVec mul k n ∧
    mulIter mul k (n + 2 ^ k * q) =
      mulIter mul k n + mul ^ countOnes (mulParityVec mul k n) * q := by
  induction k generalizing n q with
  | zero => simp [mulParityVec, mulIter, countOnes]
  | succ k ih =>
    have hm : 2 ^ (k + 1) * q = 2 * (2 ^ k * q) := by
      rw [Nat.pow_succ, Nat.mul_comm _ 2, Nat.mul_assoc]
    have hmod : (n + 2 ^ (k + 1) * q) % 2 = n % 2 := by rw [hm, Nat.add_mul_mod_self_left]
    have hhead : ((n + 2 ^ (k + 1) * q) % 2 == 1) = (n % 2 == 1) := by rw [hmod]
    by_cases he : n % 2 = 0
    · have hst : mulStep mul (n + 2 ^ (k + 1) * q) = mulStep mul n + 2 ^ k * q := by
        rw [mulStep, mulStep, ite_eq_left (hmod.trans he), ite_eq_left he, hm]
        exact Nat.add_mul_div_left n (2 ^ k * q) (by decide : 0 < 2)
      have hb : (n % 2 == 1) = false := by rw [he]; rfl
      have hih := ih (mulStep mul n) q
      exact ⟨by simp [mulParityVec, hhead, hst, hih.1],
        by simp [mulIter, hst, hih.2, mulParityVec, countOnes, hb]⟩
    · have hodd : n % 2 = 1 := by omega
      have hst : mulStep mul (n + 2 ^ (k + 1) * q) = mulStep mul n + 2 ^ k * (mul * q) := by
        rw [mulStep, mulStep, ite_eq_right (by omega : (n + 2 ^ (k + 1) * q) % 2 ≠ 0),
          ite_eq_right he]
        rw [show mul * (n + 2 ^ (k + 1) * q) + 1 = (mul * n + 1) + 2 * (2 ^ k * (mul * q)) by
          rw [hm, Nat.mul_add, Nat.mul_left_comm mul 2, Nat.mul_left_comm mul (2 ^ k)]; omega]
        exact Nat.add_mul_div_left (mul * n + 1) (2 ^ k * (mul * q)) (by decide : 0 < 2)
      have hih := ih (mulStep mul n) (mul * q)
      refine ⟨by simp [mulParityVec, hhead, hst, hih.1], ?_⟩
      simp only [mulIter, hst, hih.2, mulParityVec, countOnes, beq_iff_eq.mpr hodd, ↓reduceIte]
      rw [Nat.add_comm 1 _, Nat.pow_succ, Nat.mul_assoc]
private theorem mul_child_left (mul k r : Nat) :
    (mulIter mul k r % 2 = 0 →
      mulIter mul (k + 1) r = mulIter mul k r / 2 ∧
      mul ^ countOnes (mulParityVec mul (k + 1) r) = mul ^ countOnes (mulParityVec mul k r)) ∧
    (mulIter mul k r % 2 ≠ 0 →
      mulIter mul (k + 1) r = (mul * mulIter mul k r + 1) / 2 ∧
      mul ^ countOnes (mulParityVec mul (k + 1) r) =
        mul * mul ^ countOnes (mulParityVec mul k r)) := by
  have hvec : mulParityVec mul (k + 1) r =
      mulParityVec mul k r ++ [(mulIter mul k r % 2 == 1)] := by
    simpa [mulParityVec] using mulParityVec_add mul k 1 r
  refine ⟨fun hev => ⟨?_, ?_⟩, fun hne => ⟨?_, ?_⟩⟩
  · rw [← mulIter_add mul k 1 r]; simp [mulIter, mulStep, hev]
  · have hb : (mulIter mul k r % 2 == 1) = false := by rw [hev]; rfl
    rw [hvec, countOnes_append, hb]; simp [countOnes]
  · rw [← mulIter_add mul k 1 r]; simp [mulIter, mulStep, hne]
  · have hb : (mulIter mul k r % 2 == 1) = true := beq_iff_eq.mpr (by omega)
    rw [hvec, countOnes_append, hb]; simp [countOnes, Nat.pow_succ, Nat.mul_comm]
private theorem mul_child_right {mul : Nat} (hmul : mul % 2 = 1) (k r : Nat) :
    let cpm := mulIter mul k r + mul ^ countOnes (mulParityVec mul k r)
    let pm := mul ^ countOnes (mulParityVec mul k r)
    (mulIter mul k r % 2 = 0 →
      mulIter mul (k + 1) (r + 2 ^ k) = (mul * cpm + 1) / 2 ∧
      mul ^ countOnes (mulParityVec mul (k + 1) (r + 2 ^ k)) = mul * pm) ∧
    (mulIter mul k r % 2 ≠ 0 →
      mulIter mul (k + 1) (r + 2 ^ k) = cpm / 2 ∧
      mul ^ countOnes (mulParityVec mul (k + 1) (r + 2 ^ k)) = pm) := by
  have hcong := mulParityVec_mod_two_pow hmul k r 1; simp only [Nat.mul_one] at hcong
  have hpar := mul_child_left mul k (r + 2 ^ k)
  have hmodd : (mul ^ countOnes (mulParityVec mul k r)) % 2 = 1 := by
    induction countOnes (mulParityVec mul k r) with
    | zero => rfl | succ c ih => rw [Nat.pow_succ, Nat.mul_mod, hmul, ih]
  refine ⟨fun hev => ?_, fun hne => ?_⟩
  · rcases hpar.2 (by rw [hcong.2]; omega) with ⟨h1, h2⟩
    rw [hcong.2] at h1; rw [hcong.1] at h2; exact ⟨h1, h2⟩
  · rcases hpar.1 (by rw [hcong.2]; omega) with ⟨h1, h2⟩
    rw [hcong.2] at h1; rw [hcong.1] at h2; exact ⟨h1, h2⟩
private theorem mulDropsLoop_iff (mul rem j r : Nat) :
    mulDropsLoop mul rem (mulIter mul j r) (mul ^ countOnes (mulParityVec mul j r)) (2 ^ j) =
        true ↔
      ∃ k : Nat, j + 1 ≤ k ∧ k ≤ j + rem ∧ mul ^ countOnes (mulParityVec mul k r) < 2 ^ k := by
  induction rem generalizing j with
  | zero => simp only [mulDropsLoop, Bool.false_eq_true, false_iff, not_exists, not_and]; omega
  | succ rem ih =>
    have hvec : mulParityVec mul (j + 1) r =
        mulParityVec mul j r ++ [(mulIter mul j r % 2 == 1)] := by
      simpa [mulParityVec] using mulParityVec_add mul j 1 r
    have hp : (if mulIter mul j r % 2 == 1 then mul * mul ^ countOnes (mulParityVec mul j r)
          else mul ^ countOnes (mulParityVec mul j r)) =
        mul ^ countOnes (mulParityVec mul (j + 1) r) := by
      rw [hvec, countOnes_append]
      cases (mulIter mul j r % 2 == 1) <;> simp [countOnes, Nat.pow_succ, Nat.mul_comm]
    dsimp only [mulDropsLoop]
    rw [hp, show 2 * 2 ^ j = 2 ^ (j + 1) by rw [Nat.pow_succ, Nat.mul_comm],
      show mulStep mul (mulIter mul j r) = mulIter mul (j + 1) r from mulIter_add mul j 1 r]
    by_cases hlt : mul ^ countOnes (mulParityVec mul (j + 1) r) < 2 ^ (j + 1)
    · simp only [hlt, ↓reduceIte, true_iff]; exact ⟨j + 1, Nat.le_refl _, by omega, hlt⟩
    · simp only [hlt, ↓reduceIte, ih (j + 1)]
      refine ⟨fun ⟨k, hk1, hk2, hc⟩ => ⟨k, by omega, by omega, hc⟩, fun ⟨k, hk1, hk2, hc⟩ => ?_⟩
      rcases Nat.eq_or_lt_of_le hk1 with rfl | hgt
      · exact absurd hc hlt
      · exact ⟨k, hgt, by omega, hc⟩
private def mulDropsWithin (mul K r : Nat) : Bool := mulDropsLoop mul K r 1 1
private theorem mulDropsWithin_iff (mul K r : Nat) :
    mulDropsWithin mul K r = true ↔
      ∃ k : Nat, 1 ≤ k ∧ k ≤ K ∧ mul ^ countOnes (mulParityVec mul k r) < 2 ^ k := by
  simpa [mulDropsWithin, mulIter, mulParityVec, countOnes] using mulDropsLoop_iff mul K 0 r
private theorem ble_add1_eq {a b : Nat} : Nat.ble (Nat.add a 1) b = true ↔ a + 1 ≤ b :=
  iff_of_eq Nat.ble_eq
private theorem ble_add1_add_eq {a b c d : Nat} :
    Nat.ble (Nat.add (Nat.add a b) 1) (Nat.add c d) = true ↔ a + b + 1 ≤ c + d :=
  iff_of_eq Nat.ble_eq
private theorem mulDropsWithin_add_two_pow {mul : Nat} (hmul : mul % 2 = 1) (K r q : Nat) :
    mulDropsWithin mul K (r + 2 ^ K * q) = mulDropsWithin mul K r := by
  apply Bool.eq_iff_iff.mpr; simp only [mulDropsWithin_iff]
  have hmod : ∀ {k}, k ≤ K → mulParityVec mul k (r + 2 ^ K * q) = mulParityVec mul k r := by
    intro k hk; have h := (mulParityVec_mod_two_pow hmul k r (2 ^ (K - k) * q)).1
    rw [← Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_of_le hk] at h; exact h
  constructor <;> rintro ⟨k, hk1, hkK, hlt⟩ <;> refine ⟨k, hk1, hkK, ?_⟩
  · rwa [hmod hkK] at hlt
  · rwa [hmod hkK]
private theorem mul_subtree_covered {mul : Nat} (hmul : mul % 2 = 1) {k r rem : Nat}
    (hk : 1 ≤ k) (hlt : mul ^ countOnes (mulParityVec mul k r) < 2 ^ k) :
    countPow2 (fun q => !mulDropsWithin mul (k + rem) (r + 2 ^ k * q)) rem 0 = 0 := by
  apply countPow2_zero_of_all_false; intro q
  rw [(mulDropsWithin_iff _ _ _).mpr ⟨k, hk, Nat.le_add_right k rem,
    by rw [(mulParityVec_mod_two_pow hmul k r q).1]; exact hlt⟩]; rfl
private theorem mul_guard_false (mul k r : Nat) (hunc : mulDropsWithin mul k r = false) :
    and (Nat.ble 1 k) (Nat.ble (Nat.add (mul ^ countOnes (mulParityVec mul k r)) 1) (2 ^ k)) =
      false := by
  cases h : and (Nat.ble 1 k) (Nat.ble (Nat.add (mul ^ countOnes (mulParityVec mul k r)) 1) (2 ^ k))
  · rfl
  · simp only [Bool.and_eq_true, ble_add1_eq] at h
    exact absurd ((mulDropsWithin_iff mul k r).mpr ⟨k, h.1, Nat.le_refl k, by omega⟩)
      (by rw [hunc]; decide)
private theorem mulDropsWithin_succ_false (mul k c : Nat) (hunc : mulDropsWithin mul k c = false)
    (hge : ¬ mul ^ countOnes (mulParityVec mul (k + 1) c) < 2 ^ (k + 1)) :
    mulDropsWithin mul (k + 1) c = false := by
  cases h : mulDropsWithin mul (k + 1) c
  · rfl
  · rcases (mulDropsWithin_iff mul (k + 1) c).mp h with ⟨j, hj1, hjK, hlt⟩
    rcases Nat.eq_or_lt_of_le hjK with rfl | hltj
    · exact absurd hlt hge
    · exact absurd ((mulDropsWithin_iff mul k c).mpr ⟨j, hj1, by omega, hlt⟩) (by rw [hunc]; decide)
private theorem genDyadicUncovered_child_eq {mul : Nat} (hmul : mul % 2 = 1) (rem k c : Nat)
    (huc : mulDropsWithin mul k c = false)
    (ih : ∀ c' : Nat, mulDropsWithin mul (k + 1) c' = false →
      genDyadicUncovered mul rem (k + 1) (mulIter mul (k + 1) c')
        (mul ^ countOnes (mulParityVec mul (k + 1) c')) (2 ^ (k + 1)) =
      countPow2 (fun q => !mulDropsWithin mul (k + 1 + rem) (c' + 2 ^ (k + 1) * q)) rem 0) :
    genDyadicUncovered mul rem (k + 1) (mulIter mul (k + 1) c)
      (mul ^ countOnes (mulParityVec mul (k + 1) c)) (2 ^ (k + 1)) =
    countPow2 (fun q => !mulDropsWithin mul (k + 1 + rem) (c + 2 ^ (k + 1) * q)) rem 0 := by
  by_cases hlt : mul ^ countOnes (mulParityVec mul (k + 1) c) < 2 ^ (k + 1)
  · rw [mul_subtree_covered hmul (Nat.succ_pos k) hlt]
    cases rem with
    | zero =>
      change cond (and (Nat.ble 1 (k + 1)) (Nat.ble (Nat.add _ 1) (2 ^ (k + 1)))) 0 1 = 0
      simp [Nat.ble_eq]; omega
    | succ _ =>
      change cond (and (Nat.ble 1 (k + 1)) (Nat.ble (Nat.add _ 1) (2 ^ (k + 1)))) 0 _ = 0
      simp [Nat.ble_eq]; omega
  · exact ih c (mulDropsWithin_succ_false mul k c huc hlt)
private theorem genDyadicUncovered_succ (mul rem k cur pmul p2 : Nat)
    (hg : and (Nat.ble 1 k) (Nat.ble (Nat.add pmul 1) p2) = false) :
    genDyadicUncovered mul (rem + 1) k cur pmul p2 =
      if cur % 2 = 0 then
        genDyadicUncovered mul rem (k + 1) (cur / 2) pmul (2 * p2) +
        genDyadicUncovered mul rem (k + 1) ((mul * (cur + pmul) + 1) / 2) (mul * pmul) (2 * p2)
      else
        genDyadicUncovered mul rem (k + 1) ((mul * cur + 1) / 2) (mul * pmul) (2 * p2) +
        genDyadicUncovered mul rem (k + 1) ((cur + pmul) / 2) pmul (2 * p2) := by
  change cond (and (Nat.ble 1 k) (Nat.ble (Nat.add pmul 1) p2)) 0
    (cond (Nat.beq (Nat.mod cur 2) 0) _ _) = _
  rw [hg, Bool.cond_false]; by_cases he : cur % 2 = 0
  · rw [show Nat.beq (Nat.mod cur 2) 0 = true from Nat.beq_eq.mpr he, Bool.cond_true,
      ite_eq_left he]; rfl
  · have hf : Nat.beq (Nat.mod cur 2) 0 = false := by
      change Nat.beq (cur % 2) 0 = false
      rcases Nat.mod_two_eq_zero_or_one cur with h0 | h1
      · exact absurd h0 he
      · rw [h1]; rfl
    rw [hf, Bool.cond_false, ite_eq_right he]; rfl
private theorem genDyadicUncovered_eq_branch {mul : Nat} (hmul : mul % 2 = 1) (rem k r : Nat)
    (hunc : mulDropsWithin mul k r = false) :
    genDyadicUncovered mul rem k (mulIter mul k r)
      (mul ^ countOnes (mulParityVec mul k r)) (2 ^ k) =
      countPow2 (fun q => !mulDropsWithin mul (k + rem) (r + 2 ^ k * q)) rem 0 := by
  induction rem generalizing k r with
  | zero =>
    change cond (and (Nat.ble 1 k)
        (Nat.ble (Nat.add (mul ^ countOnes (mulParityVec mul k r)) 1) (2 ^ k))) 0 1 = _
    rw [mul_guard_false mul k r hunc]; simp [countPow2, hunc]
  | succ rem ih =>
    have hsplit := countPow2_split_parity
      (fun q => !mulDropsWithin mul (k + (rem + 1)) (r + 2 ^ k * q)) rem
    have hL_eq : (fun q => !mulDropsWithin mul (k + (rem + 1)) (r + 2 ^ k * (2 * q))) =
        (fun q => !mulDropsWithin mul (k + 1 + rem) (r + 2 ^ (k + 1) * q)) := by
      funext q; rw [show k + (rem + 1) = k + 1 + rem by omega, Nat.pow_succ, ← Nat.mul_assoc]
    have hR_eq : (fun q => !mulDropsWithin mul (k + (rem + 1)) (r + 2 ^ k * (2 * q + 1))) =
        (fun q => !mulDropsWithin mul (k + 1 + rem) ((r + 2 ^ k) + 2 ^ (k + 1) * q)) := by
      funext q; rw [show k + (rem + 1) = k + 1 + rem by omega, Nat.pow_succ, Nat.mul_add,
        Nat.mul_one, ← Nat.mul_assoc, Nat.add_comm (2 ^ k * 2 * q) (2 ^ k), ← Nat.add_assoc]
    have huc_r : mulDropsWithin mul k (r + 2 ^ k) = false := by
      simpa [Nat.mul_one] using (mulDropsWithin_add_two_pow hmul k r 1).trans hunc
    have h2pow : 2 * 2 ^ k = 2 ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hsplit, hL_eq, hR_eq, genDyadicUncovered_succ _ _ _ _ _ _ (mul_guard_false mul k r hunc)]
    by_cases hev : mulIter mul k r % 2 = 0
    · rcases (mul_child_left mul k r).1 hev with ⟨hL1, hL2⟩
      rcases (mul_child_right hmul k r).1 hev with ⟨hR1, hR2⟩
      rw [ite_eq_left hev, h2pow]
      conv => lhs; arg 1; rw [← hL1, ← hL2]
      conv => lhs; arg 2; rw [← hR1, ← hR2]
      rw [genDyadicUncovered_child_eq hmul rem k r hunc (ih (k + 1)),
        genDyadicUncovered_child_eq hmul rem k (r + 2 ^ k) huc_r (ih (k + 1))]
    · rcases (mul_child_left mul k r).2 hev with ⟨hL1, hL2⟩
      rcases (mul_child_right hmul k r).2 hev with ⟨hR1, hR2⟩
      rw [ite_eq_right hev, h2pow]
      conv => lhs; arg 1; rw [← hL1, ← hL2]
      conv => lhs; arg 2; rw [← hR1, ← hR2]
      rw [genDyadicUncovered_child_eq hmul rem k r hunc (ih (k + 1)),
        genDyadicUncovered_child_eq hmul rem k (r + 2 ^ k) huc_r (ih (k + 1))]
private theorem mulDropsWithin_3_eq (K r : Nat) : mulDropsWithin 3 K r = dropsWithin K r := by
  rw [← fastDropsWithin_eq_dropsWithin]; change mulDropsLoop 3 K r 1 1 = fastDropsLoop K r 1 1
  have h : ∀ rem c p3 p2, mulDropsLoop 3 rem c p3 p2 = fastDropsLoop rem c p3 p2 := by
    intro rem; induction rem with | zero => intros; rfl | succ rem ih =>
      intro c p3 p2; rcases Nat.mod_two_eq_zero_or_one c with hc | hc <;>
        simp only [mulDropsLoop, fastDropsLoop, show mulStep 3 c = terrasStep c from rfl, hc]
      · by_cases hlt : p3 < 2 * p2 <;> simp [hlt, ih]
      · by_cases hlt : 3 * p3 < 2 * p2 <;> simp [hlt, ih]
  exact h K r 1 1
private theorem mulDropsWithin_5_eq (K r : Nat) : mulDropsWithin 5 K r = fiveDropsLoop K r 1 1 := by
  change mulDropsLoop 5 K r 1 1 = fiveDropsLoop K r 1 1
  have h : ∀ rem c p5 p2, mulDropsLoop 5 rem c p5 p2 = fiveDropsLoop rem c p5 p2 := by
    intro rem; induction rem with | zero => intros; rfl | succ rem ih =>
      intro c p5 p2; rcases Nat.mod_two_eq_zero_or_one c with hc | hc <;>
        simp only [mulDropsLoop, fiveDropsLoop, show mulStep 5 c = fiveStep c from rfl, hc]
      · by_cases hlt : p5 < 2 * p2 <;> simp [hlt, ih]
      · by_cases hlt : 5 * p5 < 2 * p2 <;> simp [hlt, ih]
  exact h K r 1 1
/-- **Exact Dyadic Uncovered Count Identity (`3n + 1`):** for every horizon `K`,
`uncoveredCount K = genDyadicUncovered 3 K 0 0 1 1`. -/
theorem uncoveredCount_eq_dyadicUncovered (K : Nat) :
    uncoveredCount K = genDyadicUncovered 3 K 0 0 1 1 := by
  have h := genDyadicUncovered_eq_branch (mul := 3) (by decide) K 0 0 rfl
  simp only [mulIter, mulParityVec, countOnes, Nat.pow_zero, Nat.zero_add, Nat.one_mul] at h
  have hc := countPow2_congr (p := fun q => !dropsWithin K q)
    (q := fun q => !mulDropsWithin 3 K q) K 0 (fun q _ _ => by rw [mulDropsWithin_3_eq])
  rw [uncoveredCount, hc, ← h]
/-- **Exact Dyadic Covered Count Identity (`3n + 1`):**
`coveredCount K = 2 ^ K - genDyadicUncovered 3 K 0 0 1 1`. -/
theorem coveredCount_eq_dyadicUncovered (K : Nat) :
    coveredCount K = 2 ^ K - genDyadicUncovered 3 K 0 0 1 1 := by
  have h := coveredCount_add_uncoveredCount K; rw [uncoveredCount_eq_dyadicUncovered] at h; omega
private theorem mod_two_pow_succ_cases (m k : Nat) :
    m % 2 ^ (k + 1) = m % 2 ^ k ∨ m % 2 ^ (k + 1) = m % 2 ^ k + 2 ^ k := by
  have hkpos := Nat.two_pow_pos k; have hlt := Nat.mod_lt m hkpos
  have hq := Nat.div_add_mod (m / 2 ^ k) 2; have hm := Nat.mod_add_div m (2 ^ k)
  rw [Nat.pow_succ 2 k]; rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ k) with h0 | h1
  · left; conv => lhs; rw [← hm, ← hq, h0, Nat.add_zero, ← Nat.mul_assoc]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  · right; conv => lhs; rw [← hm, ← hq, h1, Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc,
      Nat.add_comm _ (2 ^ k), ← Nat.add_assoc]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
private theorem mulIter3_eq (k r : Nat) :
    mulIter 3 k r = terrasIter k r ∧ mulParityVec 3 k r = terrasParityVec k r := by
  induction k generalizing r with
  | zero => exact ⟨rfl, rfl⟩
  | succ _ ih =>
    obtain ⟨h1, h2⟩ := ih (terrasStep r)
    exact ⟨by simpa [mulIter, terrasIter, show mulStep 3 r = terrasStep r from rfl] using h1,
      by simpa [mulParityVec, terrasParityVec, show mulStep 3 r = terrasStep r from rfl] using h2⟩
private theorem dyadicStrongCheck_child_step (rem k c : Nat) (hc : c < 2 ^ (k + 1))
    (hunc : dropsWithin k c = false)
    (hchk : dyadicStrongCheck rem (k + 1) c (terrasIter (k + 1) c)
      (3 ^ countOnes (terrasParityVec (k + 1) c)) (2 ^ (k + 1)) = true)
    (ih : ∀ c' : Nat, c' < 2 ^ (k + 1) → dropsWithin (k + 1) c' = false →
      dyadicStrongCheck rem (k + 1) c' (terrasIter (k + 1) c')
        (3 ^ countOnes (terrasParityVec (k + 1) c')) (2 ^ (k + 1)) = true →
      ∀ m : Nat, m % 2 ^ (k + 1) = c' → dropsWithin (k + 1 + rem) m = true →
        dropsWithinStrong (k + 1 + rem) m = true)
    {m : Nat} (hm : m % 2 ^ (k + 1) = c) (hd : dropsWithin (k + 1 + rem) m = true) :
    dropsWithinStrong (k + 1 + rem) m = true := by
  by_cases hlt : 3 ^ countOnes (terrasParityVec (k + 1) c) < 2 ^ (k + 1)
  · have hg : and (Nat.ble 1 (k + 1))
        (Nat.ble (Nat.add (3 ^ countOnes (terrasParityVec (k + 1) c)) 1) (2 ^ (k + 1))) =
        true := by simp only [Bool.and_eq_true, ble_add1_eq]; omega
    have hrem_lt : terrasIter (k + 1) c + 3 ^ countOnes (terrasParityVec (k + 1) c) <
        c + 2 ^ (k + 1) := by
      cases rem with
      | zero =>
        change cond (and (Nat.ble 1 (k + 1)) (Nat.ble (Nat.add _ 1) (2 ^ (k + 1))))
          (Nat.ble (Nat.add (Nat.add _ _) 1) (Nat.add c (2 ^ (k + 1)))) true = true at hchk
        rw [hg, Bool.cond_true, ble_add1_add_eq] at hchk; omega
      | succ _ =>
        change cond (and (Nat.ble 1 (k + 1)) (Nat.ble (Nat.add _ 1) (2 ^ (k + 1))))
          (Nat.ble (Nat.add (Nat.add _ _) 1) (Nat.add c (2 ^ (k + 1)))) _ = true at hchk
        rw [hg, Bool.cond_true, ble_add1_add_eq] at hchk; omega
    have hcs : checkDropsStrong (k + 1) (m % 2 ^ (k + 1)) = true := by
      rw [hm]; simp [checkDropsStrong, checkDropsAt, hc, hlt, hrem_lt]
    exact (dropsWithinStrong_iff (k + 1 + rem) m).mpr ⟨k + 1, Nat.succ_pos k, by omega, hcs⟩
  · have huc1 : dropsWithin (k + 1) c = false := by
      rw [← mulDropsWithin_3_eq]; exact mulDropsWithin_succ_false 3 k c
        (by rw [mulDropsWithin_3_eq, hunc]) (by rw [(mulIter3_eq (k + 1) c).2]; exact hlt)
    exact ih c hc huc1 hchk m hm hd
private theorem dyadicStrongCheck_succ (rem k r cur p3 p2 : Nat)
    (hg : and (Nat.ble 1 k) (Nat.ble (Nat.add p3 1) p2) = false) :
    dyadicStrongCheck (rem + 1) k r cur p3 p2 =
      if cur % 2 = 0 then
        and (dyadicStrongCheck rem (k + 1) r (cur / 2) p3 (2 * p2))
          (dyadicStrongCheck rem (k + 1) (r + p2) ((3 * (cur + p3) + 1) / 2) (3 * p3) (2 * p2))
      else
        and (dyadicStrongCheck rem (k + 1) r ((3 * cur + 1) / 2) (3 * p3) (2 * p2))
          (dyadicStrongCheck rem (k + 1) (r + p2) ((cur + p3) / 2) p3 (2 * p2)) := by
  change cond (and (Nat.ble 1 k) (Nat.ble (Nat.add p3 1) p2)) _
    (cond (Nat.beq (Nat.mod cur 2) 0) _ _) = _
  rw [hg, Bool.cond_false]
  by_cases he : cur % 2 = 0
  · have ht : Nat.beq (Nat.mod cur 2) 0 = true := by
      change Nat.beq (cur % 2) 0 = true; exact Nat.beq_eq.mpr he
    rw [ht, Bool.cond_true, ite_eq_left he]; rfl
  · have hf : Nat.beq (Nat.mod cur 2) 0 = false := by
      change Nat.beq (cur % 2) 0 = false
      rcases Nat.mod_two_eq_zero_or_one cur with h0 | h1
      · exact absurd h0 he
      · rw [h1]; rfl
    rw [hf, Bool.cond_false, ite_eq_right he]; rfl
private theorem dyadicStrongCheck_children (rem k r : Nat) (hunc : dropsWithin k r = false)
    (hchk : dyadicStrongCheck (rem + 1) k r (terrasIter k r)
      (3 ^ countOnes (terrasParityVec k r)) (2 ^ k) = true) :
    dyadicStrongCheck rem (k + 1) r (terrasIter (k + 1) r)
      (3 ^ countOnes (terrasParityVec (k + 1) r)) (2 ^ (k + 1)) = true ∧
    dyadicStrongCheck rem (k + 1) (r + 2 ^ k) (terrasIter (k + 1) (r + 2 ^ k))
      (3 ^ countOnes (terrasParityVec (k + 1) (r + 2 ^ k))) (2 ^ (k + 1)) = true := by
  have h2pow : 2 * 2 ^ k = 2 ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  have hgf : and (Nat.ble 1 k)
      (Nat.ble (Nat.add (3 ^ countOnes (terrasParityVec k r)) 1) (2 ^ k)) = false := by
    rw [← (mulIter3_eq k r).2]
    exact mul_guard_false 3 k r (by rw [mulDropsWithin_3_eq]; exact hunc)
  rw [dyadicStrongCheck_succ _ _ _ _ _ _ hgf] at hchk
  have hL := mul_child_left 3 k r; have hR := mul_child_right (mul := 3) (by decide) k r
  simp only [mulIter3_eq] at hL hR
  by_cases hev : terrasIter k r % 2 = 0
  · rw [ite_eq_left hev, Bool.and_eq_true] at hchk
    rcases hL.1 hev with ⟨hL1, hL2⟩; rcases hR.1 hev with ⟨hR1, hR2⟩
    exact ⟨by rw [hL1, hL2, ← h2pow]; exact hchk.1, by rw [hR1, hR2, ← h2pow]; exact hchk.2⟩
  · rw [ite_eq_right hev, Bool.and_eq_true] at hchk
    rcases hL.2 hev with ⟨hL1, hL2⟩; rcases hR.2 hev with ⟨hR1, hR2⟩
    exact ⟨by rw [hL1, hL2, ← h2pow]; exact hchk.1, by rw [hR1, hR2, ← h2pow]; exact hchk.2⟩
private theorem dyadicStrongCheck_branch (rem k r : Nat) (hr : r < 2 ^ k)
    (hunc : dropsWithin k r = false)
    (hchk : dyadicStrongCheck rem k r (terrasIter k r)
      (3 ^ countOnes (terrasParityVec k r)) (2 ^ k) = true) :
    ∀ m : Nat, m % 2 ^ k = r → dropsWithin (k + rem) m = true →
      dropsWithinStrong (k + rem) m = true := by
  induction rem generalizing k r with
  | zero => intro m hm hd; rw [Nat.add_zero, ← dropsWithin_mod_eq k m, hm, hunc] at hd; cases hd
  | succ rem ih =>
    intro m hm hd; obtain ⟨hLchk, hRchk⟩ := dyadicStrongCheck_children rem k r hunc hchk
    have hr_lt := Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by decide) (Nat.le_succ k))
    have hrp_lt : r + 2 ^ k < 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
    have huc_r : dropsWithin k (r + 2 ^ k) = false := by
      simpa [Nat.mul_one] using (dropsWithin_add_two_pow k r 1).trans hunc
    rw [show k + (rem + 1) = k + 1 + rem by omega] at hd ⊢
    rcases mod_two_pow_succ_cases m k with hL | hR
    · rw [hm] at hL; exact dyadicStrongCheck_child_step rem k r hr_lt hunc hLchk (ih (k + 1)) hL hd
    · rw [hm] at hR
      exact dyadicStrongCheck_child_step rem k (r + 2 ^ k) hrp_lt huc_r hRchk (ih (k + 1)) hR hd
/-- **Exact Counting & Unconditional Descent Soundness Theorem:**
if `genDyadicUncovered 3 K 0 0 1 1 = U`, `dyadicStrongCheck K 0 0 0 1 1 = true`, and `K <= 20`,
then `2 ^ K - U` residue classes mod `2 ^ K` are covered (`uncoveredCount K = U`), and every
`n >= 2` in any covered class has `HasFiniteStoppingTime n` (via `EliahouLifted` below `2^K`). -/
theorem dyadic_sieve_soundness (K U : Nat) (hK : K ≤ 20)
    (hU : genDyadicUncovered 3 K 0 0 1 1 = U)
    (hchk : dyadicStrongCheck K 0 0 0 1 1 = true) :
    coveredCount K = 2 ^ K - U ∧ uncoveredCount K = U ∧
      ∀ n : Nat, 2 ≤ n → dropsWithin K (n % 2 ^ K) = true → HasFiniteStoppingTime n := by
  refine ⟨by rw [coveredCount_eq_dyadicUncovered, hU],
    by rw [uncoveredCount_eq_dyadicUncovered, hU], fun n hn hdrop => ?_⟩
  by_cases hlt : n < 2 ^ K
  · have h20 : 2 ^ K ≤ 1048576 := by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hK
    exact small_lt_1048576_finiteStoppingTime hn (Nat.lt_of_lt_of_le hlt h20)
  · have hbr : dropsWithinStrong K (n % 2 ^ K) = true := by
      simpa using dyadicStrongCheck_branch K 0 0 (by decide) rfl
        (by simpa [terrasIter, terrasParityVec, countOnes] using hchk)
        (n % 2 ^ K) (Nat.mod_one _) (by simpa using hdrop)
    exact dropsWithinStrong_sound hbr rfl (Nat.le_of_not_lt hlt)

/-! ### 2. Flagship Kernel-Verified Covering Density (`mod 2^16` & `mod 2^18`) -/
private theorem mod65536_bundle : coveredCount 16 = 63422 ∧ uncoveredCount 16 = 2114 ∧
    ∀ n : Nat, 2 ≤ n → dropsWithin 16 (n % 65536) = true → HasFiniteStoppingTime n := by
  simpa using dyadic_sieve_soundness 16 2114 (by decide) (by decide) (by decide)
private theorem mod262144_bundle : coveredCount 18 = 254649 ∧ uncoveredCount 18 = 7495 ∧
    ∀ n : Nat, 2 ≤ n → dropsWithin 18 (n % 262144) = true → HasFiniteStoppingTime n := by
  simpa using dyadic_sieve_soundness 18 7495 (by decide) (by decide) (by decide)
/-- **Mod-65,536 (`2^16`) Uncovered Certificate:** `2,114 / 65,536` residues survive. -/
theorem sieve_mod65536_uncovered : uncoveredCount 16 = 2114 := mod65536_bundle.2.1
/-- **Mod-65,536 (`2^16`) Covered Certificate:** `63,422 / 65,536` (`96.7743%`) covered. -/
theorem sieve_mod65536_covered : coveredCount 16 = 63422 := by simpa using mod65536_bundle.1
/-- **Unconditional `mod 65,536` Covered Descent:** every `n >= 2` with
`dropsWithin 16 (n % 65536) = true` has finite Collatz stopping time. -/
theorem mod65536_covered_finiteStoppingTime {n : Nat} (hn : 2 ≤ n)
    (hdrop : dropsWithin 16 (n % 65536) = true) : HasFiniteStoppingTime n :=
  mod65536_bundle.2.2 n hn (by simpa using hdrop)
/-- **Mod-262,144 (`2^18`) Uncovered Certificate:** `7,495 / 262,144` residues survive. -/
theorem sieve_mod262144_uncovered : uncoveredCount 18 = 7495 := mod262144_bundle.2.1
/-- **Flagship Mod-262,144 (`2^18`) Covered Certificate:** `254,649 / 262,144` (`97.1409%`)
covered in Lean 4's kernel (`by decide`, zero `native_decide`), matching `REF-008`
`glide_hunter`. -/
theorem sieve_mod262144_covered : coveredCount 18 = 254649 := by simpa using mod262144_bundle.1
/-- **Flagship Unconditional `mod 262,144` Covered Descent:** every `n >= 2` with
`dropsWithin 18 (n % 262144) = true` has finite Collatz stopping time. -/
theorem mod262144_covered_finiteStoppingTime {n : Nat} (hn : 2 ≤ n)
    (hdrop : dropsWithin 18 (n % 262144) = true) : HasFiniteStoppingTime n :=
  mod262144_bundle.2.2 n hn (by simpa using hdrop)
/-- **Exact Rational Density Bounds (`mod 2^16` & `mod 2^18`):**
`coveredCount 16 > 96.77%` (`> 96.5%` target) and `coveredCount 18 > 97.14%`, strictly improving
`mod 4,096` (`94.48%`) -> `mod 65,536` (`96.77%`) -> `mod 262,144` (`97.14%`). -/
theorem covered_density_progression :
    coveredCount 16 * 10000 > 9677 * 65536 ∧ coveredCount 18 * 10000 > 9714 * 262144 ∧
    coveredCount 12 * 2 ^ 16 < coveredCount 16 * 2 ^ 12 ∧
    coveredCount 16 * 2 ^ 18 < coveredCount 18 * 2 ^ 16 := by
  rw [sieve_mod4096_covered, sieve_mod65536_covered, sieve_mod262144_covered]; decide
private theorem filter_length_le_of_imp {α : Type} (l : List α) {p q : α → Bool}
    (h : ∀ x ∈ l, p x = true → q x = true) : (l.filter p).length ≤ (l.filter q).length := by
  induction l with | nil => simp | cons x xs ih =>
    have ih' := ih fun y hy => h y (List.mem_cons_of_mem x hy)
    cases hp : p x
    · rw [List.filter_cons_of_neg (by simp [hp])]
      cases hq : q x
      · rw [List.filter_cons_of_neg (by simp [hq])]; exact ih'
      · rw [List.filter_cons_of_pos (by simp [hq]), List.length_cons]; omega
    · rw [List.filter_cons_of_pos (by simp [hp]),
        List.filter_cons_of_pos (by simp [h x List.mem_cons_self hp]),
        List.length_cons, List.length_cons]; omega
private theorem countBelow_eq_filter (p : Nat → Bool) (n : Nat) :
    countBelow p n = ((List.range n).filter p).length := by
  induction n with | zero => rfl | succ n ih =>
    rw [countBelow, List.range_succ, List.filter_append, List.length_append, ih]
    cases hp : p n <;> simp [hp]
private theorem pow_le_three_pow_of_drops_false {K r : Nat} (hr : r < 2 ^ K)
    (hunc : dropsWithin K r = false) : 2 ^ K ≤ 3 ^ countOnes (terrasParityVec K r) := by
  cases K with | zero => simp [terrasParityVec, countOnes] | succ k =>
    by_cases hlt : 3 ^ countOnes (terrasParityVec (k + 1) r) < 2 ^ (k + 1)
    · exact absurd ((dropsWithin_iff (k + 1) r).mpr ⟨k + 1, Nat.succ_pos k, Nat.le_refl _,
        by rw [Nat.mod_eq_of_lt hr]; simp [checkDropsAt, hr, hlt]⟩) (by rw [hunc]; decide)
    · exact Nat.le_of_not_lt hlt
/-- **Bridge to `TerrasDensity.badCount`:** cumulative uncovered classes never exceed single-horizon
bad classes (`uncoveredCount K <= badCount K` for all `K >= 1`). -/
theorem uncoveredCount_le_badCount (K : Nat) (_hK : 1 ≤ K) : uncoveredCount K ≤ badCount K := by
  rw [uncoveredCount_eq_countBelow, countBelow_eq_filter, badCount, countLt_eq_filter_range]
  refine filter_length_le_of_imp (List.range (2 ^ K)) fun r hr hunc => ?_
  simp only [Bool.not_eq_true'] at hunc
  simpa [badResidue] using pow_le_three_pow_of_drops_false (List.mem_range.mp hr) hunc

/-! ### 3. Sharpened Survivor Lower Bounds & Projective `Z_2` Towers -/
/-- Constructive concatenation residue `< 2 ^ (K + B)` joining `r mod 2^K` and `s mod 2^B`. -/
def joinParityResidue (K B r s : Nat) : Nat :=
  terrasVecWitness (terrasParityVec K r ++ terrasParityVec B s)
private theorem terrasParityVec_take {k m : Nat} (hk : k ≤ m) (n : Nat) :
    (terrasParityVec m n).take k = terrasParityVec k n := by
  induction k generalizing m n with | zero => rfl | succ _ ih =>
    cases m with | zero => omega | succ m => simp [terrasParityVec, ih (m := m) (by omega)]
private theorem take_append_ge {α : Type} {a b : List α} {k : Nat} (hk : a.length ≤ k) :
    (a ++ b).take k = a ++ b.take (k - a.length) := by
  induction a generalizing k with | nil => simp | cons _ _ ih =>
    cases k with | zero => simp at hk | succ _ => simp [ih (by simpa using hk)]
private theorem append_eq_of_length_eq {α : Type} {a b c d : List α} (hl : a.length = c.length)
    (h : a ++ b = c ++ d) : a = c ∧ b = d := by
  induction a generalizing c with
  | nil => cases c with | nil => exact ⟨rfl, h⟩ | cons _ _ => simp at hl
  | cons _ _ ih => cases c with | nil => simp at hl | cons _ _ =>
    simp only [List.length_cons, Nat.succ.injEq, List.cons_append, List.cons.injEq] at hl h
    rcases ih hl h.2 with ⟨h1, h2⟩; exact ⟨by rw [h.1, h1], h2⟩
private theorem joinParityResidue_spec (K B r s : Nat) :
    joinParityResidue K B r s < 2 ^ (K + B) ∧ terrasParityVec (K + B) (joinParityResidue K B r s) =
      terrasParityVec K r ++ terrasParityVec B s := by
  simpa [joinParityResidue, terrasParityVec_length] using
    terrasVecWitness_spec (terrasParityVec K r ++ terrasParityVec B s)
private theorem joinParityResidue_inj {K B r1 r2 s1 s2 : Nat}
    (hr1 : r1 < 2 ^ K) (hr2 : r2 < 2 ^ K) (hs1 : s1 < 2 ^ B) (hs2 : s2 < 2 ^ B)
    (heq : joinParityResidue K B r1 s1 = joinParityResidue K B r2 s2) : r1 = r2 ∧ s1 = s2 := by
  have h1 := (joinParityResidue_spec K B r1 s1).2
  have h2 := (joinParityResidue_spec K B r2 s2).2; rw [heq] at h1
  rcases append_eq_of_length_eq (by simp [terrasParityVec_length]) (h1.symm.trans h2) with ⟨v1, v2⟩
  exact ⟨terrasParityVec_inj_mod_two_pow hr1 hr2 v1, terrasParityVec_inj_mod_two_pow hs1 hs2 v2⟩
private theorem joinParityResidue_uncovered {K B r s : Nat} (hr : r < 2 ^ K) (_hs : s < 2 ^ B)
    (hur : dropsWithin K r = false) (hus : dropsWithin B s = false) :
    dropsWithin (K + B) (joinParityResidue K B r s) = false := by
  let u := joinParityResidue K B r s
  cases h : dropsWithin (K + B) u
  · rfl
  · exfalso; rcases (dropsWithin_iff (K + B) u).mp h with ⟨k, hk1, hkKB, hchk⟩
    simp only [checkDropsAt, Bool.and_eq_true, decide_eq_true_eq, terrasParityVec_mod_eq] at hchk
    have htake : terrasParityVec k u = (terrasParityVec K r ++ terrasParityVec B s).take k := by
      rw [← (joinParityResidue_spec K B r s).2, terrasParityVec_take hkKB u]
    by_cases hkK : k ≤ K
    · have hvec : terrasParityVec k u = terrasParityVec k r := by
        rw [htake, List.take_append_of_le_length (by rw [terrasParityVec_length]; exact hkK),
          terrasParityVec_take hkK r]
      have hd := (dropsWithin_iff K r).mpr ⟨k, hk1, hkK, by
        simp [checkDropsAt, Nat.mod_lt _ (Nat.two_pow_pos k), terrasParityVec_mod_eq,
          ← hvec, hchk.2]⟩
      rw [hur] at hd; exact absurd hd (by decide)
    · let j := k - K; have hj1 : 1 ≤ j := (by omega); have hjB : j ≤ B := (by omega)
      have hvec : terrasParityVec k u = terrasParityVec K r ++ terrasParityVec j s := by
        rw [htake, take_append_ge (by rw [terrasParityVec_length]; omega),
          terrasParityVec_length, terrasParityVec_take hjB s]
      have hj_le : 2 ^ j ≤ 3 ^ countOnes (terrasParityVec j s) := by
        by_cases hltj : 3 ^ countOnes (terrasParityVec j s) < 2 ^ j
        · exfalso; have hd := (dropsWithin_iff B s).mpr ⟨j, hj1, hjB, by
            simp [checkDropsAt, Nat.mod_lt _ (Nat.two_pow_pos j), terrasParityVec_mod_eq, hltj]⟩
          rw [hus] at hd; exact absurd hd (by decide)
        · exact Nat.le_of_not_lt hltj
      have hprod : 2 ^ k ≤ 3 ^ countOnes (terrasParityVec k u) := by
        rw [hvec, countOnes_append]; conv => lhs; rw [show k = K + j by omega, Nat.pow_add]
        rw [Nat.pow_add]; exact Nat.mul_le_mul (pow_le_three_pow_of_drops_false hr hur) hj_le
      omega
private theorem flatMap_map_length {α β γ : Type} (l1 : List α) (l2 : List β) (f : α → β → γ) :
    (l1.flatMap (fun a => l2.map (f a))).length = l1.length * l2.length := by
  induction l1 with
  | nil => simp
  | cons _ _ ih => simp [List.flatMap_cons, List.length_append, ih, Nat.succ_mul, Nat.add_comm]
private theorem nodup_map_inj' {α β : Type} {f : α → β} {l : List α} (hl : l.Nodup)
    (hinj : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) : (l.map f).Nodup := by
  induction l with | nil => simp | cons x _ ih =>
    rw [List.map_cons, List.nodup_cons]; rw [List.nodup_cons] at hl
    refine ⟨fun hm => ?_, ih hl.2 fun a ha b hb =>
      hinj a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb)⟩
    rcases List.mem_map.mp hm with ⟨y, hy, hxy⟩
    exact hl.1 ((hinj y (List.mem_cons_of_mem x hy) x List.mem_cons_self hxy) ▸ hy)
private theorem flatMap_map_nodup {α β γ : Type} {l1 : List α} {l2 : List β} {f : α → β → γ}
    (h1 : l1.Nodup) (h2 : l2.Nodup)
    (hinj : ∀ a1 ∈ l1, ∀ b1 ∈ l2, ∀ a2 ∈ l1, ∀ b2 ∈ l2, f a1 b1 = f a2 b2 → a1 = a2 ∧ b1 = b2) :
    (l1.flatMap (fun a => l2.map (f a))).Nodup := by
  induction l1 with | nil => simp | cons a _ ih =>
    rw [List.flatMap_cons, List.nodup_append]; rw [List.nodup_cons] at h1
    refine ⟨nodup_map_inj' h2 (fun _ hb1 _ hb2 h =>
        (hinj a List.mem_cons_self _ hb1 a List.mem_cons_self _ hb2 h).2),
      ih h1.2 (fun a1 ha1 b1 hb1 a2 ha2 b2 hb2 =>
        hinj a1 (List.mem_cons_of_mem a ha1) b1 hb1 a2 (List.mem_cons_of_mem a ha2) b2 hb2),
      fun _ hx _ hy hxy => ?_⟩
    rcases List.mem_map.mp hx with ⟨_, hb1, rfl⟩
    rcases List.mem_flatMap.mp hy with ⟨_, ha2, hy2⟩; rcases List.mem_map.mp hy2 with ⟨_, hb2, rfl⟩
    exact h1.1 ((hinj a List.mem_cons_self _ hb1 _ (List.mem_cons_of_mem a ha2) _ hb2 hxy).1 ▸ ha2)
private theorem nodup_length_le_subset' {α : Type} [BEq α] [LawfulBEq α] {l1 l2 : List α}
    (h1 : l1.Nodup) (hsub : ∀ x ∈ l1, x ∈ l2) : l1.length ≤ l2.length := by
  induction l1 generalizing l2 with | nil => simp | cons x _ ih =>
    rw [List.nodup_cons] at h1; have hx : x ∈ l2 := hsub x List.mem_cons_self
    have hlen := ih h1.2 fun y hy => (List.mem_erase_of_ne (fun h =>
      h1.1 (by subst h; exact hy))).mpr (hsub y (List.mem_cons_of_mem x hy))
    have := List.length_pos_of_mem hx; rw [List.length_erase_of_mem hx] at hlen
    simp only [List.length_cons]; omega
/-- **Supermultiplicative Survivor Law (`PROVE-C1` Phase 3):**
`uncoveredCount K * uncoveredCount B <= uncoveredCount (K + B)` for all `K, B : Nat`. -/
theorem uncoveredCount_supermul (K B : Nat) :
    uncoveredCount K * uncoveredCount B ≤ uncoveredCount (K + B) := by
  let lK := (List.range (2 ^ K)).filter (fun r => !dropsWithin K r)
  let lB := (List.range (2 ^ B)).filter (fun s => !dropsWithin B s)
  let lKB := (List.range (2 ^ (K + B))).filter (fun u => !dropsWithin (K + B) u)
  have hnd : (lK.flatMap (fun r => lB.map (joinParityResidue K B r))).Nodup :=
    flatMap_map_nodup (List.nodup_range.filter _) (List.nodup_range.filter _)
      fun _ hr1 _ hs1 _ hr2 _ hs2 heq => joinParityResidue_inj
        (List.mem_range.mp (List.mem_filter.mp hr1).1)
        (List.mem_range.mp (List.mem_filter.mp hr2).1)
        (List.mem_range.mp (List.mem_filter.mp hs1).1)
        (List.mem_range.mp (List.mem_filter.mp hs2).1) heq
  have hsub : ∀ u ∈ lK.flatMap (fun r => lB.map (joinParityResidue K B r)), u ∈ lKB := by
    intro _ hu; rcases List.mem_flatMap.mp hu with ⟨_, hr, hru⟩
    rcases List.mem_map.mp hru with ⟨_, hs, rfl⟩
    simp only [lK, lB, lKB, List.mem_filter, List.mem_range, Bool.not_eq_true'] at hr hs ⊢
    exact ⟨(joinParityResidue_spec K B _ _).1, joinParityResidue_uncovered hr.1 hs.1 hr.2 hs.2⟩
  have hlen := nodup_length_le_subset' hnd hsub; rw [flatMap_map_length] at hlen
  simp only [uncoveredCount_eq_countBelow, countBelow_eq_filter] at hlen ⊢; exact hlen
/-- Power amplification: `uncoveredCount B ^ m <= uncoveredCount (B * m)`. -/
theorem uncoveredCount_pow_le_mul (B m : Nat) : uncoveredCount B ^ m ≤ uncoveredCount (B * m) := by
  induction m with | zero => simp [uncoveredCount, countPow2, dropsWithin] | succ m ih =>
    rw [Nat.pow_succ, Nat.mul_succ]
    exact Nat.le_trans (Nat.mul_le_mul_right _ ih) (uncoveredCount_supermul (B * m) B)
/-- **Sharpened Exponential Survivor Lower Bounds (`PROVE-C1` Phase 3):**
`2114 ^ m <= uncoveredCount (16 * m)`, `7495 ^ m <= uncoveredCount (18 * m)`, and
`2 ^ (12 * m) <= uncoveredCount (18 * m)` (doubling Phase 2's `1/3` exponent to `2/3`). -/
theorem uncoveredCount_sharpened_lower_bounds (m : Nat) :
    2114 ^ m ≤ uncoveredCount (16 * m) ∧
    7495 ^ m ≤ uncoveredCount (18 * m) ∧ 2 ^ (12 * m) ≤ uncoveredCount (18 * m) := by
  have h18 : 7495 ^ m ≤ uncoveredCount (18 * m) := by
    simpa [sieve_mod262144_uncovered] using uncoveredCount_pow_le_mul 18 m
  refine ⟨by simpa [sieve_mod65536_uncovered] using uncoveredCount_pow_le_mul 16 m, h18,
    Nat.le_trans (by rw [Nat.pow_mul]; exact Nat.pow_le_pow_left (by decide) m) h18⟩
private theorem oddDenom_terrasIter_add' (k m : Nat) (a : OddDenomRat) :
    OddDenomRat.terrasIter m (OddDenomRat.terrasIter k a) = OddDenomRat.terrasIter (k + m) a := by
  induction k generalizing a with
  | zero => simp [OddDenomRat.terrasIter]
  | succ _ ih => simp only [OddDenomRat.terrasIter, Nat.succ_add]; exact ih _
private theorem oddDenom_terrasParityVec_add' (k m : Nat) (a : OddDenomRat) :
    OddDenomRat.terrasParityVec (k + m) a = OddDenomRat.terrasParityVec k a ++
        OddDenomRat.terrasParityVec m (OddDenomRat.terrasIter k a) := by
  induction k generalizing a with
  | zero => simp [OddDenomRat.terrasParityVec, OddDenomRat.terrasIter]
  | succ _ ih => simp [Nat.succ_add, OddDenomRat.terrasParityVec, OddDenomRat.terrasIter, ih]
private theorem periodic_terras_noncontracting' {a : OddDenomRat} {P : Nat} (hP : 0 < P)
    (hcyc : OddDenomRat.terrasIter P a = a)
    (hfull : 2 ^ P ≤ 3 ^ countOnes (OddDenomRat.terrasParityVec P a))
    (hrem : ∀ r : Nat, r < P → 2 ^ r ≤ 3 ^ countOnes (OddDenomRat.terrasParityVec r a))
    (j : Nat) : 2 ^ j ≤ 3 ^ countOnes (OddDenomRat.terrasParityVec j a) := by
  have hit : ∀ m : Nat, OddDenomRat.terrasIter (P * m) a = a := fun m => by
    induction m with | zero => rfl | succ _ ih =>
      rw [Nat.mul_succ, ← oddDenom_terrasIter_add', ih, hcyc]
  have hcnt : ∀ m : Nat, countOnes (OddDenomRat.terrasParityVec (P * m) a) =
      m * countOnes (OddDenomRat.terrasParityVec P a) := fun m => by
    induction m with | zero => simp [OddDenomRat.terrasParityVec, countOnes] | succ _ ih =>
      rw [Nat.mul_succ, oddDenom_terrasParityVec_add', hit, countOnes_append, ih, Nat.succ_mul]
  (conv => lhs; rw [← Nat.div_add_mod j P]); (conv => rhs; rw [← Nat.div_add_mod j P])
  rw [oddDenom_terrasParityVec_add', countOnes_append, hit, hcnt,
    Nat.pow_add, Nat.pow_add, Nat.pow_mul, Nat.mul_comm (j / P) _, Nat.pow_mul]
  exact Nat.mul_le_mul (Nat.pow_le_pow_left hfull (j / P)) (hrem (j % P) (Nat.mod_lt j hP))
/-- **New Projective `Z_2` Survivor Tower (`-65 / 49 in Z_(2) \ Z`):**
`periodicPoint [1, 1, 1, 2] = -65 / 49` generates an infinite projective tower of uncovered
residues (`dropsWithin K (x.residueModTwoPow K) = false`) for every depth `K >= 1`. -/
theorem twoAdic_neg65_over_49_tower_uncovered (K : Nat) (hK : 1 ≤ K) :
    let x := periodicPoint [1, 1, 1, 2] (by decide)
    dropsWithin K (x.residueModTwoPow K) = false ∧
      x.residueModTwoPow (K + 1) % 2 ^ K = x.residueModTwoPow K := by
  intro x; have hx : x = ⟨-65, 49, by decide⟩ := by decide
  have hrem : ∀ r : Nat, r < 5 → 2 ^ r ≤ 3 ^ countOnes (OddDenomRat.terrasParityVec r x) := by
    intro r hr; rw [hx]; match r, hr with | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => decide
  have ht := twoAdic_tower_uncovered (fun j _ => periodic_terras_noncontracting' (by decide)
    (by rw [hx]; decide) (by rw [hx]; decide) hrem j) K hK
  exact ⟨ht.2.2.2, ht.2.2.1⟩
private theorem neg5_tower_mem (K : Nat) (hK : 1 ≤ K) : dropsWithin K
    ((OddDenomRat.ofInt (-5)).residueModTwoPow K) = false := by
  simpa [twoAdic_cycle_neg5.1] using (twoAdic_neg5_tower_uncovered K hK).1
private theorem neg19_tower_mem (K : Nat) (hK : 1 ≤ K) : dropsWithin K
    ((⟨-19, 11, by decide⟩ : OddDenomRat).residueModTwoPow K) = false := by
  simpa [twoAdic_cycle_neg19_over_11.1] using (twoAdic_neg19_over_11_tower_uncovered K hK).1
private theorem neg65_tower_mem (K : Nat) (hK : 1 ≤ K) : dropsWithin K
    ((⟨-65, 49, by decide⟩ : OddDenomRat).residueModTwoPow K) = false := by
  simpa [show periodicPoint [1, 1, 1, 2] (by decide) = ⟨-65, 49, by decide⟩ by decide] using
    (twoAdic_neg65_over_49_tower_uncovered K hK).1
/-- **Explicit Mod-`2^16` & Mod-`2^18` Projective Survivors:** concrete surviving residue witnesses
at both `65,536` and `262,144` from `-1`, `-5`, `-19/11`, and `-65/49`. -/
theorem mod65536_and_mod262144_explicit_survivors : dropsWithin 16 65535 = false ∧
    dropsWithin 18 262143 = false ∧
    dropsWithin 16 ((OddDenomRat.ofInt (-5)).residueModTwoPow 16) = false ∧
    dropsWithin 18 ((OddDenomRat.ofInt (-5)).residueModTwoPow 18) = false ∧
    dropsWithin 16 ((⟨-19, 11, by decide⟩ : OddDenomRat).residueModTwoPow 16) = false ∧
    dropsWithin 18 ((⟨-19, 11, by decide⟩ : OddDenomRat).residueModTwoPow 18) = false ∧
    dropsWithin 16 ((⟨-65, 49, by decide⟩ : OddDenomRat).residueModTwoPow 16) = false ∧
    dropsWithin 18 ((⟨-65, 49, by decide⟩ : OddDenomRat).residueModTwoPow 18) = false :=
  ⟨sieve_misses_all_odd_class (K := 16) (by decide),
    sieve_misses_all_odd_class (K := 18) (by decide),
    neg5_tower_mem 16 (by decide), neg5_tower_mem 18 (by decide),
    neg19_tower_mem 16 (by decide), neg19_tower_mem 18 (by decide),
    neg65_tower_mem 16 (by decide), neg65_tower_mem 18 (by decide)⟩

/-! ### 4. Explicit Barrier Separations (`Barriers 1-5`) -/
private theorem fiveCoveredCount_eq_dyadic (K : Nat) :
    fiveCoveredCount K = 2 ^ K - genDyadicUncovered 5 K 0 0 1 1 := by
  have h := genDyadicUncovered_eq_branch (mul := 5) (by decide) K 0 0 rfl
  simp only [mulIter, mulParityVec, countOnes, Nat.pow_zero, Nat.zero_add, Nat.one_mul] at h
  have hc := countPow2_congr (p := fun q => !fiveDropsLoop K q 1 1)
    (q := fun q => !mulDropsWithin 5 K q) K 0 fun q _ _ => by rw [mulDropsWithin_5_eq]
  have hp : fiveCoveredCount K + countPow2 (fun q => !fiveDropsLoop K q 1 1) K 0 = 2 ^ K :=
    countPow2_add_compl _ K 0
  rw [hc, ← h] at hp; omega
/-- **Mod-65,536 `5n + 1` Density Collapse:** `fiveCoveredCount 16 = 50,216 / 65,536` (`76.62%`,
leaving `15,320` uncovered vs only `2,114` for `3n + 1`). -/
theorem five_sieve_mod65536_covered : fiveCoveredCount 16 = 50216 ∧
    fiveCoveredCount 16 * 1000 < 767 * 65536 ∧ fiveCoveredCount 16 < coveredCount 16 := by
  have h5 : genDyadicUncovered 5 16 0 0 1 1 = 15320 := by decide
  rw [fiveCoveredCount_eq_dyadic, h5, sieve_mod65536_covered]; decide
/-- **Barrier 1 Separation (`3n - 1` on `N+`):** `n = 5` lies in a mod-`2^18` covered class for
`3n + 1` (`dropsWithin 18 5 = true`, dropping under `3n + 1`), yet forms a non-trivial cycle
`5 -> 14 -> 7 -> 20 -> 10 -> 5` under `3n - 1`. -/
theorem barrier1_mod262144_three_n_minus_one : dropsWithin 18 (5 % 262144) = true ∧
    HasFiniteStoppingTime 5 ∧ Barriers.genIter 3 (-1) 5 5 = 5 ∧
    (∀ j : Nat, j < 5 → Barriers.genIter 3 (-1) j 5 ≠ 1) :=
  ⟨by decide, mod262144_covered_finiteStoppingTime (by decide) (by decide),
    Barriers.three_n_minus_one_cycle_5.1, Barriers.three_n_minus_one_cycle_5.2⟩
/-- **Barrier 2 Separation (`5n + 1` on `N+`):** mod-`65,536` covering density collapses from
`63,422` (`96.77%` for `3n + 1`) down to `50,216` (`76.62%` for `5n + 1`), while `> 50%` fail
at every `2 * m` and `n = 13` cycles under `5n + 1`. -/
theorem barrier2_mod65536_five_n_plus_one : fiveCoveredCount 16 = 50216 ∧
    coveredCount 16 = 63422 ∧ (∀ m : Nat, 1 ≤ m → 2 ^ (2 * m) < 2 * fiveBadCount (2 * m)) ∧
    Barriers.genIter 5 1 10 13 = 13 :=
  ⟨five_sieve_mod65536_covered.1, sieve_mod65536_covered,
    fun _ hm => fiveBadCount_even_gt_half hm, Barriers.five_n_plus_one_cycle_13.1⟩
/-- **Barrier 3 Separation (`3n + 1` on `Z_<0`):** `-5` escapes `2 <= n` positivity and forms a
5-step negative cycle while generating a mod-`2^18` uncovered projective `Z_2` tower. -/
theorem barrier3_mod262144_neg_int : Barriers.genIter 3 1 5 (-5) = -5 ∧
    (∀ j : Nat, j < 5 → Barriers.genIter 3 1 j (-5) ≠ 1) ∧
    dropsWithin 18 ((OddDenomRat.ofInt (-5)).residueModTwoPow 18) = false :=
  ⟨Barriers.neg_int_cycle_neg5.1, Barriers.neg_int_cycle_neg5.2,
    mod65536_and_mod262144_explicit_survivors.2.2.2.1⟩
/-- **Barrier 4 Separation (`Z_2` Non-Terminating Towers):** `-5`, `-19/11`, and `-65/49` remain
uncovered at every finite depth `K >= 1` (including `mod 65,536` and `mod 262,144`), while
`211/13` is a positive non-integral `2`-adic periodic orbit. -/
theorem barrier4_mod262144_twoAdic_towers : (∀ K : Nat, 1 ≤ K →
      dropsWithin K ((OddDenomRat.ofInt (-5)).residueModTwoPow K) = false ∧
      dropsWithin K ((⟨-19, 11, by decide⟩ : OddDenomRat).residueModTwoPow K) = false ∧
      dropsWithin K ((⟨-65, 49, by decide⟩ : OddDenomRat).residueModTwoPow K) = false) ∧
    OddDenomRat.syracuseIter 5 ⟨211, 13, by decide⟩ = ⟨211, 13, by decide⟩ :=
  ⟨fun K hK => ⟨neg5_tower_mem K hK, neg19_tower_mem K hK, neg65_tower_mem K hK⟩,
    by have h := twoAdic_cycle_211_over_13; simpa [h.1] using h.2.2.1⟩
/-- **Barrier 5 Separation (Conway `REF-002` Modular Covering Horizon):**
no finite depth `K >= 1` achieves `100%` covering (`1 <= uncoveredCount K`), `mod 2^18` leaves
`7,495` surviving classes, and survivors grow at least as `7495 ^ m <= uncoveredCount (18 * m)`. -/
theorem barrier5_mod262144_conway_obstruction :
    (∀ K : Nat, 1 ≤ K → 1 ≤ uncoveredCount K ∧ coveredCount K < 2 ^ K) ∧
    (uncoveredCount 18 = 7495 ∧ coveredCount 18 = 254649) ∧
    (∀ m : Nat, 7495 ^ m ≤ uncoveredCount (18 * m) ∧ 2 ^ (12 * m) ≤ uncoveredCount (18 * m)) :=
  ⟨no_finite_modulus_complete_sieve, ⟨sieve_mod262144_uncovered, sieve_mod262144_covered⟩,
    fun m => ⟨(uncoveredCount_sharpened_lower_bounds m).2.1,
      (uncoveredCount_sharpened_lower_bounds m).2.2⟩⟩

end SolveCollatz
