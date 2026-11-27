/-
Copyright (c) 2026 The solve-collatz contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Collatz.Known.SteinerConvergents
public import Collatz.Prove.Diophantine.MCircuit

/-!
# Unconditional 2-Circuit & `m`-Circuit Elimination via Continued Fractions (`PROVE-B1` Phase 4)

Pure Lean 4 core formalization (zero Mathlib, zero `sorry`, zero `native_decide`):
1. Orbit-wide `32768 ≤ syracuseIter i n` lower bounds (`306 ≤ K`, `485 ≤ S`, `791 ≤ K + S`).
2. Generalized `M`-valley bound `M^m * 2^S < (M+1)^m * 3^K`, forcing `S = minHalvings K`.
3. Two-circuit Simons-Legendre convergent exclusion (`(p₁₅,q₁₅) = (17087915, 10781274)`,
   `(p₁₆,q₁₆) = (85137581, 53715833)`), eliminating ALL 2-circuits for `K ≤ 64497106`
   UNCONDITIONALLY (`64497107 ≤ K`, `102225496 ≤ S`, `166722603 ≤ K + S`), bridged to `Challenge`.
4. Unconditional `m`-circuit elimination (`3`-circuits `K ≤ 14935`, `4`-circuits `K ≤ 14270`,
   `5`-circuits `K ≤ 13605`), conditional `M = 2^40` / `2^68` lifting, and Barriers 1-5.
-/

@[expose] public section

namespace SolveCollatz

/-! ### 1. Orbit-Wide `32768 ≤` Lower Bound & `SyracuseCycle` Lift for `m`-Circuits -/

private theorem syracuseIter_mul_add {K n : Nat} (hcyc : syracuseIter K n = n) :
    ∀ q r : Nat, syracuseIter (q * K + r) n = syracuseIter r n := by
  intro q r
  induction q with
  | zero => simp
  | succ q ih =>
    have hmul : (q + 1) * K + r = K + (q * K + r) := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    rw [hmul, ← syracuseIter_add K (q * K + r) n, hcyc, ih]

private theorem syracuseIter_mod_cycle {K n : Nat} (_hK : 0 < K)
    (hcyc : syracuseIter K n = n) (t : Nat) :
    syracuseIter t n = syracuseIter (t % K) n := by
  have hdiv : t / K * K + t % K = t := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod t K
  conv => lhs; rw [← hdiv]
  exact syracuseIter_mul_add hcyc (t / K) (t % K)

private theorem syracuseTotalVal_shift_cycle {K n : Nat} (hcyc : syracuseIter K n = n)
    (i₀ : Nat) : syracuseTotalVal K (syracuseIter i₀ n) = syracuseTotalVal K n := by
  have h1 := syracuseTotalVal_add i₀ K n
  have h2 := syracuseTotalVal_add K i₀ n
  rw [Nat.add_comm i₀ K] at h1
  rw [hcyc] at h2
  omega

/-- Construct a minimal-element `SyracuseCycle` from any non-trivial periodic Syracuse orbit
preserving the exact odd step count `K` and total halvings `syracuseTotalVal K n`. -/
theorem syracuseCycle_of_syracuse_cycle {n K : Nat} (hK : 0 < K) (_hn : 1 < n)
    (hcyc : syracuseIter K n = n) (hne : ∀ i : Nat, i < K → syracuseIter i n ≠ 1) :
    ∃ C : SyracuseCycle, C.k = K ∧ C.totalVal = syracuseTotalVal K n := by
  let f := fun i => syracuseIter i n
  rcases minFinVal_mem f (K - 1) with ⟨i₀, hi₀, hmin_eq⟩
  let n_min := minFinVal f (K - 1)
  have hn_odd : n % 2 = 1 := by rw [← hcyc]; exact syracuseIter_odd hK n
  have hmin_eq' : n_min = syracuseIter i₀ n := hmin_eq
  have hmin_le : ∀ t : Nat, n_min ≤ syracuseIter t n_min := by
    intro t
    have hstep : syracuseIter t n_min = syracuseIter (i₀ + t) n := by
      rw [hmin_eq', syracuseIter_add]
    rw [hstep, syracuseIter_mod_cycle hK hcyc]
    exact minFinVal_le f (K - 1) ((i₀ + t) % K) (by have := Nat.mod_lt (i₀ + t) hK; omega)
  have hne1 : n_min ≠ 1 := by rw [hmin_eq']; exact hne i₀ (by omega)
  have hodd : n_min % 2 = 1 := by rw [hmin_eq']; exact syracuseIter_odd_of_odd i₀ hn_odd
  have hcyc' : syracuseIter K n_min = n_min := by
    rw [hmin_eq', syracuseIter_add, Nat.add_comm i₀ K, ← syracuseIter_add, hcyc]
  refine ⟨⟨n_min, K, by omega, hodd, hK, hcyc', hmin_le⟩, rfl, ?_⟩
  simp only [SyracuseCycle.totalVal]; rw [hmin_eq']
  exact syracuseTotalVal_shift_cycle hcyc i₀

/-- Lifting stopping-time verification `< M` to an orbit-wide lower bound `M ≤ syracuseIter i n`
for any `IsMCircuitCycle cs n`. -/
theorem mCircuit_orbit_ge_of_stopping {cs : List (Nat × Nat)} {n M : Nat}
    (hstop : ∀ m : Nat, 2 ≤ m → m < M → HasFiniteStoppingTime m)
    (h : IsMCircuitCycle cs n) (i : Nat) : M ≤ syracuseIter i n := by
  let m := syracuseIter i n
  have hpos : 0 < m := by have := (mCircuit_valley_three_le h i).2; omega
  have hodd : m % 2 = 1 := (mCircuit_valley_three_le h i).1
  have hper : syracuseIter (mCircuitK cs) m = m := by
    dsimp only [m]; rw [syracuseIter_add, Nat.add_comm i, ← syracuseIter_add, h.period_eq]
  let L := syracuseTotalVal (mCircuitK cs) m + mCircuitK cs
  have hL : 0 < L := by have := h.mCircuitK_pos; omega
  have hcol : collatzIter L m = m := by
    dsimp only [L]; rw [collatzIter_eq_syracuseIter _ hodd, hper]
  have hne : ∀ j : Nat, j < L → collatzIter j m ≠ 1 := by
    intro j hj
    refine collatzIter_ne_one_of_syracuseIter (mCircuitK cs) hodd ?_ j hj
    intro r _ hr1
    have hle := (syracuseIter_three_le_of_cycle h.mCircuitK_pos h.one_lt_n h.period_eq (i + r)).2
    rw [← syracuseIter_add, hr1] at hle; omega
  exact collatz_cycle_elem_ge_of_stopping M hstop hpos hL hcol hne

/-- Every iterate `syracuseIter i n` along a non-trivial `m`-circuit cycle satisfies
`32768 ≤ syracuseIter i n` unconditionally. -/
theorem mCircuit_orbit_ge_32768 {cs : List (Nat × Nat)} {n : Nat}
    (h : IsMCircuitCycle cs n) (i : Nat) : 32768 ≤ syracuseIter i n :=
  mCircuit_orbit_ge_of_stopping (fun _ h2 hlt => small_lt_32768_finiteStoppingTime h2 hlt) h i

/-- Unconditional `EliahouConvergents` lower bounds for any `IsMCircuitCycle`:
`32768 ≤ n`, `306 ≤ mCircuitK cs`, `485 ≤ mCircuitS cs`, and `791 ≤ mCircuitK cs + mCircuitS cs`. -/
theorem mCircuit_unconditional_eliahou_bounds {cs : List (Nat × Nat)} {n : Nat}
    (h : IsMCircuitCycle cs n) :
    32768 ≤ n ∧ 306 ≤ mCircuitK cs ∧ 485 ≤ mCircuitS cs ∧
      791 ≤ mCircuitK cs + mCircuitS cs := by
  have hne : ∀ i : Nat, i < mCircuitK cs → syracuseIter i n ≠ 1 := by
    intro i _; have hle := (mCircuit_valley_three_le h i).2; omega
  rcases syracuseCycle_of_syracuse_cycle h.mCircuitK_pos h.one_lt_n h.period_eq hne with
    ⟨C, hCk, hCS⟩
  have hk := unconditional_syracuseCycle_odd_length_ge_306 C
  have hs := unconditional_syracuseCycle_halvings_ge_485 C
  have hlen := unconditional_syracuseCycle_collatzLen_ge_791 C
  have hS_eq : C.totalVal = mCircuitS cs := by rw [hCS, h.totalVal_eq]
  have h32k := mCircuit_orbit_ge_32768 h 0
  simp only [syracuseIter] at h32k
  refine ⟨h32k, ?_, ?_, ?_⟩
  · rwa [← hCk]
  · rwa [← hS_eq]
  · rw [← hCk, ← hS_eq]; simpa [SyracuseCycle.collatzLen, Nat.add_comm] using hlen

/-- Unconditional lower bounds for any 2-circuit (`32768 ≤ n, m`, `306 ≤ K`, `485 ≤ S`). -/
theorem twoCircuit_unconditional_eliahou_bounds {n k₁ e₁ k₂ e₂ : Nat}
    (h : IsTwoCircuitCycle n k₁ e₁ k₂ e₂) :
    32768 ≤ n ∧ 32768 ≤ syracuseIter k₁ n ∧ 306 ≤ k₁ + k₂ ∧
      485 ≤ k₁ + k₂ + e₁ + e₂ - 2 ∧ 791 ≤ (k₁ + k₂) + (k₁ + k₂ + e₁ + e₂ - 2) := by
  have hm := isTwoCircuitCycle_iff_isMCircuitCycle.mp h
  have hbd := mCircuit_unconditional_eliahou_bounds hm
  have hmid := mCircuit_orbit_ge_32768 hm k₁
  have hS : mCircuitS [(k₁, e₁), (k₂, e₂)] = k₁ + k₂ + e₁ + e₂ - 2 := by
    have hk₁ := h.k₁_pos; have hk₂ := h.k₂_pos; simp only [mCircuitS]; omega
  have hK : mCircuitK [(k₁, e₁), (k₂, e₂)] = k₁ + k₂ := by
    simp only [mCircuitK, List.map, List.sum_cons, List.sum_nil]; omega
  rw [hK, hS] at hbd
  exact ⟨hbd.1, hmid, hbd.2.1, hbd.2.2.1, hbd.2.2.2⟩

/-- Unconditional lower bounds for any 3-circuit (`32768 ≤ n, m₁, m₂`, `306 ≤ K`, `485 ≤ S`). -/
theorem threeCircuit_unconditional_eliahou_bounds {n k₁ e₁ k₂ e₂ k₃ e₃ : Nat}
    (h : IsThreeCircuitCycle n k₁ e₁ k₂ e₂ k₃ e₃) :
    32768 ≤ n ∧ 32768 ≤ syracuseIter k₁ n ∧ 32768 ≤ syracuseIter (k₁ + k₂) n ∧
      306 ≤ k₁ + k₂ + k₃ ∧ 485 ≤ k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3 ∧
      791 ≤ (k₁ + k₂ + k₃) + (k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3) := by
  have hm := isThreeCircuitCycle_iff_isMCircuitCycle.mp h
  have hbd := mCircuit_unconditional_eliahou_bounds hm
  have hv1 := mCircuit_orbit_ge_32768 hm k₁
  have hv2 := mCircuit_orbit_ge_32768 hm (k₁ + k₂)
  have hS : mCircuitS [(k₁, e₁), (k₂, e₂), (k₃, e₃)] =
      k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3 := by
    have hk₁ := h.k₁_pos; have hk₂ := h.k₂_pos; have hk₃ := h.k₃_pos
    simp only [mCircuitS]; omega
  have hK : mCircuitK [(k₁, e₁), (k₂, e₂), (k₃, e₃)] = k₁ + k₂ + k₃ := by
    simp only [mCircuitK, List.map, List.sum_cons, List.sum_nil]; omega
  rw [hK, hS] at hbd
  exact ⟨hbd.1, hv1, hv2, hbd.2.1, hbd.2.2.1, hbd.2.2.2⟩

/-! ### 2. Generalized `M`-Valley `m`-Circuit Band Bound & Sharp `S = minHalvings K` -/

private theorem mul_four_rearrange_p4 (a b c d : Nat) :
    (a * b) * (c * d) = (a * c) * (b * d) := by
  rw [Nat.mul_assoc, Nat.mul_left_comm b c d, ← Nat.mul_assoc]

private theorem oneCircuit_block_M_le {k e a M : Nat} (hk : 1 ≤ k) (hMpos : 0 < M)
    (ha : M ≤ a) (hvec : syracuseValVec k a = oneCircuitVec (k - 1) e) :
    M * 2 ^ (k + e - 1) * syracuseIter k a < (M + 1) * 3 ^ k * a := by
  have haff := syracuse_affine_vec_eq k a
  rw [hvec, paritySum_oneCircuitVec, parityOffset_oneCircuitVec] at haff
  have hsub : k - 1 + e = k + e - 1 := by omega
  have hinc : k - 1 + 1 = k := by omega
  rw [hsub, hinc] at haff
  have h23 : 2 ^ k < 3 ^ k := two_pow_lt_three_pow hk
  have hlt : 2 ^ (k + e - 1) * syracuseIter k a < 3 ^ k * (a + 1) := by
    have := Nat.two_pow_pos k; rw [haff, Nat.mul_add, Nat.mul_one]; omega
  have hMa : M * (a + 1) ≤ (M + 1) * a := by
    rw [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]; omega
  calc M * 2 ^ (k + e - 1) * syracuseIter k a
      = M * (2 ^ (k + e - 1) * syracuseIter k a) := by rw [Nat.mul_assoc]
    _ < M * (3 ^ k * (a + 1)) := (Nat.mul_lt_mul_left hMpos).mpr hlt
    _ = 3 ^ k * (M * (a + 1)) := by rw [Nat.mul_left_comm]
    _ ≤ 3 ^ k * ((M + 1) * a) := Nat.mul_le_mul_left _ hMa
    _ = (M + 1) * 3 ^ k * a := by rw [Nat.mul_left_comm, ← Nat.mul_assoc]

private theorem mCircuit_path_M_step {k e M : Nat} {rest : List (Nat × Nat)} {a : Nat}
    (hk : 1 ≤ k) (hMpos : 0 < M) (haM : M ≤ a)
    (hv1 : syracuseValVec k a = oneCircuitVec (k - 1) e)
    (hih : M ^ rest.length * 2 ^ mCircuitS rest *
        syracuseIter (mCircuitK rest) (syracuseIter k a) ≤
      (M + 1) ^ rest.length * 3 ^ mCircuitK rest * syracuseIter k a) :
    M ^ ((k, e) :: rest).length * 2 ^ mCircuitS ((k, e) :: rest) *
      syracuseIter (mCircuitK ((k, e) :: rest)) a <
    (M + 1) ^ ((k, e) :: rest).length * 3 ^ mCircuitK ((k, e) :: rest) * a := by
  have hblk := oneCircuit_block_M_le hk hMpos haM hv1
  have hc_pos : 0 < (M + 1) ^ rest.length * 3 ^ mCircuitK rest :=
    Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by decide))
  have hstrict :
      M ^ (rest.length + 1) * 2 ^ ((k + e - 1) + mCircuitS rest) *
        syracuseIter (mCircuitK rest) (syracuseIter k a) <
      (M + 1) ^ (rest.length + 1) * 3 ^ (k + mCircuitK rest) * a := by
    calc M ^ (rest.length + 1) * 2 ^ ((k + e - 1) + mCircuitS rest) *
          syracuseIter (mCircuitK rest) (syracuseIter k a)
        = (M * 2 ^ (k + e - 1)) * (M ^ rest.length * 2 ^ mCircuitS rest *
            syracuseIter (mCircuitK rest) (syracuseIter k a)) := by
            rw [Nat.pow_succ, Nat.pow_add, Nat.mul_comm (M ^ rest.length) M,
              mul_four_rearrange_p4, Nat.mul_assoc]
      _ ≤ (M * 2 ^ (k + e - 1)) *
            ((M + 1) ^ rest.length * 3 ^ mCircuitK rest * syracuseIter k a) :=
            Nat.mul_le_mul_left _ hih
      _ = ((M + 1) ^ rest.length * 3 ^ mCircuitK rest) *
            (M * 2 ^ (k + e - 1) * syracuseIter k a) := by
            rw [Nat.mul_left_comm (M * 2 ^ (k + e - 1))]
      _ < ((M + 1) ^ rest.length * 3 ^ mCircuitK rest) * ((M + 1) * 3 ^ k * a) :=
            (Nat.mul_lt_mul_left hc_pos).mpr hblk
      _ = (M + 1) ^ (rest.length + 1) * 3 ^ (k + mCircuitK rest) * a := by
            rw [← Nat.mul_assoc ((M + 1) ^ rest.length * 3 ^ mCircuitK rest),
              mul_four_rearrange_p4, Nat.mul_comm (3 ^ mCircuitK rest) (3 ^ k),
              ← Nat.pow_succ, ← Nat.pow_add]
  simpa [List.length_cons, mCircuitS, mCircuitK_cons, syracuseIter_add] using hstrict

private theorem mCircuit_path_M_aux (cs : List (Nat × Nat)) (a M : Nat) (hMpos : 0 < M)
    (hpos : ∀ p ∈ cs, 1 ≤ p.1) (hvec : syracuseValVec (mCircuitK cs) a = mCircuitVec cs)
    (hM : ∀ i : Nat, i < mCircuitK cs → M ≤ syracuseIter i a) :
    M ^ cs.length * 2 ^ mCircuitS cs * syracuseIter (mCircuitK cs) a ≤
      (M + 1) ^ cs.length * 3 ^ mCircuitK cs * a ∧
    (cs ≠ [] →
      M ^ cs.length * 2 ^ mCircuitS cs * syracuseIter (mCircuitK cs) a <
        (M + 1) ^ cs.length * 3 ^ mCircuitK cs * a) := by
  induction cs generalizing a with
  | nil =>
    simp only [List.length_nil, Nat.pow_zero, Nat.one_mul, mCircuitS, mCircuitK_nil, syracuseIter]
    exact ⟨Nat.le_refl a, fun h => absurd rfl h⟩
  | cons p rest ih =>
    rcases p with ⟨k, e⟩
    have hk : 1 ≤ k := hpos (k, e) (by simp)
    have hrest : ∀ q ∈ rest, 1 ≤ q.1 := fun q hq => hpos q (by simp [hq])
    have happ : syracuseValVec k a ++ syracuseValVec (mCircuitK rest) (syracuseIter k a) =
        oneCircuitVec (k - 1) e ++ mCircuitVec rest := by
      simpa [mCircuitK_cons, mCircuitVec] using
        (syracuseValVec_add k (mCircuitK rest) a).symm.trans hvec
    have hlen : (syracuseValVec k a).length = (oneCircuitVec (k - 1) e).length := by
      rw [syracuseValVec_length, oneCircuitVec_length]; omega
    rcases List.append_inj happ hlen with ⟨hv1, hvrest⟩
    have hMrest : ∀ i, i < mCircuitK rest → M ≤ syracuseIter i (syracuseIter k a) := by
      intro i hi; rw [syracuseIter_add]; exact hM (k + i) (by simp only [mCircuitK_cons]; omega)
    have hstrict := mCircuit_path_M_step hk hMpos
      (hM 0 (by simp only [mCircuitK_cons]; omega)) hv1
      (ih (syracuseIter k a) hrest hvrest hMrest).1
    exact ⟨Nat.le_of_lt hstrict, fun _ => hstrict⟩

/-- **Generalized `M`-Valley `m`-Circuit Band Bound:**
whenever every iterate along an `m`-circuit cycle satisfies `M ≤ syracuseIter i n` (`0 < M`),
`M ^ cs.length * 2 ^ mCircuitS cs < (M + 1) ^ cs.length * 3 ^ mCircuitK cs`. -/
theorem mCircuit_archimedean_M_bound {cs : List (Nat × Nat)} {n M : Nat} (hMpos : 0 < M)
    (h : IsMCircuitCycle cs n) (hM : ∀ i : Nat, M ≤ syracuseIter i n) :
    M ^ cs.length * 2 ^ mCircuitS cs < (M + 1) ^ cs.length * 3 ^ mCircuitK cs := by
  have hpath := (mCircuit_path_M_aux cs n M hMpos (fun p hp => (h.canonical p hp).1)
    h.valVec_eq (fun i _ => hM i)).2 h.cs_nonempty
  rw [h.period_eq] at hpath
  exact Nat.lt_of_mul_lt_mul_right hpath

/-- **Unconditional `32768`-Valley `m`-Circuit Band Bound:**
`32768 ^ cs.length * 2 ^ mCircuitS cs < 32769 ^ cs.length * 3 ^ mCircuitK cs`. -/
theorem mCircuit_unconditional_32768_bound {cs : List (Nat × Nat)} {n : Nat}
    (h : IsMCircuitCycle cs n) :
    32768 ^ cs.length * 2 ^ mCircuitS cs < 32769 ^ cs.length * 3 ^ mCircuitK cs :=
  mCircuit_archimedean_M_bound (by decide) h (mCircuit_orbit_ge_32768 h)

/-- **Unconditional Sharp `S = minHalvings K` for `m ≤ 16384`:**
every non-trivial `m`-circuit cycle with `cs.length ≤ 16384` forces `mCircuitS cs` to equal the
unique minimal halving count `minHalvings (mCircuitK cs)`. -/
theorem mCircuit_totalVal_eq_minHalvings_unconditional {cs : List (Nat × Nat)} {n : Nat}
    (hm : cs.length ≤ 16384) (h : IsMCircuitCycle cs n) :
    mCircuitS cs = minHalvings (mCircuitK cs) := by
  have h32k := mCircuit_unconditional_32768_bound h
  have h2m : 32769 ^ cs.length ≤ 2 * 32768 ^ cs.length :=
    succ_pow_le_two_mul_pow (by decide : 0 < 32768) (by omega)
  have hpow2 : 2 ^ mCircuitS cs < 2 * 3 ^ mCircuitK cs := by
    have hmul : 32768 ^ cs.length * 2 ^ mCircuitS cs <
        32768 ^ cs.length * (2 * 3 ^ mCircuitK cs) := by
      calc 32768 ^ cs.length * 2 ^ mCircuitS cs
          < 32769 ^ cs.length * 3 ^ mCircuitK cs := h32k
        _ ≤ (2 * 32768 ^ cs.length) * 3 ^ mCircuitK cs := Nat.mul_le_mul_right _ h2m
        _ = 32768 ^ cs.length * (2 * 3 ^ mCircuitK cs) := by ac_rfl
    exact Nat.lt_of_mul_lt_mul_left hmul
  exact steiner_band_unique h.pow_lt hpow2 (lt_two_pow_minHalvings (mCircuitK cs))
    (two_pow_minHalvings_lt_two_mul h.mCircuitK_pos)

/-- **Unconditional Sharp `S = minHalvings K` for ALL 3-Circuits** (eliminating `minHalvings K + 1`
from `ThreeCircuit.lean`). -/
theorem threeCircuit_totalVal_eq_minHalvings {n k₁ e₁ k₂ e₂ k₃ e₃ : Nat}
    (h : IsThreeCircuitCycle n k₁ e₁ k₂ e₂ k₃ e₃) :
    k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3 = minHalvings (k₁ + k₂ + k₃) := by
  have heq := mCircuit_totalVal_eq_minHalvings_unconditional (by simp)
    (isThreeCircuitCycle_iff_isMCircuitCycle.mp h)
  have hk₁ := h.k₁_pos; have hk₂ := h.k₂_pos; have hk₃ := h.k₃_pos
  have hS : mCircuitS [(k₁, e₁), (k₂, e₂), (k₃, e₃)] =
      k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3 := by simp only [mCircuitS]; omega
  have hK : mCircuitK [(k₁, e₁), (k₂, e₂), (k₃, e₃)] = k₁ + k₂ + k₃ := by
    simp only [mCircuitK, List.map, List.sum_cons, List.sum_nil]; omega
  rwa [hS, hK] at heq

/-- **Unconditional Sharp `S = minHalvings K` for ALL 4-Circuits** (eliminating `minHalvings K + 1`
from `MCircuit.lean`). -/
theorem fourCircuit_totalVal_eq_minHalvings {cs : List (Nat × Nat)} {n : Nat}
    (hm : cs.length = 4) (h : IsMCircuitCycle cs n) :
    mCircuitS cs = minHalvings (mCircuitK cs) :=
  mCircuit_totalVal_eq_minHalvings_unconditional (by omega) h

/-! ### 3. Pure-`Nat` Two-Circuit Simons-Legendre Convergent Exclusion -/

private theorem pow_mul_le_of_base_le {A k₀ k : Nat} (hk : k₀ ≤ k) (hbase : A * 3 ^ k₀ ≤ 4 ^ k₀) :
    A * 3 ^ k ≤ 4 ^ k := by
  have hk_split : k = k₀ + (k - k₀) := (Nat.add_sub_of_le hk).symm
  rw [hk_split, Nat.pow_add, Nat.pow_add, ← Nat.mul_assoc]
  exact Nat.mul_le_mul hbase (Nat.pow_le_pow_left (by decide : 3 ≤ 4) (k - k₀))

private theorem twoCircuit_eq_case_helper {pU qU c k S d : Nat}
    (hU : 3 ^ qU < 2 ^ pU) (hself : 3 ^ qU ≤ 2 ^ c * (2 ^ pU - 3 ^ qU))
    (hd : 1 ≤ d) (hk_eq : k = d * qU) (hS_eq : S = d * pU) :
    (3 ^ qU) ^ 2 ≤ 4 ^ c * (2 ^ pU - 3 ^ qU) ^ 2 ∧
      (2 ^ pU - 3 ^ qU) ^ 2 * ((3 ^ qU) ^ (d - 1)) ^ 2 ≤ (2 ^ S - 3 ^ k) ^ 2 ∧
      (3 ^ qU) ^ (d - 1) ≤ (4 ^ qU) ^ (d - 1) := by
  have hdiff := pow_sub_pow_ge_mul_sub (Nat.le_of_lt hU) hd
  have hS_pow : (2 ^ pU) ^ d = 2 ^ S := by rw [← Nat.pow_mul, Nat.mul_comm pU d, ← hS_eq]
  have hk_pow : (3 ^ qU) ^ d = 3 ^ k := by rw [← Nat.pow_mul, Nat.mul_comm qU d, ← hk_eq]
  rw [hS_pow, hk_pow] at hdiff
  have hsq_self : (3 ^ qU) ^ 2 ≤ 4 ^ c * (2 ^ pU - 3 ^ qU) ^ 2 := by
    have h1 := Nat.mul_le_mul hself hself
    rwa [← Nat.pow_two, ← Nat.pow_two, Nat.mul_pow,
      show (2 ^ c) ^ 2 = 4 ^ c by rw [← Nat.pow_mul, Nat.mul_comm c 2, Nat.pow_mul]] at h1
  have hsq_diff : (2 ^ pU - 3 ^ qU) ^ 2 * ((3 ^ qU) ^ (d - 1)) ^ 2 ≤ (2 ^ S - 3 ^ k) ^ 2 := by
    have h1 := Nat.mul_le_mul hdiff hdiff
    rwa [← Nat.pow_two, ← Nat.pow_two, Nat.mul_pow] at h1
  exact ⟨hsq_self, hsq_diff, Nat.pow_le_pow_left (Nat.pow_le_pow_left (by decide) qU) (d - 1)⟩

private theorem twoCircuit_convergent_eq_case {pU qU c k S d : Nat}
    (hU : 3 ^ qU < 2 ^ pU) (hself : 3 ^ qU ≤ 2 ^ c * (2 ^ pU - 3 ^ qU))
    (h4q : 16 * 4 ^ c * 3 ^ qU ≤ 4 ^ qU) (hd : 1 ≤ d) (hk_eq : k = d * qU) (hS_eq : S = d * pU) :
    16 * 3 ^ (3 * k) ≤ 4 ^ k * (2 ^ S - 3 ^ k) ^ 2 := by
  rcases twoCircuit_eq_case_helper hU hself hd hk_eq hS_eq with ⟨hsq_self, hsq_diff, h34⟩
  have h3k_split : 3 ^ (3 * k) = 3 ^ qU * (3 ^ qU) ^ 2 *
      (3 ^ qU) ^ (d - 1) * ((3 ^ qU) ^ (d - 1)) ^ 2 := by
    have hd3 : 3 * d = 1 + 2 + (d - 1) + 2 * (d - 1) := by omega
    have hbase : 3 ^ (3 * k) = (3 ^ qU) ^ (3 * d) := by
      rw [hk_eq, show 3 * (d * qU) = qU * (3 * d) by ac_rfl, Nat.pow_mul]
    rw [hbase, hd3, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_one,
      show (3 ^ qU) ^ (2 * (d - 1)) = ((3 ^ qU) ^ (d - 1)) ^ 2 by
        rw [Nat.mul_comm 2 (d - 1), Nat.pow_mul]]
  have h4k_split : 4 ^ k = 4 ^ qU * (4 ^ qU) ^ (d - 1) := by
    have hd1 : d = 1 + (d - 1) := by omega
    conv => lhs; rw [hk_eq, hd1, Nat.add_mul, Nat.one_mul, Nat.pow_add,
      Nat.mul_comm (d - 1) qU, Nat.pow_mul]
  calc 16 * 3 ^ (3 * k)
      = 16 * 3 ^ qU * (3 ^ qU) ^ 2 * (3 ^ qU) ^ (d - 1) * ((3 ^ qU) ^ (d - 1)) ^ 2 := by
          rw [h3k_split]; ac_rfl
    _ ≤ 16 * 3 ^ qU * (4 ^ c * (2 ^ pU - 3 ^ qU) ^ 2) * (3 ^ qU) ^ (d - 1) *
          ((3 ^ qU) ^ (d - 1)) ^ 2 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hsq_self))
    _ = (16 * 4 ^ c * 3 ^ qU) * (3 ^ qU) ^ (d - 1) *
          ((2 ^ pU - 3 ^ qU) ^ 2 * ((3 ^ qU) ^ (d - 1)) ^ 2) := by ac_rfl
    _ ≤ 4 ^ qU * (4 ^ qU) ^ (d - 1) * (2 ^ S - 3 ^ k) ^ 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul h4q h34) hsq_diff
    _ = 4 ^ k * (2 ^ S - 3 ^ k) ^ 2 := by rw [h4k_split]

private theorem twoCircuit_lt_linear_step {qU k S : Nat}
    (hgap4 : 64 * qU ^ 2 * 3 ^ k ≤ 4 ^ k) (hpow : 3 ^ k < 2 ^ S)
    (hbound : 4 ^ k * (2 ^ S - 3 ^ k) ^ 2 < 16 * 3 ^ (3 * k)) (hqU : 0 < qU) :
    (2 * qU) * 2 ^ S < (2 * qU + 1) * 3 ^ k := by
  have hN_pos : 0 < 2 * qU := by omega
  have hN2 : (2 * qU) ^ 2 * 16 = 64 * qU ^ 2 := by
    rw [Nat.mul_pow, show 2 ^ 2 = 4 by decide]; omega
  have h3pow : 3 ^ (3 * k) = 3 ^ k * (3 ^ k) ^ 2 := by
    rw [show 3 * k = k + 2 * k by omega, Nat.pow_add, Nat.mul_comm 2 k, Nat.pow_mul]
  have hsq_lt : 4 ^ k * ((2 * qU) * (2 ^ S - 3 ^ k)) ^ 2 < 4 ^ k * (3 ^ k) ^ 2 := by
    calc 4 ^ k * ((2 * qU) * (2 ^ S - 3 ^ k)) ^ 2
        = (2 * qU) ^ 2 * (4 ^ k * (2 ^ S - 3 ^ k) ^ 2) := by rw [Nat.mul_pow]; ac_rfl
      _ < (2 * qU) ^ 2 * (16 * 3 ^ (3 * k)) :=
          Nat.mul_lt_mul_of_pos_left hbound (Nat.pow_pos hN_pos)
      _ = (64 * qU ^ 2 * 3 ^ k) * (3 ^ k) ^ 2 := by rw [h3pow, ← hN2]; ac_rfl
      _ ≤ 4 ^ k * (3 ^ k) ^ 2 := Nat.mul_le_mul_right _ hgap4
  have hlin_sq : ((2 * qU) * (2 ^ S - 3 ^ k)) ^ 2 < (3 ^ k) ^ 2 := Nat.lt_of_mul_lt_mul_left hsq_lt
  have hlin : (2 * qU) * (2 ^ S - 3 ^ k) < 3 ^ k := by
    by_cases hlt : (2 * qU) * (2 ^ S - 3 ^ k) < 3 ^ k
    · exact hlt
    · have hle := Nat.le_of_not_lt hlt
      have := Nat.mul_le_mul hle hle; rw [← Nat.pow_two, ← Nat.pow_two] at this; omega
  rw [Nat.mul_sub] at hlin
  have h3le : (2 * qU) * 3 ^ k ≤ (2 * qU) * 2 ^ S := Nat.mul_le_mul_left _ (Nat.le_of_lt hpow)
  rw [Nat.add_mul, Nat.one_mul]; omega

private theorem twoCircuit_convergent_lt_case {pU qU k S : Nat}
    (hqU : 0 < qU) (hkpos : 1 ≤ k) (hU : 3 ^ qU < 2 ^ pU) (hlt : pU * k < qU * S)
    (hgap4 : 64 * qU ^ 2 * 3 ^ k ≤ 4 ^ k) (hpow : 3 ^ k < 2 ^ S)
    (hbound : 4 ^ k * (2 ^ S - 3 ^ k) ^ 2 < 16 * 3 ^ (3 * k)) : False := by
  have h2low : 2 * (3 ^ qU) ^ k < (2 ^ S) ^ qU := by
    have h32 : (3 ^ qU) ^ k < (2 ^ pU) ^ k := Nat.pow_lt_pow_left hU (by omega)
    calc 2 * (3 ^ qU) ^ k < 2 * (2 ^ pU) ^ k := Nat.mul_lt_mul_of_pos_left h32 (by decide)
      _ = 2 ^ (pU * k + 1) := by rw [← Nat.pow_mul, Nat.pow_succ, Nat.mul_comm]
      _ ≤ 2 ^ (qU * S) := Nat.pow_le_pow_right (by decide) hlt
      _ = (2 ^ S) ^ qU := by rw [Nat.mul_comm qU S, Nat.pow_mul]
  have hstep := twoCircuit_lt_linear_step hgap4 hpow hbound hqU
  have hq_lt : (2 * qU) ^ qU * (2 ^ S) ^ qU < (2 * qU + 1) ^ qU * (3 ^ qU) ^ k := by
    have hp := Nat.pow_lt_pow_left hstep (Nat.pos_iff_ne_zero.mp hqU)
    have h3eq : (3 ^ k) ^ qU = (3 ^ qU) ^ k := by
      rw [← Nat.pow_mul, Nat.mul_comm k qU, Nat.pow_mul]
    rw [Nat.mul_pow (2 * qU) (2 ^ S) qU, Nat.mul_pow (2 * qU + 1) (3 ^ k) qU, h3eq] at hp
    exact hp
  have hcomb : 2 * (2 * qU) ^ qU * (3 ^ qU) ^ k < (2 * qU + 1) ^ qU * (3 ^ qU) ^ k := by
    have hmul := Nat.mul_lt_mul_of_pos_left h2low (Nat.pow_pos (by omega : 0 < 2 * qU) (n := qU))
    rw [← Nat.mul_assoc, Nat.mul_comm ((2 * qU) ^ qU) 2] at hmul; exact Nat.lt_trans hmul hq_lt
  have hcancel : 2 * (2 * qU) ^ qU < (2 * qU + 1) ^ qU := Nat.lt_of_mul_lt_mul_right hcomb
  have hbern := succ_pow_le_two_mul_pow (by omega : 0 < 2 * qU) (Nat.le_refl (2 * qU))
  omega

/-- **Pure-`Nat` Two-Circuit Simons-Legendre Convergent Exclusion Lemma:**
given Farey neighbors `pL/qL < log₂(3) < pU/qU` (`2^pL < 3^qL`, `3^qU < 2^pU`,
`pU * qL = pL * qU + 1`) with `3^qU ≤ 2^c * (2^pU - 3^qU)`, `16 * 4^c * 3^qU ≤ 4^qU`, and
`64 * qU^2 * 3^k ≤ 4^k`, no pair `(k, S)` with `1 ≤ k < qU + qL` satisfies both `3^k < 2^S` and
`4^k * (2^S - 3^k)^2 < 16 * 3^(3*k)`. -/
theorem twoCircuit_simons_convergent_exclusion
    {pL qL pU qU c k S : Nat} (hqU : 0 < qU) (hkpos : 1 ≤ k)
    (hL : 2 ^ pL < 3 ^ qL) (hU : 3 ^ qU < 2 ^ pU) (hdet : pU * qL = pL * qU + 1)
    (hself : 3 ^ qU ≤ 2 ^ c * (2 ^ pU - 3 ^ qU)) (h4q : 16 * 4 ^ c * 3 ^ qU ≤ 4 ^ qU)
    (hgap4 : 64 * qU ^ 2 * 3 ^ k ≤ 4 ^ k) (hk_hi : k < qU + qL)
    (hpow : 3 ^ k < 2 ^ S) (hbound : 4 ^ k * (2 ^ S - 3 ^ k) ^ 2 < 16 * 3 ^ (3 * k)) : False := by
  have hle : pU * k ≤ qU * S := farey_upper_semiconvergent_bound hL hdet hk_hi hpow
  by_cases heq : pU * k = qU * S
  · rcases farey_eq_mul_imp_dvd hqU hkpos hdet heq with ⟨d, hd, hk_eq, hS_eq⟩
    have hcontra := twoCircuit_convergent_eq_case hU hself h4q hd hk_eq hS_eq
    omega
  · exact twoCircuit_convergent_lt_case hqU hkpos hU (by omega) hgap4 hpow hbound

/-- Parametric 2-circuit elimination over `[k₀, qU + qL)` driven by Farey neighbors
`(pL, qL)` and `(pU, qU)`. -/
theorem no_nontrivial_twoCircuit_of_farey_window
    {pL qL pU qU c k₀ : Nat} (hqU : 0 < qU) (hk₀ : 1 ≤ k₀)
    (hL : 2 ^ pL < 3 ^ qL) (hU : 3 ^ qU < 2 ^ pU) (hdet : pU * qL = pL * qU + 1)
    (hself : 3 ^ qU ≤ 2 ^ c * (2 ^ pU - 3 ^ qU)) (h4q : 16 * 4 ^ c * 3 ^ qU ≤ 4 ^ qU)
    (hgap4_0 : 64 * qU ^ 2 * 3 ^ k₀ ≤ 4 ^ k₀)
    {n k₁ e₁ k₂ e₂ : Nat} (hlo : k₀ ≤ k₁ + k₂) (hhi : k₁ + k₂ < qU + qL) :
    ¬ IsTwoCircuitCycle n k₁ e₁ k₂ e₂ := by
  intro hcyc
  have hkpos : 1 ≤ k₁ + k₂ := by have := hcyc.k₁_pos; omega
  exact twoCircuit_simons_convergent_exclusion hqU hkpos hL hU hdet hself h4q
    (pow_mul_le_of_base_le hlo hgap4_0) hhi hcyc.pow_lt (twoCircuit_exp_gap_bound hcyc)

/-! ### 4. Extended `log₂(3)` CF & Unconditional 2-Circuit Elimination (`K ≤ 64497106`) -/

/-- Extended partial quotients of `log₂(3)` up to index `16`
(`[1, 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, 1, 55, 1, 4]`). -/
def log2ThreeCFExt2 : List Nat := log2ThreeCFExt ++ [1, 4]

/-- Exact convergent pairs for `log2ThreeCFExt2` at indices `15` and `16`. -/
theorem log2ThreeCFExt2_convergents :
    cfConvergentPair (log2ThreeCFExt2.take 16) = ((16785921, 10590737), (17087915, 10781274)) ∧
    cfConvergentPair (log2ThreeCFExt2.take 17) = ((17087915, 10781274), (85137581, 53715833)) := by
  decide

/-- Farey determinant `17087915 * 53715833 = 85137581 * 10781274 + 1` via `cfConvergentPair_det`. -/
theorem log2ThreeCFExt2_det_16_17 : 17087915 * 53715833 = 85137581 * 10781274 + 1 := by
  have hdet := cfConvergentPair_det (log2ThreeCFExt2.take 17)
  have hlen : (log2ThreeCFExt2.take 17).length % 2 = 1 := by decide
  rw [log2ThreeCFExt2_convergents.2, hlen] at hdet

private theorem cf_witness_twoCircuit_64m :
    2 ^ 85137581 < 3 ^ 53715833 ∧ 3 ^ 10781274 < 2 ^ 17087915 ∧
    (82000000 + 1) * 3 ^ 10781274 ≤ 82000000 * 2 ^ 17087915 ∧
    3 ^ 10781274 ≤ 2 ^ 27 * (2 ^ 17087915 - 3 ^ 10781274) ∧
    2 ^ 17087914 < 3 ^ 10781274 ∧ 64 * 10781274 ^ 2 * 3 ^ 306 ≤ 4 ^ 306 := by
  have h :
      fastPow 2 85137581 < fastPow 3 53715833 ∧ fastPow 3 10781274 < fastPow 2 17087915 ∧
      (82000000 + 1) * fastPow 3 10781274 ≤ 82000000 * fastPow 2 17087915 ∧
      fastPow 3 10781274 ≤ 2 ^ 27 * (fastPow 2 17087915 - fastPow 3 10781274) ∧
      fastPow 2 17087914 < fastPow 3 10781274 ∧
      64 * 10781274 ^ 2 * fastPow 3 306 ≤ fastPow 4 306 := by decide
  rwa [fastPow_eq 2 85137581 (by decide), fastPow_eq 3 53715833 (by decide),
    fastPow_eq 3 10781274 (by decide), fastPow_eq 2 17087915 (by decide),
    fastPow_eq 2 17087914 (by decide), fastPow_eq 3 306 (by decide),
    fastPow_eq 4 306 (by decide)] at h

private theorem four_pow_c_mul_three_pow_le {c q : Nat} (hq : 200 ≤ q)
    (hbase : 16 * 4 ^ c * 3 ^ 200 ≤ 4 ^ 200) : 16 * 4 ^ c * 3 ^ q ≤ 4 ^ q := by
  have hsplit : q = 200 + (q - 200) := (Nat.add_sub_of_le hq).symm
  rw [hsplit, Nat.pow_add, Nat.pow_add, ← Nat.mul_assoc]
  exact Nat.mul_le_mul hbase (Nat.pow_le_pow_left (by decide) (q - 200))

private theorem pow_add_lt_pow_add (a b e₁ e₂ e₁' e₂' s s' : Nat)
    (hs : e₁ + e₂ = s) (hs' : e₁' + e₂' = s') (hb : 0 < a ^ e₂)
    (h₁ : a ^ e₁ < b ^ e₁') (h₂ : a ^ e₂ < b ^ e₂') : a ^ s < b ^ s' := by
  rw [← hs, ← hs', Nat.pow_add, Nat.pow_add]
  exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right h₁ hb)
    (Nat.mul_le_mul_left (b ^ e₁') (Nat.le_of_lt h₂))

private theorem cf_witness_twoCircuit_extra :
    3 ^ 10781274 ≤ 2 ^ 27 * (2 ^ 17087915 - 3 ^ 10781274) ∧
    16 * 4 ^ 27 * 3 ^ 10781274 ≤ 4 ^ 10781274 ∧ 2 ^ 102225495 < 3 ^ 64497107 := by
  have hpow_self := cf_witness_twoCircuit_64m.2.2.2.1
  have h4q : 16 * 4 ^ 27 * 3 ^ 10781274 ≤ 4 ^ 10781274 :=
    four_pow_c_mul_three_pow_le (c := 27) (q := 10781274)
      (by decide : 200 ≤ 10781274) (by decide : 16 * 4 ^ 27 * 3 ^ 200 ≤ 4 ^ 200)
  have hhalv : 2 ^ 102225495 < 3 ^ 64497107 :=
    pow_add_lt_pow_add 2 3 17087914 85137581 10781274 53715833 102225495 64497107
      (by decide) (by decide) (Nat.two_pow_pos 85137581)
      cf_witness_twoCircuit_64m.2.2.2.2.1 cf_witness_twoCircuit_64m.1
  exact ⟨hpow_self, h4q, hhalv⟩

private theorem halving_ge_of_k_ge {K S k₀ s₀ : Nat}
    (hpow : 3 ^ K < 2 ^ S) (hk : k₀ ≤ K) (hw : 2 ^ s₀ < 3 ^ k₀) : s₀ + 1 ≤ S := by
  have h3le : 3 ^ k₀ ≤ 3 ^ K := Nat.pow_le_pow_right (by decide) hk
  have h2lt : 2 ^ s₀ < 2 ^ S := Nat.lt_trans (Nat.lt_of_lt_of_le hw h3le) hpow
  by_cases hs : s₀ + 1 ≤ S
  · exact hs
  · exact absurd h2lt (Nat.not_lt_of_ge (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))

/-- **Flagship Unconditional 2-Circuit Elimination (`K ≤ 64497106`, zero `native_decide`):**
there is no non-trivial positive 2-circuit Collatz cycle with `k₁ + k₂ ≤ 64497106`
(a `2,224,038x` leap over `no_nontrivial_twoCircuit_le_29`). -/
theorem no_nontrivial_twoCircuit_le_64497106 :
    ∀ n k₁ e₁ k₂ e₂ : Nat, k₁ + k₂ ≤ 64497106 → ¬ IsTwoCircuitCycle n k₁ e₁ k₂ e₂ := by
  intro n k₁ e₁ k₂ e₂ hle hcyc
  have hk306 : 306 ≤ k₁ + k₂ := (twoCircuit_unconditional_eliahou_bounds hcyc).2.2.1
  exact no_nontrivial_twoCircuit_of_farey_window (pL := 85137581) (qL := 53715833)
    (pU := 17087915) (qU := 10781274) (c := 27) (k₀ := 306) (by decide) (by decide)
    cf_witness_twoCircuit_64m.1 cf_witness_twoCircuit_64m.2.1 log2ThreeCFExt2_det_16_17
    cf_witness_twoCircuit_extra.1 cf_witness_twoCircuit_extra.2.1
    cf_witness_twoCircuit_64m.2.2.2.2.2 hk306 (by omega) hcyc

/-- **Unconditional 2-Circuit Odd-Length Lower Bound (`64497107 ≤ K`).** -/
theorem twoCircuit_k_ge_64497107 {n k₁ e₁ k₂ e₂ : Nat}
    (h : IsTwoCircuitCycle n k₁ e₁ k₂ e₂) : 64497107 ≤ k₁ + k₂ :=
  if hk : 64497107 ≤ k₁ + k₂ then hk
  else absurd h (no_nontrivial_twoCircuit_le_64497106 n k₁ e₁ k₂ e₂ (Nat.le_of_not_lt hk))

/-- **Unconditional 2-Circuit Halving Lower Bound (`102225496 ≤ S`).** -/
theorem twoCircuit_halvings_ge_102225496 {n k₁ e₁ k₂ e₂ : Nat}
    (h : IsTwoCircuitCycle n k₁ e₁ k₂ e₂) : 102225496 ≤ k₁ + k₂ + e₁ + e₂ - 2 :=
  halving_ge_of_k_ge h.pow_lt (twoCircuit_k_ge_64497107 h) cf_witness_twoCircuit_extra.2.2

/-- **Unconditional 2-Circuit Total Collatz-Length Lower Bound (`166722603 ≤ K + S`).** -/
theorem twoCircuit_collatzLen_ge_166722603 {n k₁ e₁ k₂ e₂ : Nat}
    (h : IsTwoCircuitCycle n k₁ e₁ k₂ e₂) :
    166722603 ≤ (k₁ + k₂) + (k₁ + k₂ + e₁ + e₂ - 2) :=
  Nat.le_trans (by decide : 166722603 ≤ 64497107 + 102225496)
    (Nat.add_le_add (twoCircuit_k_ge_64497107 h) (twoCircuit_halvings_ge_102225496 h))

/-- **Bridge to Frozen `Challenge.lean` for 2-Circuits.** -/
theorem twoCircuit_challenge_bounds {n k₁ e₁ k₂ e₂ : Nat}
    (h : IsTwoCircuitCycle n k₁ e₁ k₂ e₂) :
    let K := k₁ + k₂; let S := k₁ + k₂ + e₁ + e₂ - 2
    HasNontrivialCycle ∧ collatzIter (K + S) n = n ∧
    (∀ j : Nat, j < K + S → collatzIter j n ≠ 1) ∧
    32768 ≤ n ∧ 64497107 ≤ K ∧ 102225496 ≤ S ∧ 166722603 ≤ K + S := by
  intro K S
  have hodd := h.odd; have htot := h.totalVal_eq
  have hne_syr : ∀ i : Nat, i < K → syracuseIter i n ≠ 1 := fun i _ h1 => by
    have hKpos : 0 < K := by have := h.k₁_pos; omega
    have h3 := (syracuseIter_three_le_of_cycle hKpos h.one_lt_n h.period_eq i).2; omega
  have hcol : collatzIter (K + S) n = n := by
    dsimp only [K, S]; rw [Nat.add_comm, ← htot, collatzIter_eq_syracuseIter _ hodd, h.period_eq]
  have havoid : ∀ j : Nat, j < K + S → collatzIter j n ≠ 1 := fun j hj => by
    dsimp only [K, S] at hj; rw [Nat.add_comm, ← htot] at hj
    exact collatzIter_ne_one_of_syracuseIter _ hodd hne_syr j hj
  exact ⟨h.hasNontrivialCycle, hcol, havoid, (twoCircuit_unconditional_eliahou_bounds h).1,
    twoCircuit_k_ge_64497107 h, twoCircuit_halvings_ge_102225496 h,
    twoCircuit_collatzLen_ge_166722603 h⟩

/-- **Sharpened Conditional Simons-Baker Reduction above `K = 64497106`.** -/
theorem no_nontrivial_twoCircuit_of_diophantine_bound_gt_64497106
    (hBaker : ∀ k S : Nat, 64497106 < k → 3 ^ k < 2 ^ S →
      16 * 3 ^ (3 * k) ≤ 4 ^ k * (2 ^ S - 3 ^ k) ^ 2) :
    ∀ n k₁ e₁ k₂ e₂ : Nat, ¬ IsTwoCircuitCycle n k₁ e₁ k₂ e₂ :=
  no_nontrivial_twoCircuit_of_diophantine_bound 64497106 hBaker
    no_nontrivial_twoCircuit_le_64497106

/-! ### 5. `O(1)` `m`-Circuit CF Elimination & Unconditional 3/4/5-Circuit Bounds -/

private theorem mCircuit_cf_ratio_chain {M m a b d pU qU K : Nat}
    (hd : 0 < d) (hgap : (d + 1) * 3 ^ qU ≤ d * 2 ^ pU)
    (hMstep : (M + 1) ^ (m * a) * d ^ b ≤ M ^ (m * a) * (d + 1) ^ b) :
    ((M + 1) ^ (m * a)) ^ K * ((3 ^ qU) ^ b) ^ K ≤
      (M ^ (m * a)) ^ K * ((2 ^ pU) ^ b) ^ K := by
  have hd_pos : 0 < d ^ b * (d + 1) ^ b :=
    Nat.mul_pos (Nat.pow_pos hd) (Nat.pow_pos (by omega))
  have hgap_b : (d + 1) ^ b * (3 ^ qU) ^ b ≤ d ^ b * (2 ^ pU) ^ b := by
    rw [← Nat.mul_pow, ← Nat.mul_pow]; exact Nat.pow_le_pow_left hgap b
  have hcomb : (M + 1) ^ (m * a) * (3 ^ qU) ^ b * (d ^ b * (d + 1) ^ b) ≤
      M ^ (m * a) * (2 ^ pU) ^ b * (d ^ b * (d + 1) ^ b) := by
    calc (M + 1) ^ (m * a) * (3 ^ qU) ^ b * (d ^ b * (d + 1) ^ b)
        = ((M + 1) ^ (m * a) * d ^ b) * ((d + 1) ^ b * (3 ^ qU) ^ b) := by ac_rfl
      _ ≤ (M ^ (m * a) * (d + 1) ^ b) * (d ^ b * (2 ^ pU) ^ b) := Nat.mul_le_mul hMstep hgap_b
      _ = M ^ (m * a) * (2 ^ pU) ^ b * (d ^ b * (d + 1) ^ b) := by ac_rfl
  have hK := Nat.pow_le_pow_left (Nat.le_of_mul_le_mul_right hcomb hd_pos) K
  rwa [Nat.mul_pow, Nat.mul_pow] at hK

private theorem mCircuit_cf_monotone_shift (M : Nat) {e₁ e₂ : Nat} (hle : e₁ ≤ e₂) :
    M ^ e₂ * (M + 1) ^ e₁ ≤ M ^ e₁ * (M + 1) ^ e₂ := by
  have he : e₂ = e₁ + (e₂ - e₁) := (Nat.add_sub_of_le hle).symm
  conv => lhs; rw [he, Nat.pow_add]
  conv => rhs; rw [he, Nat.pow_add]
  have hpow : M ^ (e₂ - e₁) ≤ (M + 1) ^ (e₂ - e₁) := Nat.pow_le_pow_left (by omega) _
  calc M ^ e₁ * M ^ (e₂ - e₁) * (M + 1) ^ e₁
      = M ^ e₁ * (M + 1) ^ e₁ * M ^ (e₂ - e₁) := by ac_rfl
    _ ≤ M ^ e₁ * (M + 1) ^ e₁ * (M + 1) ^ (e₂ - e₁) := Nat.mul_le_mul_left _ hpow
    _ = M ^ e₁ * ((M + 1) ^ e₁ * (M + 1) ^ (e₂ - e₁)) := by rw [Nat.mul_assoc]

private theorem mCircuit_cf_pow_lift {M m pL qL pU qU K S b : Nat}
    (hqU : 0 < qU) (hb : 0 < b) (hL : 2 ^ pL < 3 ^ qL) (hdet : pU * qL = pL * qU + 1)
    (hpow : 3 ^ K < 2 ^ S) (hk_lt : K < qU + qL)
    (hband : M ^ m * 2 ^ S < (M + 1) ^ m * 3 ^ K) :
    M ^ (m * (b * qU)) * ((2 ^ pU) ^ b) ^ K <
      (M + 1) ^ (m * (b * qU)) * ((3 ^ qU) ^ b) ^ K := by
  have hmul : pU * K ≤ qU * S := farey_upper_semiconvergent_bound hL hdet hk_lt hpow
  have hp := Nat.pow_lt_pow_left hband (Nat.pos_iff_ne_zero.mp hqU)
  rw [Nat.mul_pow (M ^ m) (2 ^ S) qU, Nat.mul_pow ((M + 1) ^ m) (3 ^ K) qU,
    ← Nat.pow_mul M m qU, ← Nat.pow_mul 2 S qU, ← Nat.pow_mul (M + 1) m qU,
    ← Nat.pow_mul 3 K qU, Nat.mul_comm S qU, Nat.mul_comm K qU] at hp
  have h2le : (2 ^ pU) ^ K ≤ 2 ^ (qU * S) := by
    rw [← Nat.pow_mul]; exact Nat.pow_le_pow_right (by decide) hmul
  have hq_lt := Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ h2le) hp
  have hqb := Nat.pow_lt_pow_left hq_lt (Nat.pos_iff_ne_zero.mp hb)
  have h3eq : ((3 ^ K) ^ qU) ^ b = ((3 ^ qU) ^ b) ^ K := by
    rw [← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul]; ac_rfl
  rw [Nat.mul_pow (M ^ (m * qU)) ((2 ^ pU) ^ K) b,
    Nat.mul_pow ((M + 1) ^ (m * qU)) (3 ^ (qU * K)) b,
    ← Nat.pow_mul M (m * qU) b, ← Nat.pow_mul (M + 1) (m * qU) b,
    Nat.mul_assoc m qU b, Nat.mul_comm qU b,
    ← Nat.pow_mul (2 ^ pU) K b, Nat.mul_comm K b, Nat.pow_mul (2 ^ pU) b K,
    Nat.mul_comm qU K, Nat.pow_mul 3 K qU, h3eq] at hqb
  exact hqb

/-- **General `O(1)` Parametric `m`-Circuit Continued-Fraction Elimination.** -/
theorem mCircuit_cf_elimination_step {M m pL qL pU qU K₀ a b d : Nat}
    (hMpos : 0 < M) (hqU : 0 < qU) (hb : 0 < b) (hd : 0 < d)
    (hL : 2 ^ pL < 3 ^ qL) (hdet : pU * qL = pL * qU + 1)
    (hrel : b * qU ≤ a * K₀) (hgap : (d + 1) * 3 ^ qU ≤ d * 2 ^ pU)
    (hMstep : (M + 1) ^ (m * a) * d ^ b ≤ M ^ (m * a) * (d + 1) ^ b)
    {cs : List (Nat × Nat)} {n : Nat}
    (hm : cs.length = m) (hcyc : IsMCircuitCycle cs n)
    (hM : ∀ i : Nat, M ≤ syracuseIter i n) (hK₀ : K₀ ≤ mCircuitK cs) :
    qU + qL ≤ mCircuitK cs := by
  by_cases hge : qU + qL ≤ mCircuitK cs
  · exact hge
  · exfalso
    let K := mCircuitK cs
    have hband := mCircuit_archimedean_M_bound hMpos hcyc hM
    rw [hm] at hband
    have hqb := mCircuit_cf_pow_lift hqU hb hL hdet hcyc.pow_lt (Nat.lt_of_not_ge hge) hband
    have hchain := mCircuit_cf_ratio_chain hd hgap hMstep (K := K)
    have hshift := mCircuit_cf_monotone_shift M
      (Nat.mul_le_mul_left m (Nat.le_trans hrel (Nat.mul_le_mul_left a hK₀)))
    have hpos_fac : 0 < ((M + 1) ^ (m * a)) ^ K * (M ^ (m * a)) ^ K :=
      Nat.mul_pos (Nat.pow_pos (Nat.pow_pos (by omega))) (Nat.pow_pos (Nat.pow_pos hMpos))
    have hLHS_eq : ((M + 1) ^ (m * a)) ^ K = (M + 1) ^ (m * (a * K)) := by
      rw [← Nat.pow_mul, Nat.mul_assoc]
    have hRHS_eq : (M ^ (m * a)) ^ K = M ^ (m * (a * K)) := by
      rw [← Nat.pow_mul, Nat.mul_assoc]
    have hfinal : M ^ (m * (b * qU)) * ((M + 1) ^ (m * a)) ^ K * (M ^ (m * a)) ^ K *
          ((2 ^ pU) ^ b) ^ K <
        M ^ (m * (b * qU)) * ((M + 1) ^ (m * a)) ^ K * (M ^ (m * a)) ^ K *
          ((2 ^ pU) ^ b) ^ K := by
      calc M ^ (m * (b * qU)) * ((M + 1) ^ (m * a)) ^ K * (M ^ (m * a)) ^ K *
            ((2 ^ pU) ^ b) ^ K
          = (M ^ (m * (b * qU)) * ((2 ^ pU) ^ b) ^ K) *
              (((M + 1) ^ (m * a)) ^ K * (M ^ (m * a)) ^ K) := by ac_rfl
        _ < ((M + 1) ^ (m * (b * qU)) * ((3 ^ qU) ^ b) ^ K) *
              (((M + 1) ^ (m * a)) ^ K * (M ^ (m * a)) ^ K) :=
            Nat.mul_lt_mul_of_pos_right hqb hpos_fac
        _ = (M ^ (m * (a * K)) * (M + 1) ^ (m * (b * qU))) *
              (((M + 1) ^ (m * a)) ^ K * ((3 ^ qU) ^ b) ^ K) := by rw [hRHS_eq]; ac_rfl
        _ ≤ (M ^ (m * (b * qU)) * (M + 1) ^ (m * (a * K))) *
              ((M ^ (m * a)) ^ K * ((2 ^ pU) ^ b) ^ K) := Nat.mul_le_mul hshift hchain
        _ = M ^ (m * (b * qU)) * ((M + 1) ^ (m * a)) ^ K * (M ^ (m * a)) ^ K *
              ((2 ^ pU) ^ b) ^ K := by rw [hLHS_eq]; ac_rfl
    exact Nat.lt_irrefl _ hfinal

/-- Bernoulli linear-threshold helper for large `M` (`(d + 1) * Q ≤ M` implies
`(M + 1) ^ Q * d ^ 1 ≤ M ^ Q * (d + 1) ^ 1` without computing `M ^ Q`). -/
theorem mCircuit_bernoulli_step (M Q d : Nat) (hM : 0 < M) (hQM : (d + 1) * Q ≤ M) :
    (M + 1) ^ Q * d ^ 1 ≤ M ^ Q * (d + 1) ^ 1 := by
  have hQle : Q ≤ M := Nat.le_trans (by simpa using Nat.mul_le_mul_right Q (Nat.succ_pos d)) hQM
  have hbern := succ_pow_mul_sub_le M Q hQle
  have hlin : M * d ≤ (d + 1) * (M - Q) := by
    rw [Nat.mul_sub, Nat.add_mul, Nat.one_mul]
    have hdm : d * Q ≤ d * M := Nat.mul_le_mul_left d hQle
    rw [Nat.mul_comm M d]; omega
  have hmul : ((M + 1) ^ Q * d) * M ≤ (M ^ Q * (d + 1)) * M := by
    calc ((M + 1) ^ Q * d) * M = (M + 1) ^ Q * (M * d) := by ac_rfl
      _ ≤ (M + 1) ^ Q * ((d + 1) * (M - Q)) := Nat.mul_le_mul_left _ hlin
      _ = ((M + 1) ^ Q * (M - Q)) * (d + 1) := by ac_rfl
      _ ≤ M ^ (Q + 1) * (d + 1) := Nat.mul_le_mul_right (d + 1) hbern
      _ = (M ^ Q * (d + 1)) * M := by rw [Nat.pow_succ]; ac_rfl
  simpa only [Nat.pow_one] using Nat.le_of_mul_le_mul_right hmul hM

private theorem cf_semi_det_665 (c : Nat) :
    (c * 1054 + 485) * 665 = 1054 * (c * 665 + 306) + 1 :=
  cf_semiconvergent_det (prev := (485, 306)) (cur := (1054, 665)) c (by decide)

private theorem mCircuit_32k_witness_A :
    ((1070 + 1) * 3 ^ 1636 ≤ 1070 * 2 ^ 2593 ∧
      (32768 + 1) ^ (4 * 6) * 1070 ^ 1 ≤ 32768 ^ (4 * 6) * (1070 + 1) ^ 1 ∧
      (32768 + 1) ^ (5 * 6) * 1070 ^ 1 ≤ 32768 ^ (5 * 6) * (1070 + 1) ^ 1) ∧
    ((1122 + 1) * 3 ^ 2301 ≤ 1122 * 2 ^ 3647 ∧
      (32768 + 1) ^ (3 * 8) * 1122 ^ 1 ≤ 32768 ^ (3 * 8) * (1122 + 1) ^ 1) ∧
    ((1845 + 1) * 3 ^ 7621 ≤ 1845 * 2 ^ 12079 ∧
      (32768 + 1) ^ (5 * 7) * 1845 ^ 2 ≤ 32768 ^ (5 * 7) * (1845 + 1) ^ 2) ∧
    ((2006 + 1) * 3 ^ 8286 ≤ 2006 * 2 ^ 13133 ∧
      (32768 + 1) ^ (4 * 4) * 2006 ^ 1 ≤ 32768 ^ (4 * 4) * (2006 + 1) ^ 1) := by
  have h :
      ((1070 + 1) * fastPow 3 1636 ≤ 1070 * fastPow 2 2593 ∧
        (32768 + 1) ^ (4 * 6) * 1070 ^ 1 ≤ 32768 ^ (4 * 6) * (1070 + 1) ^ 1 ∧
        (32768 + 1) ^ (5 * 6) * 1070 ^ 1 ≤ 32768 ^ (5 * 6) * (1070 + 1) ^ 1) ∧
      ((1122 + 1) * fastPow 3 2301 ≤ 1122 * fastPow 2 3647 ∧
        (32768 + 1) ^ (3 * 8) * 1122 ^ 1 ≤ 32768 ^ (3 * 8) * (1122 + 1) ^ 1) ∧
      ((1845 + 1) * fastPow 3 7621 ≤ 1845 * fastPow 2 12079 ∧
        (32768 + 1) ^ (5 * 7) * 1845 ^ 2 ≤ 32768 ^ (5 * 7) * (1845 + 1) ^ 2) ∧
      ((2006 + 1) * fastPow 3 8286 ≤ 2006 * fastPow 2 13133 ∧
        (32768 + 1) ^ (4 * 4) * 2006 ^ 1 ≤ 32768 ^ (4 * 4) * (2006 + 1) ^ 1) := by decide
  rwa [fastPow_eq 3 1636 (by decide), fastPow_eq 2 2593 (by decide),
    fastPow_eq 3 2301 (by decide), fastPow_eq 2 3647 (by decide),
    fastPow_eq 3 7621 (by decide), fastPow_eq 2 12079 (by decide),
    fastPow_eq 3 8286 (by decide), fastPow_eq 2 13133 (by decide)] at h

private theorem mCircuit_32k_witness_B :
    ((2722 + 1) * 3 ^ 10281 ≤ 2722 * 2 ^ 16295 ∧
      (32768 + 1) ^ (3 * 4) * 2722 ^ 1 ≤ 32768 ^ (3 * 4) * (2722 + 1) ^ 1) ∧
    ((4229 + 1) * 3 ^ 12276 ≤ 4229 * 2 ^ 19457 ∧
      (32768 + 1) ^ (5 * 3) * 4229 ^ 2 ≤ 32768 ^ (5 * 3) * (4229 + 1) ^ 2) ∧
    ((5186 + 1) * 3 ^ 12941 ≤ 5186 * 2 ^ 20511 ∧
      (32768 + 1) ^ (4 * 3) * 5186 ^ 2 ≤ 32768 ^ (4 * 3) * (5186 + 1) ^ 2 ∧
      (32768 + 1) ^ (5 * 1) * 5186 ^ 1 ≤ 32768 ^ (5 * 1) * (5186 + 1) ^ 1) ∧
    ((6704 + 1) * 3 ^ 13606 ≤ 6704 * 2 ^ 21565 ∧
      (32768 + 1) ^ (3 * 3) * 6704 ^ 2 ≤ 32768 ^ (3 * 3) * (6704 + 1) ^ 2 ∧
      (32768 + 1) ^ (4 * 1) * 6704 ^ 1 ≤ 32768 ^ (4 * 1) * (6704 + 1) ^ 1) ∧
    ((9478 + 1) * 3 ^ 14271 ≤ 9478 * 2 ^ 22619 ∧
      (32768 + 1) ^ (3 * 1) * 9478 ^ 1 ≤ 32768 ^ (3 * 1) * (9478 + 1) ^ 1) := by
  have h :
      ((2722 + 1) * fastPow 3 10281 ≤ 2722 * fastPow 2 16295 ∧
        (32768 + 1) ^ (3 * 4) * 2722 ^ 1 ≤ 32768 ^ (3 * 4) * (2722 + 1) ^ 1) ∧
      ((4229 + 1) * fastPow 3 12276 ≤ 4229 * fastPow 2 19457 ∧
        (32768 + 1) ^ (5 * 3) * 4229 ^ 2 ≤ 32768 ^ (5 * 3) * (4229 + 1) ^ 2) ∧
      ((5186 + 1) * fastPow 3 12941 ≤ 5186 * fastPow 2 20511 ∧
        (32768 + 1) ^ (4 * 3) * 5186 ^ 2 ≤ 32768 ^ (4 * 3) * (5186 + 1) ^ 2 ∧
        (32768 + 1) ^ (5 * 1) * 5186 ^ 1 ≤ 32768 ^ (5 * 1) * (5186 + 1) ^ 1) ∧
      ((6704 + 1) * fastPow 3 13606 ≤ 6704 * fastPow 2 21565 ∧
        (32768 + 1) ^ (3 * 3) * 6704 ^ 2 ≤ 32768 ^ (3 * 3) * (6704 + 1) ^ 2 ∧
        (32768 + 1) ^ (4 * 1) * 6704 ^ 1 ≤ 32768 ^ (4 * 1) * (6704 + 1) ^ 1) ∧
      ((9478 + 1) * fastPow 3 14271 ≤ 9478 * fastPow 2 22619 ∧
        (32768 + 1) ^ (3 * 1) * 9478 ^ 1 ≤ 32768 ^ (3 * 1) * (9478 + 1) ^ 1) := by decide
  rwa [fastPow_eq 3 10281 (by decide), fastPow_eq 2 16295 (by decide),
    fastPow_eq 3 12276 (by decide), fastPow_eq 2 19457 (by decide),
    fastPow_eq 3 12941 (by decide), fastPow_eq 2 20511 (by decide),
    fastPow_eq 3 13606 (by decide), fastPow_eq 2 21565 (by decide),
    fastPow_eq 3 14271 (by decide), fastPow_eq 2 22619 (by decide)] at h

private theorem mCircuit_32k_halvings_witness :
    2 ^ 23672 < 3 ^ 14936 ∧ 2 ^ 22618 < 3 ^ 14271 ∧ 2 ^ 21564 < 3 ^ 13606 := by
  have h : fastPow 2 23672 < fastPow 3 14936 ∧ fastPow 2 22618 < fastPow 3 14271 ∧
      fastPow 2 21564 < fastPow 3 13606 := by decide
  rwa [fastPow_eq 2 23672 (by decide), fastPow_eq 3 14936 (by decide),
    fastPow_eq 2 22618 (by decide), fastPow_eq 3 14271 (by decide),
    fastPow_eq 2 21564 (by decide), fastPow_eq 3 13606 (by decide)] at h

/-- **Unconditional 3-Circuit Odd-Length Lower Bound (`14936 ≤ K`, `1244x` leap over `K ≤ 12`):**
every non-trivial positive 3-circuit cycle has `14936 ≤ k₁ + k₂ + k₃`, `23673 ≤ S`, and
`38609 ≤ K + S` (zero external hypotheses). -/
theorem threeCircuit_unconditional_bounds {n k₁ e₁ k₂ e₂ k₃ e₃ : Nat}
    (h : IsThreeCircuitCycle n k₁ e₁ k₂ e₂ k₃ e₃) :
    14936 ≤ k₁ + k₂ + k₃ ∧ 23673 ≤ k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3 ∧
      38609 ≤ (k₁ + k₂ + k₃) + (k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3) := by
  have hm := isThreeCircuitCycle_iff_isMCircuitCycle.mp h
  have hM := mCircuit_orbit_ge_32768 hm
  have hK0 : 306 ≤ mCircuitK [(k₁, e₁), (k₂, e₂), (k₃, e₃)] :=
    (mCircuit_unconditional_eliahou_bounds hm).2.1
  have hL := log2ThreeCF_lower_exps.2.2.2.2
  have h1 := mCircuit_cf_elimination_step (M := 32768) (m := 3) (pL := 1054) (qL := 665)
    (pU := 3647) (qU := 2301) (K₀ := 306) (a := 8) (b := 1) (d := 1122)
    (by decide) (by decide) (by decide) (by decide) hL (cf_semi_det_665 3) (by decide)
    mCircuit_32k_witness_A.2.1.1 mCircuit_32k_witness_A.2.1.2 rfl hm hM hK0
  have h2 := mCircuit_cf_elimination_step (M := 32768) (m := 3) (pL := 1054) (qL := 665)
    (pU := 16295) (qU := 10281) (K₀ := 2966) (a := 4) (b := 1) (d := 2722)
    (by decide) (by decide) (by decide) (by decide) hL (cf_semi_det_665 15) (by decide)
    mCircuit_32k_witness_B.1.1 mCircuit_32k_witness_B.1.2 rfl hm hM h1
  have h3 := mCircuit_cf_elimination_step (M := 32768) (m := 3) (pL := 1054) (qL := 665)
    (pU := 21565) (qU := 13606) (K₀ := 10946) (a := 3) (b := 2) (d := 6704)
    (by decide) (by decide) (by decide) (by decide) hL (cf_semi_det_665 20) (by decide)
    mCircuit_32k_witness_B.2.2.2.1.1 mCircuit_32k_witness_B.2.2.2.1.2.1 rfl hm hM h2
  have h4 := mCircuit_cf_elimination_step (M := 32768) (m := 3) (pL := 1054) (qL := 665)
    (pU := 22619) (qU := 14271) (K₀ := 14271) (a := 1) (b := 1) (d := 9478)
    (by decide) (by decide) (by decide) (by decide) hL (cf_semi_det_665 21) (by decide)
    mCircuit_32k_witness_B.2.2.2.2.1 mCircuit_32k_witness_B.2.2.2.2.2 rfl hm hM h3
  have hKeq : mCircuitK [(k₁, e₁), (k₂, e₂), (k₃, e₃)] = k₁ + k₂ + k₃ := by
    simp only [mCircuitK, List.map, List.sum_cons, List.sum_nil]; omega
  rw [hKeq] at h4
  have h4' : 14936 ≤ k₁ + k₂ + k₃ := Nat.le_trans (by decide : 14936 ≤ 14271 + 665) h4
  have hS := halving_ge_of_k_ge (threeCircuit_pow_lt h) h4' mCircuit_32k_halvings_witness.1
  exact ⟨h4', hS, by omega⟩

/-- **Flagship Unconditional 3-Circuit Elimination (`K ≤ 14935`, zero `native_decide`).** -/
theorem no_nontrivial_threeCircuit_le_14935 :
    ∀ n k₁ e₁ k₂ e₂ k₃ e₃ : Nat, k₁ + k₂ + k₃ ≤ 14935 →
      ¬ IsThreeCircuitCycle n k₁ e₁ k₂ e₂ k₃ e₃ :=
  fun _ _ _ _ _ _ _ hle hcyc => by have hk := (threeCircuit_unconditional_bounds hcyc).1; omega

/-- **Unconditional 4-Circuit Elimination (`K ≤ 14270`, `1,189x` leap over `K ≤ 12`).** -/
theorem fourCircuit_unconditional_bounds {cs : List (Nat × Nat)} {n : Nat}
    (hlen : cs.length = 4) (h : IsMCircuitCycle cs n) :
    14271 ≤ mCircuitK cs ∧ 22619 ≤ mCircuitS cs ∧ 36890 ≤ mCircuitK cs + mCircuitS cs := by
  have hM := mCircuit_orbit_ge_32768 h
  have hK0 : 306 ≤ mCircuitK cs := (mCircuit_unconditional_eliahou_bounds h).2.1
  have hL := log2ThreeCF_lower_exps.2.2.2.2
  have h1 := mCircuit_cf_elimination_step (M := 32768) (m := 4) (pL := 1054) (qL := 665)
    (pU := 2593) (qU := 1636) (K₀ := 306) (a := 6) (b := 1) (d := 1070)
    (by decide) (by decide) (by decide) (by decide) hL (cf_semi_det_665 2) (by decide)
    mCircuit_32k_witness_A.1.1 mCircuit_32k_witness_A.1.2.1 hlen h hM hK0
  have h2 := mCircuit_cf_elimination_step (M := 32768) (m := 4) (pL := 1054) (qL := 665)
    (pU := 13133) (qU := 8286) (K₀ := 2301) (a := 4) (b := 1) (d := 2006)
    (by decide) (by decide) (by decide) (by decide) hL (cf_semi_det_665 12) (by decide)
    mCircuit_32k_witness_A.2.2.2.1 mCircuit_32k_witness_A.2.2.2.2 hlen h hM h1
  have h3 := mCircuit_cf_elimination_step (M := 32768) (m := 4) (pL := 1054) (qL := 665)
    (pU := 20511) (qU := 12941) (K₀ := 8951) (a := 3) (b := 2) (d := 5186)
    (by decide) (by decide) (by decide) (by decide) hL (cf_semi_det_665 19) (by decide)
    mCircuit_32k_witness_B.2.2.1.1 mCircuit_32k_witness_B.2.2.1.2.1 hlen h hM h2
  have h4 := mCircuit_cf_elimination_step (M := 32768) (m := 4) (pL := 1054) (qL := 665)
    (pU := 21565) (qU := 13606) (K₀ := 13606) (a := 1) (b := 1) (d := 6704)
    (by decide) (by decide) (by decide) (by decide) hL (cf_semi_det_665 20) (by decide)
    mCircuit_32k_witness_B.2.2.2.1.1 mCircuit_32k_witness_B.2.2.2.1.2.2 hlen h hM h3
  have h4' : 14271 ≤ mCircuitK cs := Nat.le_trans (by decide : 14271 ≤ 13606 + 665) h4
  have hS := halving_ge_of_k_ge h.pow_lt h4' mCircuit_32k_halvings_witness.2.1
  exact ⟨h4', hS, by omega⟩

/-- **Unconditional 4-Circuit Elimination (`K ≤ 14270`).** -/
theorem no_nontrivial_fourCircuit_le_14270 :
    ∀ cs : List (Nat × Nat), ∀ n : Nat,
      cs.length = 4 → mCircuitK cs ≤ 14270 → ¬ IsMCircuitCycle cs n :=
  fun _ _ hlen hle hcyc => by have hk := (fourCircuit_unconditional_bounds hlen hcyc).1; omega

/-- **Unconditional 5-Circuit Elimination (`K ≤ 13605`).** -/
theorem fiveCircuit_unconditional_bounds {cs : List (Nat × Nat)} {n : Nat}
    (hlen : cs.length = 5) (h : IsMCircuitCycle cs n) :
    13606 ≤ mCircuitK cs ∧ 21565 ≤ mCircuitS cs ∧ 35171 ≤ mCircuitK cs + mCircuitS cs := by
  have hM := mCircuit_orbit_ge_32768 h
  have hK0 : 306 ≤ mCircuitK cs := (mCircuit_unconditional_eliahou_bounds h).2.1
  have hL := log2ThreeCF_lower_exps.2.2.2.2
  have h1 := mCircuit_cf_elimination_step (M := 32768) (m := 5) (pL := 1054) (qL := 665)
    (pU := 2593) (qU := 1636) (K₀ := 306) (a := 6) (b := 1) (d := 1070)
    (by decide) (by decide) (by decide) (by decide) hL (cf_semi_det_665 2) (by decide)
    mCircuit_32k_witness_A.1.1 mCircuit_32k_witness_A.1.2.2 hlen h hM hK0
  have h2 := mCircuit_cf_elimination_step (M := 32768) (m := 5) (pL := 1054) (qL := 665)
    (pU := 12079) (qU := 7621) (K₀ := 2301) (a := 7) (b := 2) (d := 1845)
    (by decide) (by decide) (by decide) (by decide) hL (cf_semi_det_665 11) (by decide)
    mCircuit_32k_witness_A.2.2.1.1 mCircuit_32k_witness_A.2.2.1.2 hlen h hM h1
  have h3 := mCircuit_cf_elimination_step (M := 32768) (m := 5) (pL := 1054) (qL := 665)
    (pU := 19457) (qU := 12276) (K₀ := 8286) (a := 3) (b := 2) (d := 4229)
    (by decide) (by decide) (by decide) (by decide) hL (cf_semi_det_665 18) (by decide)
    mCircuit_32k_witness_B.2.1.1 mCircuit_32k_witness_B.2.1.2 hlen h hM h2
  have h4 := mCircuit_cf_elimination_step (M := 32768) (m := 5) (pL := 1054) (qL := 665)
    (pU := 20511) (qU := 12941) (K₀ := 12941) (a := 1) (b := 1) (d := 5186)
    (by decide) (by decide) (by decide) (by decide) hL (cf_semi_det_665 19) (by decide)
    mCircuit_32k_witness_B.2.2.1.1 mCircuit_32k_witness_B.2.2.1.2.2 hlen h hM h3
  have h4' : 13606 ≤ mCircuitK cs := Nat.le_trans (by decide : 13606 ≤ 12941 + 665) h4
  have hS := halving_ge_of_k_ge h.pow_lt h4' mCircuit_32k_halvings_witness.2.2
  exact ⟨h4', hS, by omega⟩

/-- Combined Bernoulli + CF elimination step for large `M`, avoiding `M ^ (m * a)` evaluation. -/
theorem mCircuit_cf_elimination_bernoulli {M m pL qL pU qU K₀ a d : Nat}
    (hMpos : 0 < M) (hqU : 0 < qU) (hd : 0 < d)
    (hL : 2 ^ pL < 3 ^ qL) (hdet : pU * qL = pL * qU + 1)
    (hrel : qU ≤ a * K₀) (hgap : (d + 1) * 3 ^ qU ≤ d * 2 ^ pU)
    (hQM : (d + 1) * (m * a) ≤ M)
    {cs : List (Nat × Nat)} {n : Nat}
    (hm : cs.length = m) (hcyc : IsMCircuitCycle cs n)
    (hM : ∀ i : Nat, M ≤ syracuseIter i n) (hK₀ : K₀ ≤ mCircuitK cs) :
    qU + qL ≤ mCircuitK cs :=
  mCircuit_cf_elimination_step hMpos hqU (by decide) hd hL hdet (by simpa using hrel) hgap
    (mCircuit_bernoulli_step M (m * a) d hMpos hQM) hm hcyc hM hK₀

/-- **Conditional 3-Circuit Lifting (`M = 2^40` ⇒ `K ≤ 64497106`):**
stopping-time verification `< 2^40` forces `64497107 ≤ K`, `102225496 ≤ S`, and
`166722603 ≤ K + S` for ALL non-trivial 3-circuits via `mCircuit_cf_elimination_bernoulli`. -/
theorem threeCircuit_bounds_of_stopping_pow2_40
    (hstop : ∀ m : Nat, 2 ≤ m → m < 2 ^ 40 → HasFiniteStoppingTime m)
    {n k₁ e₁ k₂ e₂ k₃ e₃ : Nat} (h : IsThreeCircuitCycle n k₁ e₁ k₂ e₂ k₃ e₃) :
    64497107 ≤ k₁ + k₂ + k₃ ∧ 102225496 ≤ k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3 ∧
      166722603 ≤ (k₁ + k₂ + k₃) + (k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3) := by
  have hm := isThreeCircuitCycle_iff_isMCircuitCycle.mp h
  have hM := mCircuit_orbit_ge_of_stopping hstop hm
  have hk14k : 14936 ≤ mCircuitK [(k₁, e₁), (k₂, e₂), (k₃, e₃)] := by
    have hbd := (threeCircuit_unconditional_bounds h).1
    simp only [mCircuitK, List.map, List.sum_cons, List.sum_nil]; omega
  have hk := mCircuit_cf_elimination_bernoulli (M := 2 ^ 40) (m := 3) (pL := 85137581)
    (qL := 53715833) (pU := 17087915) (qU := 10781274) (K₀ := 14936) (a := 722)
    (d := 82000000) (by decide) (by decide) (by decide) cf_witness_twoCircuit_64m.1
    log2ThreeCFExt2_det_16_17 (by decide) cf_witness_twoCircuit_64m.2.2.1 (by decide)
    rfl hm hM hk14k
  have hKeq : mCircuitK [(k₁, e₁), (k₂, e₂), (k₃, e₃)] = k₁ + k₂ + k₃ := by
    simp only [mCircuitK, List.map, List.sum_cons, List.sum_nil]; omega
  rw [hKeq] at hk
  have hk' : 64497107 ≤ k₁ + k₂ + k₃ :=
    Nat.le_trans (by decide : 64497107 ≤ 10781274 + 53715833) hk
  have hS := halving_ge_of_k_ge (threeCircuit_pow_lt h) hk' cf_witness_twoCircuit_extra.2.2
  exact ⟨hk', hS, by omega⟩

/-- **Conditional `m`-Circuit Lifting (`M = 2^68`, `m ≤ 1000000` ⇒ `K ≤ 64497106`):**
Barina-scale stopping-time verification `< 2^68` eliminates ALL `m`-circuits with `m ≤ 10^6` and
`K ≤ 64497106`, forcing `64497107 ≤ K`, `102225496 ≤ S`, and `166722603 ≤ K + S`. -/
theorem mCircuit_bounds_of_stopping_pow2_68
    (hstop : ∀ m : Nat, 2 ≤ m → m < 2 ^ 68 → HasFiniteStoppingTime m)
    {cs : List (Nat × Nat)} {n : Nat} (hm_le : cs.length ≤ 1000000)
    (h : IsMCircuitCycle cs n) :
    64497107 ≤ mCircuitK cs ∧ 102225496 ≤ mCircuitS cs ∧
      166722603 ≤ mCircuitK cs + mCircuitS cs := by
  have hM := mCircuit_orbit_ge_of_stopping hstop h
  have hK0 : 306 ≤ mCircuitK cs := (mCircuit_unconditional_eliahou_bounds h).2.1
  have hQM : (82000000 + 1) * (cs.length * 35233) ≤ 2 ^ 68 :=
    Nat.le_trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right 35233 hm_le))
      (by decide : (82000000 + 1) * (1000000 * 35233) ≤ 2 ^ 68)
  have hk := mCircuit_cf_elimination_bernoulli (M := 2 ^ 68) (m := cs.length) (pL := 85137581)
    (qL := 53715833) (pU := 17087915) (qU := 10781274) (K₀ := 306) (a := 35233)
    (d := 82000000) (by decide) (by decide) (by decide) cf_witness_twoCircuit_64m.1
    log2ThreeCFExt2_det_16_17 (by decide) cf_witness_twoCircuit_64m.2.2.1 hQM rfl h hM hK0
  have hk' : 64497107 ≤ mCircuitK cs :=
    Nat.le_trans (by decide : 64497107 ≤ 10781274 + 53715833) hk
  have hS := halving_ge_of_k_ge h.pow_lt hk' cf_witness_twoCircuit_extra.2.2
  exact ⟨hk', hS, by omega⟩

/-! ### 6. Explicit Barrier 1-5 Separations -/

/-- **Barrier 1 Separation (`3n - 1` on `ℕ⁺`):** `n = 5` and 2-circuit `n = 17` (`K = 7`). -/
theorem barrier1_twoCircuit_three_n_minus_one :
    (Barriers.genIter 3 (-1) 5 5 = 5 ∧ 2 ≤ 64497106 ∧ ¬ (3 ^ 2 < 2 ^ 3)) ∧
    (Barriers.genIter 3 (-1) 18 17 = 17 ∧ (3 ^ 7 - 2 ^ 11) * 17 = twoCircuitOffset 4 2 3 4 ∧
      7 ≤ 64497106 ∧ ¬ (3 ^ 7 < 2 ^ 11)) :=
  ⟨⟨Barriers.three_n_minus_one_cycle_5.1, by decide, by decide⟩,
    ⟨by decide, by decide, by decide, by decide⟩⟩

/-- **Barrier 2 Separation (`5n + 1` on `ℕ⁺`):** `n = 1` and `n = 13` violate Simons bands. -/
theorem barrier2_twoCircuit_five_n_plus_one :
    (Barriers.genIter 5 1 7 1 = 1 ∧ 2 ≤ 64497106 ∧ 5 ^ 2 < 2 ^ 5 ∧ ¬ (9 * 2 ^ 5 < 16 * 3 ^ 2)) ∧
    (Barriers.genIter 5 1 10 13 = 13 ∧ (∀ j : Nat, j < 10 → Barriers.genIter 5 1 j 13 ≠ 1) ∧
      3 ≤ 14935 ∧ 5 ^ 3 < 2 ^ 7 ∧ ¬ (9 * 2 ^ 7 < 16 * 3 ^ 3) ∧ ¬ (27 * 2 ^ 7 < 64 * 3 ^ 3)) :=
  ⟨⟨by decide, by decide, by decide, by decide⟩,
    ⟨Barriers.five_n_plus_one_cycle_13.1, Barriers.five_n_plus_one_cycle_13.2,
      by decide, by decide, by decide, by decide⟩⟩

/-- **Barrier 3 Separation (`3n + 1` on `ℤ_{<0}`):** `n = -5` and 2-circuit `n = -17`. -/
theorem barrier3_twoCircuit_neg_int :
    (Barriers.genIter 3 1 5 (-5) = -5 ∧ 2 ≤ 64497106 ∧ ¬ (3 ^ 2 < 2 ^ 3)) ∧
    (Barriers.genIter 3 1 18 (-17) = -17 ∧
      ((2 : Int) ^ 11 - (3 : Int) ^ 7) * (-17) = (twoCircuitOffset 4 2 3 4 : Int) ∧
      7 ≤ 64497106 ∧ ¬ (3 ^ 7 < 2 ^ 11)) :=
  ⟨⟨Barriers.neg_int_cycle_neg5.1, by decide, by decide⟩,
    ⟨by decide, by decide, by decide, by decide⟩⟩

/-- **Barrier 4 Separation (`ℤ₂` rational 2-circuit `23 / 5` and 3-circuit `143 / 47`).** -/
theorem barrier4_twoCircuit_twoAdic :
    let x2 := periodicPoint (twoCircuitVec 2 2 1 2) (by decide)
    let x3 := periodicPoint (threeCircuitVec 1 2 1 2 2 2) (by decide)
    (x2 = ⟨23, 5, by decide⟩ ∧ 3 ≤ 64497106 ∧ 3 ^ 3 < 2 ^ 5 ∧ 9 * 2 ^ 5 < 16 * 3 ^ 3 ∧
      OddDenomRat.syracuseIter 3 x2 = x2 ∧ (¬ ∃ m : Int, x2.Equiv (OddDenomRat.ofInt m))) ∧
    (x3 = ⟨143, 47, by decide⟩ ∧ 4 ≤ 14935 ∧ 3 ^ 4 < 2 ^ 7 ∧ 27 * 2 ^ 7 < 64 * 3 ^ 4 ∧
      OddDenomRat.syracuseIter 4 x3 = x3 ∧ (¬ ∃ m : Int, x3.Equiv (OddDenomRat.ofInt m))) :=
  ⟨⟨barrier4_twoAdic_twoCircuit_separation.2.2.1, by decide, by decide, by decide,
      barrier4_twoAdic_twoCircuit_separation.2.2.2.1,
      barrier4_twoAdic_twoCircuit_separation.2.2.2.2.2⟩,
    ⟨barrier4_twoAdic_threeCircuit_separation.2.2.1, by decide, by decide, by decide,
      barrier4_twoAdic_threeCircuit_separation.2.2.2.1,
      barrier4_twoAdic_threeCircuit_separation.2.2.2.2.2⟩⟩

/-- **Barrier 5 Separation (Conway 1972 / Finite Verification Horizon).** -/
theorem barrier5_twoCircuit_conway_finite_horizon :
    (∀ n k₁ e₁ k₂ e₂ : Nat, k₁ + k₂ ≤ 64497106 → ¬ IsTwoCircuitCycle n k₁ e₁ k₂ e₂) ∧
    (∀ n k₁ e₁ k₂ e₂ k₃ e₃ : Nat, k₁ + k₂ + k₃ ≤ 14935 →
      ¬ IsThreeCircuitCycle n k₁ e₁ k₂ e₂ k₃ e₃) ∧
    (∀ cs : List (Nat × Nat), ∀ n : Nat,
      cs.length = 4 → mCircuitK cs ≤ 14270 → ¬ IsMCircuitCycle cs n) ∧
    ((∀ k S : Nat, 64497106 < k → 3 ^ k < 2 ^ S →
        16 * 3 ^ (3 * k) ≤ 4 ^ k * (2 ^ S - 3 ^ k) ^ 2) →
      ∀ n k₁ e₁ k₂ e₂ : Nat, ¬ IsTwoCircuitCycle n k₁ e₁ k₂ e₂) :=
  ⟨no_nontrivial_twoCircuit_le_64497106, no_nontrivial_threeCircuit_le_14935,
    no_nontrivial_fourCircuit_le_14270, no_nontrivial_twoCircuit_of_diophantine_bound_gt_64497106⟩

end SolveCollatz
