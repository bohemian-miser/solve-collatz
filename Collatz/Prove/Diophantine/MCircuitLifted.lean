/-
Copyright (c) 2026 The solve-collatz contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Collatz.Known.EliahouLifted
public import Collatz.Prove.Diophantine.TwoCircuitConvergents

/-!
# `2^20`-Lifted `m`-Circuit Continued-Fraction Elimination (`PROVE-B1` Phase 5)

Pure Lean 4 core formalization (zero Mathlib, zero `sorry`, zero `native_decide`):
1. Orbit-wide unconditional `1048576 ≤ syracuseIter i n` (`M = 2^20` from `EliahouLifted.lean`,
   `32x` stronger than `32768`), forcing `2966 ≤ K`, `4701 ≤ S`, `7667 ≤ K + S`,
   `1048576^m * 2^S < 1048577^m * 3^K`, `mCircuitS cs = minHalvings (mCircuitK cs)` for ALL
   `m ≤ 524288` (`32x` leap over `16384`), and `twoCircuit_challenge_bounds` lifted to `2^20 ≤ n`.
2. Unconditional `m`-circuit CF elimination at `M = 1048576`:
   - `m ≤ 500`: `8951 ≤ K`, `14187 ≤ S`, `23138 ≤ K + S`
   - `m ≤ 68` (Simons-de Weger threshold): `14936 ≤ K`, `23673 ≤ S`, `38609 ≤ K + S`
   - `m ≤ 64`: `15601 ≤ K`, `24727 ≤ S`, `40328 ≤ K + S`
   - `m ≤ 19` (incl. `m ≤ 16`): `47468 ≤ K`, `75235 ≤ S`, `122703 ≤ K + S`
   - `m ≤ 11` (incl. `4, 5, 6`-circuits): `79335 ≤ K`, `125743 ≤ S`, `205078 ≤ K + S`
   - `3`-circuits: `190537 ≤ K`, `301994 ≤ S`, `492531 ≤ K + S` (`K ≤ 190536` eliminated!).
3. Direct bridges to frozen `Challenge.HasNontrivialCycle` and Barrier 1–5 separations.
-/

@[expose] public section

namespace SolveCollatz

/-! ### 1. Orbit-Wide `1048576 ≤` Lower Bound & `m ≤ 524288` Halving Uniqueness -/

/-- Every iterate `syracuseIter i n` along a non-trivial `m`-circuit cycle satisfies
`1048576 ≤ syracuseIter i n` unconditionally (`M = 2^20` from `EliahouLifted.lean`). -/
theorem mCircuit_orbit_ge_1048576 {cs : List (Nat × Nat)} {n : Nat}
    (h : IsMCircuitCycle cs n) (i : Nat) : 1048576 ≤ syracuseIter i n :=
  mCircuit_orbit_ge_of_stopping (fun _ h2 hlt => small_lt_1048576_finiteStoppingTime h2 hlt) h i

/-- Unconditional `EliahouLifted` lower bounds for any `IsMCircuitCycle`:
`1048576 ≤ n`, `2966 ≤ mCircuitK cs`, `4701 ≤ mCircuitS cs`, and `7667 ≤ K + S`. -/
theorem mCircuit_unconditional_eliahou_lifted_bounds {cs : List (Nat × Nat)} {n : Nat}
    (h : IsMCircuitCycle cs n) :
    1048576 ≤ n ∧ 2966 ≤ mCircuitK cs ∧ 4701 ≤ mCircuitS cs ∧
      7667 ≤ mCircuitK cs + mCircuitS cs := by
  have hne : ∀ i : Nat, i < mCircuitK cs → syracuseIter i n ≠ 1 := by
    intro i _; have hle := (mCircuit_valley_three_le h i).2; omega
  rcases syracuseCycle_of_syracuse_cycle h.mCircuitK_pos h.one_lt_n h.period_eq hne with
    ⟨C, hCk, hCS⟩
  have hbd := unconditional_syracuseCycle_lifted_bounds C
  have hS_eq : C.totalVal = mCircuitS cs := by rw [hCS, h.totalVal_eq]
  have h1m := mCircuit_orbit_ge_1048576 h 0
  simp only [syracuseIter] at h1m
  refine ⟨h1m, ?_, ?_, ?_⟩
  · rw [← hCk]; exact hbd.2.1
  · rw [← hS_eq]; exact hbd.2.2.1
  · rw [← hCk, ← hS_eq]; simpa [SyracuseCycle.collatzLen, Nat.add_comm] using hbd.2.2.2

/-- **Unconditional `1048576`-Valley `m`-Circuit Band Bound:**
`1048576 ^ cs.length * 2 ^ mCircuitS cs < 1048577 ^ cs.length * 3 ^ mCircuitK cs`. -/
theorem mCircuit_unconditional_1048576_bound {cs : List (Nat × Nat)} {n : Nat}
    (h : IsMCircuitCycle cs n) :
    1048576 ^ cs.length * 2 ^ mCircuitS cs < 1048577 ^ cs.length * 3 ^ mCircuitK cs :=
  mCircuit_archimedean_M_bound (by decide) h (mCircuit_orbit_ge_1048576 h)

/-- **Unconditional Sharp `S = minHalvings K` for `m ≤ 524288` (`32x` leap over `16384`):**
every non-trivial `m`-circuit cycle with `cs.length ≤ 524288` forces `mCircuitS cs` to equal
the unique minimal halving count `minHalvings (mCircuitK cs)`. -/
theorem mCircuit_totalVal_eq_minHalvings_le_524288 {cs : List (Nat × Nat)} {n : Nat}
    (hm : cs.length ≤ 524288) (h : IsMCircuitCycle cs n) :
    mCircuitS cs = minHalvings (mCircuitK cs) := by
  have h1m := mCircuit_unconditional_1048576_bound h
  have h2m : 1048577 ^ cs.length ≤ 2 * 1048576 ^ cs.length :=
    succ_pow_le_two_mul_pow (by decide : 0 < 1048576) (by omega)
  have hpow2 : 2 ^ mCircuitS cs < 2 * 3 ^ mCircuitK cs := by
    have hmul : 1048576 ^ cs.length * 2 ^ mCircuitS cs <
        1048576 ^ cs.length * (2 * 3 ^ mCircuitK cs) := by
      calc 1048576 ^ cs.length * 2 ^ mCircuitS cs
          < 1048577 ^ cs.length * 3 ^ mCircuitK cs := h1m
        _ ≤ (2 * 1048576 ^ cs.length) * 3 ^ mCircuitK cs := Nat.mul_le_mul_right _ h2m
        _ = 1048576 ^ cs.length * (2 * 3 ^ mCircuitK cs) := by ac_rfl
    exact Nat.lt_of_mul_lt_mul_left hmul
  exact steiner_band_unique h.pow_lt hpow2 (lt_two_pow_minHalvings (mCircuitK cs))
    (two_pow_minHalvings_lt_two_mul h.mCircuitK_pos)

/-- **Lifted Bridge to Frozen `Challenge.lean` for 2-Circuits (`1048576 ≤ n`):**
upgrades `twoCircuit_challenge_bounds` from `32768 ≤ n` to `1048576 ≤ n` alongside
`64497107 ≤ K`, `102225496 ≤ S`, and `166722603 ≤ K + S`. -/
theorem twoCircuit_challenge_bounds_lifted {n k₁ e₁ k₂ e₂ : Nat}
    (h : IsTwoCircuitCycle n k₁ e₁ k₂ e₂) :
    let K := k₁ + k₂; let S := k₁ + k₂ + e₁ + e₂ - 2
    HasNontrivialCycle ∧ collatzIter (K + S) n = n ∧
    (∀ j : Nat, j < K + S → collatzIter j n ≠ 1) ∧
    1048576 ≤ n ∧ 64497107 ≤ K ∧ 102225496 ≤ S ∧ 166722603 ≤ K + S := by
  have hb := twoCircuit_challenge_bounds h
  have h1m := mCircuit_orbit_ge_1048576 (isTwoCircuitCycle_iff_isMCircuitCycle.mp h) 0
  simp only [syracuseIter] at h1m
  exact ⟨hb.1, hb.2.1, hb.2.2.1, h1m, hb.2.2.2.2⟩

/-! ### 2. `log₂(3)` Continued-Fraction Witnesses & `M = 1048576` Bernoulli Helpers -/

private theorem log2ThreeCFExt2_semi_dets :
    24727 * 31867 = 50508 * 15601 + 1 ∧
    75235 * 31867 = 50508 * 47468 + 1 ∧
    125743 * 111202 = 176251 * 79335 + 1 := by
  decide

private theorem cf_semi_det_665_lifted {c pU qU : Nat}
    (hp : c * 1054 + 485 = pU) (hq : c * 665 + 306 = qU) :
    pU * 665 = 1054 * qU + 1 := by
  rw [← hp, ← hq]
  exact cf_semiconvergent_det (prev := (485, 306)) (cur := (1054, 665)) c (by decide)

private theorem mCircuit_1m_lower_halving_witness :
    2 ^ 50508 < 3 ^ 31867 ∧ 2 ^ 176251 < 3 ^ 111202 ∧
    2 ^ 14186 < 3 ^ 8951 ∧ 2 ^ 23672 < 3 ^ 14936 ∧
    2 ^ 24726 < 3 ^ 15601 ∧ 2 ^ 75234 < 3 ^ 47468 ∧
    2 ^ 125742 < 3 ^ 79335 ∧ 2 ^ 301993 < 3 ^ 190537 := by
  have h :
      fastPow 2 50508 < fastPow 3 31867 ∧ fastPow 2 176251 < fastPow 3 111202 ∧
      fastPow 2 14186 < fastPow 3 8951 ∧ fastPow 2 23672 < fastPow 3 14936 ∧
      fastPow 2 24726 < fastPow 3 15601 ∧ fastPow 2 75234 < fastPow 3 47468 ∧
      fastPow 2 125742 < fastPow 3 79335 ∧ fastPow 2 301993 < fastPow 3 190537 := by decide
  rwa [fastPow_eq 2 50508 (by decide), fastPow_eq 3 31867 (by decide),
    fastPow_eq 2 176251 (by decide), fastPow_eq 3 111202 (by decide),
    fastPow_eq 2 14186 (by decide), fastPow_eq 3 8951 (by decide),
    fastPow_eq 2 23672 (by decide), fastPow_eq 3 14936 (by decide),
    fastPow_eq 2 24726 (by decide), fastPow_eq 3 15601 (by decide),
    fastPow_eq 2 75234 (by decide), fastPow_eq 3 47468 (by decide),
    fastPow_eq 2 125742 (by decide), fastPow_eq 3 79335 (by decide),
    fastPow_eq 2 301993 (by decide), fastPow_eq 3 190537 (by decide)] at h

private theorem mCircuit_1m_gap_witness_500 :
    (1180 + 1) * 3 ^ 2966 ≤ 1180 * 2 ^ 4701 ∧
    (1244 + 1) * 3 ^ 3631 ≤ 1244 * 2 ^ 5755 ∧
    (1315 + 1) * 3 ^ 4296 ≤ 1315 * 2 ^ 6809 ∧
    (1395 + 1) * 3 ^ 4961 ≤ 1395 * 2 ^ 7863 ∧
    (1486 + 1) * 3 ^ 5626 ≤ 1486 * 2 ^ 8917 ∧
    (1589 + 1) * 3 ^ 6291 ≤ 1589 * 2 ^ 9971 ∧
    (1707 + 1) * 3 ^ 6956 ≤ 1707 * 2 ^ 11025 ∧
    (1845 + 1) * 3 ^ 7621 ≤ 1845 * 2 ^ 12079 ∧
    (2006 + 1) * 3 ^ 8286 ≤ 2006 * 2 ^ 13133 := by
  have h :
      (1180 + 1) * fastPow 3 2966 ≤ 1180 * fastPow 2 4701 ∧
      (1244 + 1) * fastPow 3 3631 ≤ 1244 * fastPow 2 5755 ∧
      (1315 + 1) * fastPow 3 4296 ≤ 1315 * fastPow 2 6809 ∧
      (1395 + 1) * fastPow 3 4961 ≤ 1395 * fastPow 2 7863 ∧
      (1486 + 1) * fastPow 3 5626 ≤ 1486 * fastPow 2 8917 ∧
      (1589 + 1) * fastPow 3 6291 ≤ 1589 * fastPow 2 9971 ∧
      (1707 + 1) * fastPow 3 6956 ≤ 1707 * fastPow 2 11025 ∧
      (1845 + 1) * fastPow 3 7621 ≤ 1845 * fastPow 2 12079 ∧
      (2006 + 1) * fastPow 3 8286 ≤ 2006 * fastPow 2 13133 := by decide
  rwa [fastPow_eq 3 2966 (by decide), fastPow_eq 2 4701 (by decide),
    fastPow_eq 3 3631 (by decide), fastPow_eq 2 5755 (by decide),
    fastPow_eq 3 4296 (by decide), fastPow_eq 2 6809 (by decide),
    fastPow_eq 3 4961 (by decide), fastPow_eq 2 7863 (by decide),
    fastPow_eq 3 5626 (by decide), fastPow_eq 2 8917 (by decide),
    fastPow_eq 3 6291 (by decide), fastPow_eq 2 9971 (by decide),
    fastPow_eq 3 6956 (by decide), fastPow_eq 2 11025 (by decide),
    fastPow_eq 3 7621 (by decide), fastPow_eq 2 12079 (by decide),
    fastPow_eq 3 8286 (by decide), fastPow_eq 2 13133 (by decide)] at h

private theorem mCircuit_1m_gap_witness_main :
    (3570 + 1) * 3 ^ 11611 ≤ 3570 * 2 ^ 18403 ∧
    (6704 + 1) * 3 ^ 13606 ≤ 6704 * 2 ^ 21565 ∧
    (9478 + 1) * 3 ^ 14271 ≤ 9478 * 2 ^ 22619 ∧
    (16168 + 1) * 3 ^ 14936 ≤ 16168 * 2 ^ 23673 ∧
    (54961 + 1) * 3 ^ 15601 ≤ 54961 * 2 ^ 24727 ∧
    (91494 + 1) * 3 ^ 47468 ≤ 91494 * 2 ^ 75235 ∧
    (272872 + 1) * 3 ^ 79335 ≤ 272872 * 2 ^ 125743 := by
  have h :
      (3570 + 1) * fastPow 3 11611 ≤ 3570 * fastPow 2 18403 ∧
      (6704 + 1) * fastPow 3 13606 ≤ 6704 * fastPow 2 21565 ∧
      (9478 + 1) * fastPow 3 14271 ≤ 9478 * fastPow 2 22619 ∧
      (16168 + 1) * fastPow 3 14936 ≤ 16168 * fastPow 2 23673 ∧
      (54961 + 1) * fastPow 3 15601 ≤ 54961 * fastPow 2 24727 ∧
      (91494 + 1) * fastPow 3 47468 ≤ 91494 * fastPow 2 75235 ∧
      (272872 + 1) * fastPow 3 79335 ≤ 272872 * fastPow 2 125743 := by decide
  rwa [fastPow_eq 3 11611 (by decide), fastPow_eq 2 18403 (by decide),
    fastPow_eq 3 13606 (by decide), fastPow_eq 2 21565 (by decide),
    fastPow_eq 3 14271 (by decide), fastPow_eq 2 22619 (by decide),
    fastPow_eq 3 14936 (by decide), fastPow_eq 2 23673 (by decide),
    fastPow_eq 3 15601 (by decide), fastPow_eq 2 24727 (by decide),
    fastPow_eq 3 47468 (by decide), fastPow_eq 2 75235 (by decide),
    fastPow_eq 3 79335 (by decide), fastPow_eq 2 125743 (by decide)] at h

private theorem lifted_cf_665_step {c pU qU K₀ K₁ a d : Nat} {cs : List (Nat × Nat)} {n : Nat}
    (hpU : c * 1054 + 485 = pU) (hqU : c * 665 + 306 = qU) (hK1 : qU + 665 = K₁)
    (hqUpos : 0 < qU) (hd : 0 < d) (hrel : qU ≤ a * K₀)
    (hgap : (d + 1) * 3 ^ qU ≤ d * 2 ^ pU)
    (hQM : (d + 1) * (cs.length * a) ≤ 1048576)
    (hcyc : IsMCircuitCycle cs n) (hK₀ : K₀ ≤ mCircuitK cs) :
    K₁ ≤ mCircuitK cs := by
  have hres := mCircuit_cf_elimination_bernoulli (M := 1048576) (m := cs.length)
    (pL := 1054) (qL := 665) (pU := pU) (qU := qU)
    (K₀ := K₀) (a := a) (d := d) (by decide) hqUpos hd
    log2ThreeCF_lower_exps.2.2.2.2 (cf_semi_det_665_lifted hpU hqU) hrel hgap hQM
    rfl hcyc (mCircuit_orbit_ge_1048576 hcyc) hK₀
  omega

private theorem lifted_halving_ge_of_k {cs : List (Nat × Nat)} {k₀ s₀ : Nat}
    (hpow : 3 ^ mCircuitK cs < 2 ^ mCircuitS cs) (hk : k₀ ≤ mCircuitK cs)
    (hw : 2 ^ s₀ < 3 ^ k₀) : s₀ + 1 ≤ mCircuitS cs := by
  have h3le : 3 ^ k₀ ≤ 3 ^ mCircuitK cs := Nat.pow_le_pow_right (by decide) hk
  have h2lt : 2 ^ s₀ < 2 ^ mCircuitS cs := Nat.lt_trans (Nat.lt_of_lt_of_le hw h3le) hpow
  by_cases hs : s₀ + 1 ≤ mCircuitS cs
  · exact hs
  · exact absurd h2lt (Nat.not_lt_of_ge (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))

/-! ### 3. Massive Unconditional `M = 1048576` CF Elimination for `m`-Circuit Families -/

/-- **Unconditional `m ≤ 500` Circuit Elimination (`K ≤ 8950` ruled out):**
every non-trivial `m`-circuit cycle with `cs.length ≤ 500` satisfies
`8951 ≤ mCircuitK cs`, `14187 ≤ mCircuitS cs`, and `23138 ≤ mCircuitK cs + mCircuitS cs`. -/
theorem mCircuit_unconditional_bounds_le_500 {cs : List (Nat × Nat)} {n : Nat}
    (hm : cs.length ≤ 500) (h : IsMCircuitCycle cs n) :
    8951 ≤ mCircuitK cs ∧ 14187 ≤ mCircuitS cs ∧ 23138 ≤ mCircuitK cs + mCircuitS cs := by
  have hK0 : 2966 ≤ mCircuitK cs := (mCircuit_unconditional_eliahou_lifted_bounds h).2.1
  have h1 := lifted_cf_665_step (c := 4) (pU := 4701) (qU := 2966) (K₀ := 2966) (K₁ := 3631)
    (a := 1) (d := 1180) rfl rfl rfl (by decide) (by decide) (by decide)
    mCircuit_1m_gap_witness_500.1 (by omega) h hK0
  have h2 := lifted_cf_665_step (c := 5) (pU := 5755) (qU := 3631) (K₀ := 3631) (K₁ := 4296)
    (a := 1) (d := 1244) rfl rfl rfl (by decide) (by decide) (by decide)
    mCircuit_1m_gap_witness_500.2.1 (by omega) h h1
  have h3 := lifted_cf_665_step (c := 6) (pU := 6809) (qU := 4296) (K₀ := 4296) (K₁ := 4961)
    (a := 1) (d := 1315) rfl rfl rfl (by decide) (by decide) (by decide)
    mCircuit_1m_gap_witness_500.2.2.1 (by omega) h h2
  have h4 := lifted_cf_665_step (c := 7) (pU := 7863) (qU := 4961) (K₀ := 4961) (K₁ := 5626)
    (a := 1) (d := 1395) rfl rfl rfl (by decide) (by decide) (by decide)
    mCircuit_1m_gap_witness_500.2.2.2.1 (by omega) h h3
  have h5 := lifted_cf_665_step (c := 8) (pU := 8917) (qU := 5626) (K₀ := 5626) (K₁ := 6291)
    (a := 1) (d := 1486) rfl rfl rfl (by decide) (by decide) (by decide)
    mCircuit_1m_gap_witness_500.2.2.2.2.1 (by omega) h h4
  have h6 := lifted_cf_665_step (c := 9) (pU := 9971) (qU := 6291) (K₀ := 6291) (K₁ := 6956)
    (a := 1) (d := 1589) rfl rfl rfl (by decide) (by decide) (by decide)
    mCircuit_1m_gap_witness_500.2.2.2.2.2.1 (by omega) h h5
  have h7 := lifted_cf_665_step (c := 10) (pU := 11025) (qU := 6956) (K₀ := 6956) (K₁ := 7621)
    (a := 1) (d := 1707) rfl rfl rfl (by decide) (by decide) (by decide)
    mCircuit_1m_gap_witness_500.2.2.2.2.2.2.1 (by omega) h h6
  have h8 := lifted_cf_665_step (c := 11) (pU := 12079) (qU := 7621) (K₀ := 7621) (K₁ := 8286)
    (a := 1) (d := 1845) rfl rfl rfl (by decide) (by decide) (by decide)
    mCircuit_1m_gap_witness_500.2.2.2.2.2.2.2.1 (by omega) h h7
  have h9 := lifted_cf_665_step (c := 12) (pU := 13133) (qU := 8286) (K₀ := 8286) (K₁ := 8951)
    (a := 1) (d := 2006) rfl rfl rfl (by decide) (by decide) (by decide)
    mCircuit_1m_gap_witness_500.2.2.2.2.2.2.2.2 (by omega) h h8
  have hS := lifted_halving_ge_of_k h.pow_lt h9 mCircuit_1m_lower_halving_witness.2.2.1
  exact ⟨h9, hS, by omega⟩

/-- **Unconditional `m ≤ 68` Circuit Elimination (Simons-de Weger, `K ≤ 14935` ruled out):**
every non-trivial `m`-circuit cycle with `cs.length ≤ 68` satisfies
`14936 ≤ mCircuitK cs`, `23673 ≤ mCircuitS cs`, and `38609 ≤ mCircuitK cs + mCircuitS cs`. -/
theorem mCircuit_unconditional_bounds_le_68 {cs : List (Nat × Nat)} {n : Nat}
    (hm : cs.length ≤ 68) (h : IsMCircuitCycle cs n) :
    14936 ≤ mCircuitK cs ∧ 23673 ≤ mCircuitS cs ∧ 38609 ≤ mCircuitK cs + mCircuitS cs := by
  have hK0 : 2966 ≤ mCircuitK cs := (mCircuit_unconditional_eliahou_lifted_bounds h).2.1
  have h1 := lifted_cf_665_step (c := 17) (pU := 18403) (qU := 11611) (K₀ := 2966) (K₁ := 12276)
    (a := 4) (d := 3570) rfl rfl rfl (by decide) (by decide) (by decide)
    mCircuit_1m_gap_witness_main.1 (by omega) h hK0
  have h2 := lifted_cf_665_step (c := 20) (pU := 21565) (qU := 13606) (K₀ := 12276) (K₁ := 14271)
    (a := 2) (d := 6704) rfl rfl rfl (by decide) (by decide) (by decide)
    mCircuit_1m_gap_witness_main.2.1 (by omega) h h1
  have h3 := lifted_cf_665_step (c := 21) (pU := 22619) (qU := 14271) (K₀ := 14271) (K₁ := 14936)
    (a := 1) (d := 9478) rfl rfl rfl (by decide) (by decide) (by decide)
    mCircuit_1m_gap_witness_main.2.2.1 (by omega) h h2
  have hS := lifted_halving_ge_of_k h.pow_lt h3 mCircuit_1m_lower_halving_witness.2.2.2.1
  exact ⟨h3, hS, by omega⟩

/-- **Unconditional `m ≤ 64` Circuit Elimination (`K ≤ 15600` ruled out):**
every non-trivial `m`-circuit cycle with `cs.length ≤ 64` satisfies
`15601 ≤ mCircuitK cs`, `24727 ≤ mCircuitS cs`, and `40328 ≤ mCircuitK cs + mCircuitS cs`. -/
theorem mCircuit_unconditional_bounds_le_64 {cs : List (Nat × Nat)} {n : Nat}
    (hm : cs.length ≤ 64) (h : IsMCircuitCycle cs n) :
    15601 ≤ mCircuitK cs ∧ 24727 ≤ mCircuitS cs ∧ 40328 ≤ mCircuitK cs + mCircuitS cs := by
  have h68 := (mCircuit_unconditional_bounds_le_68 (by omega) h).1
  have hk := lifted_cf_665_step (c := 22) (pU := 23673) (qU := 14936) (K₀ := 14936) (K₁ := 15601)
    (a := 1) (d := 16168) rfl rfl rfl (by decide) (by decide) (by decide)
    mCircuit_1m_gap_witness_main.2.2.2.1 (by omega) h h68
  have hS := lifted_halving_ge_of_k h.pow_lt hk mCircuit_1m_lower_halving_witness.2.2.2.2.1
  exact ⟨hk, hS, by omega⟩

/-- **Unconditional `m ≤ 19` Circuit Elimination (`K ≤ 47467` ruled out):**
every non-trivial `m`-circuit cycle with `cs.length ≤ 19` satisfies
`47468 ≤ mCircuitK cs`, `75235 ≤ mCircuitS cs`, and `122703 ≤ mCircuitK cs + mCircuitS cs`. -/
theorem mCircuit_unconditional_bounds_le_19 {cs : List (Nat × Nat)} {n : Nat}
    (hm : cs.length ≤ 19) (h : IsMCircuitCycle cs n) :
    47468 ≤ mCircuitK cs ∧ 75235 ≤ mCircuitS cs ∧ 122703 ≤ mCircuitK cs + mCircuitS cs := by
  have h64 := (mCircuit_unconditional_bounds_le_64 (by omega) h).1
  have hk := mCircuit_cf_elimination_bernoulli (M := 1048576) (m := cs.length)
    (pL := 50508) (qL := 31867) (pU := 24727) (qU := 15601) (K₀ := 15601) (a := 1) (d := 54961)
    (by decide) (by decide) (by decide) mCircuit_1m_lower_halving_witness.1
    log2ThreeCFExt2_semi_dets.1 (by decide) mCircuit_1m_gap_witness_main.2.2.2.2.1 (by omega)
    rfl h (mCircuit_orbit_ge_1048576 h) h64
  have hk' : 47468 ≤ mCircuitK cs := Nat.le_trans (by decide : 47468 ≤ 15601 + 31867) hk
  have hS := lifted_halving_ge_of_k h.pow_lt hk' mCircuit_1m_lower_halving_witness.2.2.2.2.2.1
  exact ⟨hk', hS, by omega⟩

/-- **Unconditional `m ≤ 16` Circuit Elimination (`K ≤ 47467` ruled out).** -/
theorem mCircuit_unconditional_bounds_le_16 {cs : List (Nat × Nat)} {n : Nat}
    (hm : cs.length ≤ 16) (h : IsMCircuitCycle cs n) :
    47468 ≤ mCircuitK cs ∧ 75235 ≤ mCircuitS cs ∧ 122703 ≤ mCircuitK cs + mCircuitS cs :=
  mCircuit_unconditional_bounds_le_19 (by omega) h

/-- **Unconditional `m ≤ 11` Circuit Elimination (`K ≤ 79334` ruled out):**
every non-trivial `m`-circuit cycle with `cs.length ≤ 11` (covering ALL `m = 4, 5, 6, ..., 11`)
satisfies `79335 ≤ mCircuitK cs`, `125743 ≤ mCircuitS cs`, and
`205078 ≤ mCircuitK cs + mCircuitS cs`. -/
theorem mCircuit_unconditional_bounds_le_11 {cs : List (Nat × Nat)} {n : Nat}
    (hm : cs.length ≤ 11) (h : IsMCircuitCycle cs n) :
    79335 ≤ mCircuitK cs ∧ 125743 ≤ mCircuitS cs ∧ 205078 ≤ mCircuitK cs + mCircuitS cs := by
  have h19 := (mCircuit_unconditional_bounds_le_19 (by omega) h).1
  have hk := mCircuit_cf_elimination_bernoulli (M := 1048576) (m := cs.length)
    (pL := 50508) (qL := 31867) (pU := 75235) (qU := 47468) (K₀ := 47468) (a := 1) (d := 91494)
    (by decide) (by decide) (by decide) mCircuit_1m_lower_halving_witness.1
    log2ThreeCFExt2_semi_dets.2.1 (by decide) mCircuit_1m_gap_witness_main.2.2.2.2.2.1 (by omega)
    rfl h (mCircuit_orbit_ge_1048576 h) h19
  have hk' : 79335 ≤ mCircuitK cs := Nat.le_trans (by decide : 79335 ≤ 47468 + 31867) hk
  have hS := lifted_halving_ge_of_k h.pow_lt hk' mCircuit_1m_lower_halving_witness.2.2.2.2.2.2.1
  exact ⟨hk', hS, by omega⟩

/-! ### 4. Flagship `3`-, `4`-, `5`-, `6`-Circuit Bounds & Frozen `Challenge` Bridges -/

/-- **Flagship Unconditional 3-Circuit Bounds (`190537 ≤ K`, `12.75x` leap over `14936`):**
every non-trivial positive 3-circuit cycle satisfies `190537 ≤ k₁ + k₂ + k₃`,
`301994 ≤ k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3`, and `492531 ≤ K + S`. -/
theorem threeCircuit_unconditional_bounds_lifted {n k₁ e₁ k₂ e₂ k₃ e₃ : Nat}
    (h : IsThreeCircuitCycle n k₁ e₁ k₂ e₂ k₃ e₃) :
    190537 ≤ k₁ + k₂ + k₃ ∧ 301994 ≤ k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3 ∧
      492531 ≤ (k₁ + k₂ + k₃) + (k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3) := by
  have hm := isThreeCircuitCycle_iff_isMCircuitCycle.mp h
  have h11 := (mCircuit_unconditional_bounds_le_11 (by simp) hm).1
  have hk := mCircuit_cf_elimination_bernoulli (M := 1048576) (m := 3)
    (pL := 176251) (qL := 111202) (pU := 125743) (qU := 79335) (K₀ := 79335) (a := 1) (d := 272872)
    (by decide) (by decide) (by decide) mCircuit_1m_lower_halving_witness.2.1
    log2ThreeCFExt2_semi_dets.2.2 (by decide) mCircuit_1m_gap_witness_main.2.2.2.2.2.2
    (by decide) rfl hm (mCircuit_orbit_ge_1048576 hm) h11
  have hKeq : mCircuitK [(k₁, e₁), (k₂, e₂), (k₃, e₃)] = k₁ + k₂ + k₃ := by
    simp only [mCircuitK, List.map, List.sum_cons, List.sum_nil]; omega
  rw [hKeq] at hk
  have hk' : 190537 ≤ k₁ + k₂ + k₃ := Nat.le_trans (by decide : 190537 ≤ 79335 + 111202) hk
  have hS := lifted_halving_ge_of_k hm.pow_lt (by rwa [hKeq])
    mCircuit_1m_lower_halving_witness.2.2.2.2.2.2.2
  have hSeq : mCircuitS [(k₁, e₁), (k₂, e₂), (k₃, e₃)] = k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3 := by
    have hk₁ := h.k₁_pos; have hk₂ := h.k₂_pos; have hk₃ := h.k₃_pos
    simp only [mCircuitS]; omega
  rw [hSeq] at hS
  exact ⟨hk', hS, by omega⟩

/-- **Flagship Unconditional 3-Circuit Elimination (`K ≤ 190536`, zero `native_decide`).** -/
theorem no_nontrivial_threeCircuit_le_190536 :
    ∀ n k₁ e₁ k₂ e₂ k₃ e₃ : Nat, k₁ + k₂ + k₃ ≤ 190536 →
      ¬ IsThreeCircuitCycle n k₁ e₁ k₂ e₂ k₃ e₃ :=
  fun _ _ _ _ _ _ _ hle hcyc => by
    have hk := (threeCircuit_unconditional_bounds_lifted hcyc).1; omega

/-- **Flagship Unconditional 4-Circuit Bounds (`79335 ≤ K`, `5.55x` leap over `14271`).** -/
theorem fourCircuit_unconditional_bounds_lifted {cs : List (Nat × Nat)} {n : Nat}
    (hlen : cs.length = 4) (h : IsMCircuitCycle cs n) :
    79335 ≤ mCircuitK cs ∧ 125743 ≤ mCircuitS cs ∧ 205078 ≤ mCircuitK cs + mCircuitS cs :=
  mCircuit_unconditional_bounds_le_11 (by omega) h

/-- **Flagship Unconditional 4-Circuit Elimination (`K ≤ 79334`).** -/
theorem no_nontrivial_fourCircuit_le_79334 :
    ∀ cs : List (Nat × Nat), ∀ n : Nat,
      cs.length = 4 → mCircuitK cs ≤ 79334 → ¬ IsMCircuitCycle cs n :=
  fun _ _ hlen hle hcyc => by
    have hk := (fourCircuit_unconditional_bounds_lifted hlen hcyc).1; omega

/-- **Flagship Unconditional 5-Circuit Bounds (`79335 ≤ K`, `5.83x` leap over `13606`).** -/
theorem fiveCircuit_unconditional_bounds_lifted {cs : List (Nat × Nat)} {n : Nat}
    (hlen : cs.length = 5) (h : IsMCircuitCycle cs n) :
    79335 ≤ mCircuitK cs ∧ 125743 ≤ mCircuitS cs ∧ 205078 ≤ mCircuitK cs + mCircuitS cs :=
  mCircuit_unconditional_bounds_le_11 (by omega) h

/-- **Flagship Unconditional 5-Circuit Elimination (`K ≤ 79334`).** -/
theorem no_nontrivial_fiveCircuit_le_79334 :
    ∀ cs : List (Nat × Nat), ∀ n : Nat,
      cs.length = 5 → mCircuitK cs ≤ 79334 → ¬ IsMCircuitCycle cs n :=
  fun _ _ hlen hle hcyc => by
    have hk := (fiveCircuit_unconditional_bounds_lifted hlen hcyc).1; omega

/-- **Flagship Unconditional 6-Circuit Bounds (`79335 ≤ K`, `2,479x` over `REF-011` `K ≤ 32`).** -/
theorem sixCircuit_unconditional_bounds_lifted {cs : List (Nat × Nat)} {n : Nat}
    (hlen : cs.length = 6) (h : IsMCircuitCycle cs n) :
    79335 ≤ mCircuitK cs ∧ 125743 ≤ mCircuitS cs ∧ 205078 ≤ mCircuitK cs + mCircuitS cs :=
  mCircuit_unconditional_bounds_le_11 (by omega) h

/-- **Flagship Unconditional 6-Circuit Elimination (`K ≤ 79334`).** -/
theorem no_nontrivial_sixCircuit_le_79334 :
    ∀ cs : List (Nat × Nat), ∀ n : Nat,
      cs.length = 6 → mCircuitK cs ≤ 79334 → ¬ IsMCircuitCycle cs n :=
  fun _ _ hlen hle hcyc => by
    have hk := (sixCircuit_unconditional_bounds_lifted hlen hcyc).1; omega

private theorem mCircuit_challenge_bridge {cs : List (Nat × Nat)} {n K₀ S₀ L₀ : Nat}
    (h : IsMCircuitCycle cs n)
    (hbd : K₀ ≤ mCircuitK cs ∧ S₀ ≤ mCircuitS cs ∧ L₀ ≤ mCircuitK cs + mCircuitS cs) :
    let K := mCircuitK cs; let S := mCircuitS cs
    HasNontrivialCycle ∧ collatzIter (K + S) n = n ∧
    (∀ j : Nat, j < K + S → collatzIter j n ≠ 1) ∧
    1048576 ≤ n ∧ K₀ ≤ K ∧ S₀ ≤ S ∧ L₀ ≤ K + S := by
  intro K S
  have hodd := h.odd; have htot := h.totalVal_eq
  have hne_syr : ∀ i : Nat, i < K → syracuseIter i n ≠ 1 := fun i _ h1 => by
    have h3 := (mCircuit_valley_three_le h i).2; omega
  have hcol : collatzIter (K + S) n = n := by
    dsimp only [K, S]; rw [Nat.add_comm, ← htot, collatzIter_eq_syracuseIter _ hodd, h.period_eq]
  have havoid : ∀ j : Nat, j < K + S → collatzIter j n ≠ 1 := fun j hj => by
    dsimp only [K, S] at hj; rw [Nat.add_comm, ← htot] at hj
    exact collatzIter_ne_one_of_syracuseIter _ hodd hne_syr j hj
  have h1m := mCircuit_orbit_ge_1048576 h 0
  simp only [syracuseIter] at h1m
  exact ⟨h.hasNontrivialCycle, hcol, havoid, h1m, hbd.1, hbd.2.1, hbd.2.2⟩

/-- **Bridge to Frozen `Challenge.lean` for 3-Circuits (`1048576 ≤ n`, `190537 ≤ K`).** -/
theorem threeCircuit_challenge_bounds {n k₁ e₁ k₂ e₂ k₃ e₃ : Nat}
    (h : IsThreeCircuitCycle n k₁ e₁ k₂ e₂ k₃ e₃) :
    let K := k₁ + k₂ + k₃; let S := k₁ + k₂ + k₃ + e₁ + e₂ + e₃ - 3
    HasNontrivialCycle ∧ collatzIter (K + S) n = n ∧
    (∀ j : Nat, j < K + S → collatzIter j n ≠ 1) ∧
    1048576 ≤ n ∧ 190537 ≤ K ∧ 301994 ≤ S ∧ 492531 ≤ K + S := by
  intro K S
  have hm := isThreeCircuitCycle_iff_isMCircuitCycle.mp h
  have hKeq : mCircuitK [(k₁, e₁), (k₂, e₂), (k₃, e₃)] = K := by
    simp only [K, mCircuitK, List.map, List.sum_cons, List.sum_nil]; omega
  have hSeq : mCircuitS [(k₁, e₁), (k₂, e₂), (k₃, e₃)] = S := by
    have hk₁ := h.k₁_pos; have hk₂ := h.k₂_pos; have hk₃ := h.k₃_pos
    simp only [S, mCircuitS]; omega
  have hb := mCircuit_challenge_bridge hm
    (by rw [hKeq, hSeq]; exact threeCircuit_unconditional_bounds_lifted h)
  simpa only [hKeq, hSeq] using hb

/-- **Bridge to Frozen `Challenge.lean` for 4-Circuits (`1048576 ≤ n`, `79335 ≤ K`).** -/
theorem fourCircuit_challenge_bounds {cs : List (Nat × Nat)} {n : Nat}
    (hlen : cs.length = 4) (h : IsMCircuitCycle cs n) :
    let K := mCircuitK cs; let S := mCircuitS cs
    HasNontrivialCycle ∧ collatzIter (K + S) n = n ∧
    (∀ j : Nat, j < K + S → collatzIter j n ≠ 1) ∧
    1048576 ≤ n ∧ 79335 ≤ K ∧ 125743 ≤ S ∧ 205078 ≤ K + S :=
  mCircuit_challenge_bridge h (fourCircuit_unconditional_bounds_lifted hlen h)

/-- **Bridge to Frozen `Challenge.lean` for 5-Circuits (`1048576 ≤ n`, `79335 ≤ K`).** -/
theorem fiveCircuit_challenge_bounds {cs : List (Nat × Nat)} {n : Nat}
    (hlen : cs.length = 5) (h : IsMCircuitCycle cs n) :
    let K := mCircuitK cs; let S := mCircuitS cs
    HasNontrivialCycle ∧ collatzIter (K + S) n = n ∧
    (∀ j : Nat, j < K + S → collatzIter j n ≠ 1) ∧
    1048576 ≤ n ∧ 79335 ≤ K ∧ 125743 ≤ S ∧ 205078 ≤ K + S :=
  mCircuit_challenge_bridge h (fiveCircuit_unconditional_bounds_lifted hlen h)

/-- **Bridge to Frozen `Challenge.lean` for 6-Circuits (`1048576 ≤ n`, `79335 ≤ K`).** -/
theorem sixCircuit_challenge_bounds {cs : List (Nat × Nat)} {n : Nat}
    (hlen : cs.length = 6) (h : IsMCircuitCycle cs n) :
    let K := mCircuitK cs; let S := mCircuitS cs
    HasNontrivialCycle ∧ collatzIter (K + S) n = n ∧
    (∀ j : Nat, j < K + S → collatzIter j n ≠ 1) ∧
    1048576 ≤ n ∧ 79335 ≤ K ∧ 125743 ≤ S ∧ 205078 ≤ K + S :=
  mCircuit_challenge_bridge h (sixCircuit_unconditional_bounds_lifted hlen h)

/-- **Bridge to Frozen `Challenge.lean` for ALL `m ≤ 64`-Circuits (`1048576 ≤ n`, `15601 ≤ K`).** -/
theorem mCircuit_challenge_bounds_le_64 {cs : List (Nat × Nat)} {n : Nat}
    (hm : cs.length ≤ 64) (h : IsMCircuitCycle cs n) :
    let K := mCircuitK cs; let S := mCircuitS cs
    HasNontrivialCycle ∧ collatzIter (K + S) n = n ∧
    (∀ j : Nat, j < K + S → collatzIter j n ≠ 1) ∧
    1048576 ≤ n ∧ 15601 ≤ K ∧ 24727 ≤ S ∧ 40328 ≤ K + S :=
  mCircuit_challenge_bridge h (mCircuit_unconditional_bounds_le_64 hm h)

/-! ### 5. Explicit Barrier 1–5 Separations -/

/-- **Barrier 1 Separation (`3n - 1` on `ℕ⁺`):** `n = 5` (`K = 2`) and 2-circuit `n = 17` (`K = 7`)
form positive periodic orbits below `1048576` and `79334` / `190536`, violating `3^K < 2^S`. -/
theorem barrier1_mCircuit_lifted_three_n_minus_one :
    (Barriers.genIter 3 (-1) 5 5 = 5 ∧ 5 < 1048576 ∧ 2 ≤ 190536 ∧ ¬ (3 ^ 2 < 2 ^ 3)) ∧
    (Barriers.genIter 3 (-1) 18 17 = 17 ∧
      (3 ^ mCircuitK [(4, 2), (3, 4)] - 2 ^ mCircuitS [(4, 2), (3, 4)]) * 17 =
        mCircuitOffset [(4, 2), (3, 4)] ∧
      17 < 1048576 ∧ 7 ≤ 79334 ∧ ¬ (3 ^ 7 < 2 ^ 11)) :=
  ⟨⟨Barriers.three_n_minus_one_cycle_5.1, by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide, by decide, by decide⟩⟩

/-- **Barrier 2 Separation (`5n + 1` on `ℕ⁺`):** `n = 1` (`K = 2`) and `n = 13` (`K = 3, S = 7`)
satisfy `5^K < 2^S` yet violate the `3n + 1` valley bound `1048576 ≤ n` and Simons bands. -/
theorem barrier2_mCircuit_lifted_five_n_plus_one :
    (Barriers.genIter 5 1 7 1 = 1 ∧ 1 < 1048576 ∧ 2 ≤ 190536 ∧
      5 ^ 2 < 2 ^ 5 ∧ ¬ (9 * 2 ^ 5 < 16 * 3 ^ 2)) ∧
    (Barriers.genIter 5 1 10 13 = 13 ∧ (∀ j : Nat, j < 10 → Barriers.genIter 5 1 j 13 ≠ 1) ∧
      13 < 1048576 ∧ 3 ≤ 190536 ∧ 5 ^ 3 < 2 ^ 7 ∧ ¬ (27 * 2 ^ 7 < 64 * 3 ^ 3)) :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide⟩,
    ⟨Barriers.five_n_plus_one_cycle_13.1, Barriers.five_n_plus_one_cycle_13.2,
      by decide, by decide, by decide, by decide⟩⟩

/-- **Barrier 3 Separation (`3n + 1` on `ℤ_{<0}`):** `n = -5` (`K = 2`) and `-17` (`K = 7`)
form negative `3n + 1` cycles escaping archimedean positivity `1048576 ≤ n` and `3^K < 2^S`. -/
theorem barrier3_mCircuit_lifted_neg_int :
    (Barriers.genIter 3 1 5 (-5) = -5 ∧ 2 ≤ 190536 ∧ ¬ (3 ^ 2 < 2 ^ 3)) ∧
    (Barriers.genIter 3 1 18 (-17) = -17 ∧
      ((2 : Int) ^ 11 - (3 : Int) ^ 7) * (-17) = (mCircuitOffset [(4, 2), (3, 4)] : Int) ∧
      7 ≤ 79334 ∧ ¬ (3 ^ 7 < 2 ^ 11)) :=
  ⟨⟨Barriers.neg_int_cycle_neg5.1, by decide, by decide⟩,
    ⟨by decide, by decide, by decide, by decide⟩⟩

/-- **Barrier 4 Separation (`ℤ₂` rational `m`-circuits):** `143 / 47` (`m = 3, K = 4 < 190537`)
and `1927 / 295` (`m = 4, K = 6 < 79335`) satisfy `3^K < 2^S` and the Simons-de Weger bands in
`ℤ_(2) \ ℤ` yet escape global integrality in `ℕ⁺`. -/
theorem barrier4_mCircuit_lifted_twoAdic :
    let x3 := periodicPoint (threeCircuitVec 1 2 1 2 2 2) (by decide)
    let x4 := periodicPoint (mCircuitVec [(1, 2), (1, 2), (2, 2), (2, 2)]) (by decide)
    (x3 = ⟨143, 47, by decide⟩ ∧ 4 ≤ 190536 ∧ 3 ^ 4 < 2 ^ 7 ∧ 27 * 2 ^ 7 < 64 * 3 ^ 4 ∧
      OddDenomRat.syracuseIter 4 x3 = x3 ∧ (¬ ∃ m : Int, x3.Equiv (OddDenomRat.ofInt m))) ∧
    (x4 = ⟨1927, 295, by decide⟩ ∧ 6 ≤ 79334 ∧ 3 ^ 6 < 2 ^ 10 ∧ 81 * 2 ^ 10 < 256 * 3 ^ 6 ∧
      OddDenomRat.syracuseIter 6 x4 = x4 ∧ (¬ ∃ m : Int, x4.Equiv (OddDenomRat.ofInt m))) :=
  ⟨⟨barrier4_twoAdic_threeCircuit_separation.2.2.1, by decide, by decide, by decide,
      barrier4_twoAdic_threeCircuit_separation.2.2.2.1,
      barrier4_twoAdic_threeCircuit_separation.2.2.2.2.2⟩,
    ⟨barrier4_mCircuit_twoAdic.2.2.1, by decide, by decide, by decide,
      barrier4_mCircuit_twoAdic.2.2.2.1, barrier4_mCircuit_twoAdic.2.2.2.2.2⟩⟩

/-- **Barrier 5 Separation (Conway 1972 / Finite Verification Horizon vs Global Baker):**
`M = 2^20` unconditionally eliminates `3`-circuits (`K ≤ 190536`), `m ≤ 11`-circuits (`K ≤ 79334`),
`m ≤ 19`-circuits (`K ≤ 47467`), `m ≤ 64`-circuits (`K ≤ 15600`), and `m ≤ 500`-circuits
(`K ≤ 8950`), while further lifting to `K ≤ 64497106` or global `m ≤ 68` elimination requires
deeper finite stopping-time verification (`2^40`, `2^68`) or global Baker bounds. -/
theorem barrier5_mCircuit_lifted_conway_horizon :
    (∀ n k₁ e₁ k₂ e₂ k₃ e₃ : Nat, k₁ + k₂ + k₃ ≤ 190536 →
      ¬ IsThreeCircuitCycle n k₁ e₁ k₂ e₂ k₃ e₃) ∧
    (∀ cs : List (Nat × Nat), ∀ n : Nat,
      cs.length ≤ 11 → mCircuitK cs ≤ 79334 → ¬ IsMCircuitCycle cs n) ∧
    (∀ cs : List (Nat × Nat), ∀ n : Nat,
      cs.length ≤ 64 → mCircuitK cs ≤ 15600 → ¬ IsMCircuitCycle cs n) ∧
    (∀ cs : List (Nat × Nat), ∀ n : Nat,
      cs.length ≤ 500 → mCircuitK cs ≤ 8950 → ¬ IsMCircuitCycle cs n) ∧
    ((∀ m : Nat, 2 ≤ m → m < 2 ^ 68 → HasFiniteStoppingTime m) →
      ∀ cs : List (Nat × Nat), ∀ n : Nat, cs.length ≤ 1000000 → IsMCircuitCycle cs n →
        64497107 ≤ mCircuitK cs) :=
  ⟨no_nontrivial_threeCircuit_le_190536,
    fun _ _ hm hle hcyc => by have hk := (mCircuit_unconditional_bounds_le_11 hm hcyc).1; omega,
    fun _ _ hm hle hcyc => by have hk := (mCircuit_unconditional_bounds_le_64 hm hcyc).1; omega,
    fun _ _ hm hle hcyc => by have hk := (mCircuit_unconditional_bounds_le_500 hm hcyc).1; omega,
    fun hstop _ _ hm hcyc => (mCircuit_bounds_of_stopping_pow2_68 hstop hm hcyc).1⟩

end SolveCollatz
