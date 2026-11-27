/-
Copyright (c) 2026 The solve-collatz contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Collatz.Prove.Diophantine.ThreeCircuit

/-!
# General `m`-Circuit Simons–de Weger (2005) Theory & 4-Circuit Elimination (`PROVE-B1`)

Formalization of the general `m`-circuit Diophantine theory for the Collatz (`3n + 1`) conjecture,
advancing Track A node `PROVE-B1` (Phase 3):
1. Arbitrary `m`-circuit parity vectors `mCircuitVec cs`, total odd steps `mCircuitK cs`, total
   halvings `mCircuitS cs`, recursive closed-form numerator `mCircuitOffset cs`, exact identity
   `parityOffset (mCircuitVec cs) = mCircuitOffset cs`, and consistency with `twoCircuitOffset`
   and `threeCircuitOffset`.
2. `IsMCircuitCycle cs n`, automatic valley lower bounds `3 ≤ syracuseIter i n` for all `i`,
   bridge to `HasNontrivialCycle` in frozen `Challenge.lean`, and exact cycle equation
   `(2 ^ mCircuitS cs - 3 ^ mCircuitK cs) * n = mCircuitOffset cs`.
3. Universal Simons–de Weger `m`-circuit band bound (proved by induction on `m = cs.length`):
   `3 ^ cs.length * 2 ^ mCircuitS cs < 4 ^ cs.length * 3 ^ mCircuitK cs`,
   with immediate corollaries for `m = 4` (`81 * 2^S < 256 * 3^K`), `m = 5`
   (`243 * 2^S < 1024 * 3^K`), and the general window `minHalvings K ≤ S < minHalvings K + m`.
4. Kernel-verified (`decide`, zero `native_decide`) elimination of ALL non-trivial positive
   4-circuit cycles for `k₁ + k₂ + k₃ + k₄ ≤ 12`.
5. Explicit separations against Barriers 1–5 (`3n - 1`, `5n + 1`, `ℤ_{<0}`, `ℤ₂` rational
   4-circuit `1927 / 295`, and Conway undecidability).
-/

@[expose] public section

namespace SolveCollatz

/-! ### 1. Elementary Multiplication Helpers -/

private theorem mul_four_rearrange_m (a b c d : Nat) :
    (a * b) * (c * d) = (a * c) * (b * d) := by
  rw [Nat.mul_assoc, Nat.mul_left_comm b c d, ← Nat.mul_assoc]

/-! ### 2. General `m`-Circuit Parity Vectors & Recursive Closed-Form Numerator -/

/-- Canonical `m`-circuit parity vector formed by concatenating `oneCircuitVec (k - 1) e` for
each `(k, e) ∈ cs`. -/
def mCircuitVec : List (Nat × Nat) → List Nat
  | [] => []
  | (k, e) :: rest => oneCircuitVec (k - 1) e ++ mCircuitVec rest

/-- Total number of odd Syracuse steps `K = ∑ k_j` across an `m`-circuit parameter list `cs`. -/
def mCircuitK (cs : List (Nat × Nat)) : Nat :=
  (cs.map Prod.fst).sum

/-- Total number of halvings `S = ∑ (k_j + e_j - 1)` across an `m`-circuit parameter list `cs`. -/
def mCircuitS : List (Nat × Nat) → Nat
  | [] => 0
  | (k, e) :: rest => (k + e - 1) + mCircuitS rest

/-- Recursive closed-form Simons–de Weger `m`-circuit numerator `C(cs)`. -/
def mCircuitOffset : List (Nat × Nat) → Nat
  | [] => 0
  | (k, e) :: rest =>
    3 ^ mCircuitK rest * (3 ^ k - 2 ^ k) + 2 ^ (k + e - 1) * mCircuitOffset rest

/-- Unfolding lemma for `mCircuitK` on empty lists. -/
@[simp] theorem mCircuitK_nil : mCircuitK [] = 0 := rfl

/-- Unfolding lemma for `mCircuitK` on cons cells. -/
@[simp] theorem mCircuitK_cons (k e : Nat) (rest : List (Nat × Nat)) :
    mCircuitK ((k, e) :: rest) = k + mCircuitK rest := rfl

/-- Additivity of `mCircuitK` under list append. -/
theorem mCircuitK_append (cs₁ cs₂ : List (Nat × Nat)) :
    mCircuitK (cs₁ ++ cs₂) = mCircuitK cs₁ + mCircuitK cs₂ := by
  induction cs₁ with
  | nil => simp
  | cons p rest ih =>
    rcases p with ⟨k, e⟩
    simp [mCircuitK_cons, ih, Nat.add_assoc]

/-- Total length of `mCircuitVec cs` equals `mCircuitK cs` whenever every `k ≥ 1`. -/
theorem mCircuitVec_length {cs : List (Nat × Nat)} (hpos : ∀ p ∈ cs, 1 ≤ p.1) :
    (mCircuitVec cs).length = mCircuitK cs := by
  induction cs with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨k, e⟩
    have hk : 1 ≤ k := hpos (k, e) (by simp)
    have hrest : ∀ q ∈ rest, 1 ≤ q.1 := fun q hq => hpos q (by simp [hq])
    simp only [mCircuitVec, List.length_append, oneCircuitVec_length, ih hrest, mCircuitK_cons]
    omega

/-- Total halving sum of `mCircuitVec cs` equals `mCircuitS cs` whenever every `k ≥ 1`. -/
theorem paritySum_mCircuitVec {cs : List (Nat × Nat)} (hpos : ∀ p ∈ cs, 1 ≤ p.1) :
    paritySum (mCircuitVec cs) = mCircuitS cs := by
  induction cs with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨k, e⟩
    have hk : 1 ≤ k := hpos (k, e) (by simp)
    have hrest : ∀ q ∈ rest, 1 ≤ q.1 := fun q hq => hpos q (by simp [hq])
    simp only [mCircuitVec, paritySum_append, paritySum_oneCircuitVec, ih hrest, mCircuitS]
    omega

/-- Every non-empty `m`-circuit vector with positive `(k, e)` parameters is a valid parity
vector. -/
theorem mCircuitVec_valid {cs : List (Nat × Nat)} (hne : cs ≠ [])
    (hpos : ∀ p ∈ cs, 1 ≤ p.1 ∧ 1 ≤ p.2) :
    IsValidParityVec (mCircuitVec cs) := by
  refine ⟨?_, ?_⟩
  · intro hnil
    have hlen := mCircuitVec_length (fun p hp => (hpos p hp).1)
    rw [hnil] at hlen
    cases cs with
    | nil => exact hne rfl
    | cons p rest =>
      rcases p with ⟨k, e⟩
      have hk := (hpos (k, e) (by simp)).1
      simp only [List.length_nil, mCircuitK_cons] at hlen
      omega
  · intro a ha
    induction cs with
    | nil => contradiction
    | cons p rest ih =>
      rcases p with ⟨k, e⟩
      simp only [mCircuitVec, List.mem_append, oneCircuitVec, List.mem_replicate,
        List.mem_singleton] at ha
      rcases ha with (⟨_, rfl⟩ | heq) | hmem
      · omega
      · subst heq; exact (hpos (k, a) (by simp)).2
      · exact ih (by intro hnil; subst hnil; simp [mCircuitVec] at hmem)
          (fun q hq => hpos q (by simp [hq])) hmem

/-- **General Exact `m`-Circuit Offset Identity:**
`parityOffset (mCircuitVec cs) = mCircuitOffset cs` for all `cs` with `1 ≤ k` per block. -/
theorem parityOffset_mCircuitVec {cs : List (Nat × Nat)} (hpos : ∀ p ∈ cs, 1 ≤ p.1) :
    parityOffset (mCircuitVec cs) = mCircuitOffset cs := by
  induction cs with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨k, e⟩
    have hk : 1 ≤ k := hpos (k, e) (by simp)
    have hrest : ∀ q ∈ rest, 1 ≤ q.1 := fun q hq => hpos q (by simp [hq])
    have hk1 : k - 1 + 1 = k := by omega
    have hsum : k - 1 + e = k + e - 1 := by omega
    rw [mCircuitVec, parityOffset_append, mCircuitVec_length hrest,
      parityOffset_oneCircuitVec, paritySum_oneCircuitVec, ih hrest, hk1, hsum, mCircuitOffset]

/-- Consistency of `mCircuitVec` with `twoCircuitVec` at length `2`. -/
theorem mCircuitVec_two (k₁ e₁ k₂ e₂ : Nat) :
    mCircuitVec [(k₁, e₁), (k₂, e₂)] = twoCircuitVec k₁ e₁ k₂ e₂ := by
  simp [mCircuitVec, twoCircuitVec]

/-- Consistency of `mCircuitOffset` with `twoCircuitOffset` at length `2`. -/
theorem mCircuitOffset_two (k₁ e₁ k₂ e₂ : Nat) :
    mCircuitOffset [(k₁, e₁), (k₂, e₂)] = twoCircuitOffset k₁ e₁ k₂ e₂ := by
  simp [mCircuitOffset, twoCircuitOffset, mCircuitK]

/-- Consistency of `mCircuitVec` with `threeCircuitVec` at length `3`. -/
theorem mCircuitVec_three (k₁ e₁ k₂ e₂ k₃ e₃ : Nat) :
    mCircuitVec [(k₁, e₁), (k₂, e₂), (k₃, e₃)] = threeCircuitVec k₁ e₁ k₂ e₂ k₃ e₃ := by
  simp [mCircuitVec, threeCircuitVec, List.append_assoc]

/-- Consistency of `mCircuitOffset` with `threeCircuitOffset` at length `3`. -/
theorem mCircuitOffset_three {k₁ e₁ k₂ e₂ k₃ e₃ : Nat} (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) :
    mCircuitOffset [(k₁, e₁), (k₂, e₂), (k₃, e₃)] =
      threeCircuitOffset k₁ e₁ k₂ e₂ k₃ e₃ := by
  have hsum : (k₁ + e₁ - 1) + (k₂ + e₂ - 1) = k₁ + k₂ + e₁ + e₂ - 2 := by omega
  simp only [mCircuitOffset, threeCircuitOffset, mCircuitK, List.map, List.sum_cons,
    List.sum_nil, Nat.add_zero, Nat.pow_zero, Nat.one_mul, Nat.mul_zero,
    Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_add, hsum]
  omega

/-! ### 3. `IsMCircuitCycle`, Valley Lower Bounds, & Bridge to `Challenge.lean` -/

/-- A non-trivial positive `m`-circuit Syracuse cycle starting at `n > 1` with non-empty canonical
circuit parameter list `cs` (`k ≥ 1`, `e ≥ 2` for every `(k, e) ∈ cs`). -/
structure IsMCircuitCycle (cs : List (Nat × Nat)) (n : Nat) : Prop where
  /-- Non-triviality (`n > 1`, excluding the `{1, 4, 2}` fixed cycle). -/
  one_lt_n : 1 < n
  /-- At least one 1-circuit block (`cs ≠ []`). -/
  cs_nonempty : cs ≠ []
  /-- Every circuit `(k, e) ∈ cs` is canonical (`1 ≤ k` and `2 ≤ e`). -/
  canonical : ∀ p ∈ cs, 1 ≤ p.1 ∧ 2 ≤ p.2
  /-- Periodicity under `mCircuitK cs` accelerated Syracuse steps. -/
  period_eq : syracuseIter (mCircuitK cs) n = n
  /-- Exact `m`-circuit halving-exponent vector along the period. -/
  valVec_eq : syracuseValVec (mCircuitK cs) n = mCircuitVec cs

/-- Every `IsMCircuitCycle` has strictly positive total odd step count `0 < mCircuitK cs`. -/
theorem IsMCircuitCycle.mCircuitK_pos {cs : List (Nat × Nat)} {n : Nat}
    (h : IsMCircuitCycle cs n) : 0 < mCircuitK cs := by
  cases cs with
  | nil => exact absurd rfl h.cs_nonempty
  | cons p rest =>
    rcases p with ⟨k, e⟩
    have hk := (h.canonical (k, e) (by simp)).1
    simp only [mCircuitK_cons]
    omega

/-- Every `m`-circuit cycle starting point `n` is odd. -/
theorem IsMCircuitCycle.odd {cs : List (Nat × Nat)} {n : Nat}
    (h : IsMCircuitCycle cs n) : n % 2 = 1 := by
  rw [← h.period_eq]
  exact syracuseIter_odd h.mCircuitK_pos n

/-- Every non-trivial `m`-circuit cycle starting point satisfies `3 ≤ n`. -/
theorem IsMCircuitCycle.three_le_n {cs : List (Nat × Nat)} {n : Nat}
    (h : IsMCircuitCycle cs n) : 3 ≤ n := by
  have hodd := h.odd
  have hgt := h.one_lt_n
  omega

/-- Along an `m`-circuit cycle, total halving count equals `mCircuitS cs`. -/
theorem IsMCircuitCycle.totalVal_eq {cs : List (Nat × Nat)} {n : Nat}
    (h : IsMCircuitCycle cs n) :
    syracuseTotalVal (mCircuitK cs) n = mCircuitS cs := by
  rw [← paritySum_syracuseValVec, h.valVec_eq]
  exact paritySum_mCircuitVec (fun p hp => (h.canonical p hp).1)

/-- Along an `m`-circuit cycle, the affine numerator equals `mCircuitOffset cs`. -/
theorem IsMCircuitCycle.offset_eq {cs : List (Nat × Nat)} {n : Nat}
    (h : IsMCircuitCycle cs n) :
    syracuseOffset (mCircuitK cs) n = mCircuitOffset cs := by
  rw [← parityOffset_syracuseValVec, h.valVec_eq]
  exact parityOffset_mCircuitVec (fun p hp => (h.canonical p hp).1)

/-- Archimedean positivity inequality for `m`-circuits: `3 ^ mCircuitK cs < 2 ^ mCircuitS cs`. -/
theorem IsMCircuitCycle.pow_lt {cs : List (Nat × Nat)} {n : Nat}
    (h : IsMCircuitCycle cs n) :
    3 ^ mCircuitK cs < 2 ^ mCircuitS cs := by
  have hlt := syracuse_cycle_pow_lt h.mCircuitK_pos h.period_eq
  rwa [h.totalVal_eq] at hlt

/-- **Bridge to Frozen `Challenge.lean`:** any `IsMCircuitCycle` witness yields
`HasNontrivialCycle` (and hence `CollatzDisproof`). -/
theorem IsMCircuitCycle.hasNontrivialCycle {cs : List (Nat × Nat)} {n : Nat}
    (h : IsMCircuitCycle cs n) : HasNontrivialCycle := by
  refine hasNontrivialCycle_of_syracuse_cycle h.mCircuitK_pos h.period_eq ?_
  intro i hi h1
  have hreach : syracuseIter (mCircuitK cs) n = 1 := by
    calc syracuseIter (mCircuitK cs) n
        = syracuseIter (i + (mCircuitK cs - i)) n := by
            rw [Nat.add_sub_of_le (Nat.le_of_lt hi)]
      _ = syracuseIter (mCircuitK cs - i) (syracuseIter i n) := (syracuseIter_add i _ n).symm
      _ = syracuseIter (mCircuitK cs - i) 1 := by rw [h1]
      _ = 1 := syracuseIter_one _
  rw [h.period_eq] at hreach
  have hgt := h.one_lt_n
  omega

/-- **Exact `m`-Circuit Diophantine Cycle Equation (Simons–de Weger 2005):**
`(2 ^ mCircuitS cs - 3 ^ mCircuitK cs) * n = mCircuitOffset cs`. -/
theorem mCircuit_cycle_eq {cs : List (Nat × Nat)} {n : Nat}
    (h : IsMCircuitCycle cs n) :
    (2 ^ mCircuitS cs - 3 ^ mCircuitK cs) * n = mCircuitOffset cs := by
  have heq := syracuse_cycle_equation h.period_eq
  rw [h.totalVal_eq, h.offset_eq] at heq
  exact heq

/-- **Divisibility Condition (certifying `mcircuit_hunter.c`):**
every `m`-circuit cycle satisfies `(2 ^ S - 3 ^ K) ∣ mCircuitOffset cs`. -/
theorem mCircuit_cycle_dvd {cs : List (Nat × Nat)} {n : Nat}
    (h : IsMCircuitCycle cs n) :
    (2 ^ mCircuitS cs - 3 ^ mCircuitK cs) ∣ mCircuitOffset cs :=
  ⟨n, (mCircuit_cycle_eq h).symm⟩

/-- For any non-trivial `m`-circuit cycle (`3 ≤ n`), `3 * (2 ^ S - 3 ^ K) ≤ mCircuitOffset cs`. -/
theorem mCircuit_three_mul_denom_le {cs : List (Nat × Nat)} {n : Nat}
    (h : IsMCircuitCycle cs n) :
    3 * (2 ^ mCircuitS cs - 3 ^ mCircuitK cs) ≤ mCircuitOffset cs := by
  have heq := mCircuit_cycle_eq h
  have hn3 := h.three_le_n
  have hmul : 3 * (2 ^ mCircuitS cs - 3 ^ mCircuitK cs) ≤
      (2 ^ mCircuitS cs - 3 ^ mCircuitK cs) * n := by
    rw [Nat.mul_comm 3]
    exact Nat.mul_le_mul_left _ hn3
  exact Nat.le_trans hmul (Nat.le_of_eq heq)

private theorem syracuseIter_mul_period {K n : Nat} (hper : syracuseIter K n = n) :
    ∀ q : Nat, syracuseIter (q * K) n = n := by
  intro q
  induction q with
  | zero => simp [syracuseIter]
  | succ q ih =>
    rw [Nat.succ_mul, ← syracuseIter_add, ih, hper]

/-- Every iterate along a non-trivial Syracuse cycle (`0 < K`, `1 < n`) is odd and satisfies
`3 ≤ syracuseIter i n` (in particular every intermediate circuit valley is `≥ 3`). -/
theorem syracuseIter_three_le_of_cycle {K n : Nat} (hK : 0 < K) (hn : 1 < n)
    (hper : syracuseIter K n = n) (i : Nat) :
    syracuseIter i n % 2 = 1 ∧ 3 ≤ syracuseIter i n := by
  have hnodd : n % 2 = 1 := by rw [← hper]; exact syracuseIter_odd hK n
  have hodd : syracuseIter i n % 2 = 1 := syracuseIter_odd_of_odd i hnodd
  have hne1 : syracuseIter i n ≠ 1 := by
    intro hi1
    have hlt : i < (i + 1) * K := by
      have : i + 1 ≤ (i + 1) * K := Nat.le_mul_of_pos_right (i + 1) hK
      omega
    have hret : syracuseIter ((i + 1) * K) n = 1 := by
      calc syracuseIter ((i + 1) * K) n
          = syracuseIter (i + ((i + 1) * K - i)) n := by
              rw [Nat.add_sub_of_le (Nat.le_of_lt hlt)]
        _ = syracuseIter ((i + 1) * K - i) (syracuseIter i n) := (syracuseIter_add i _ n).symm
        _ = syracuseIter ((i + 1) * K - i) 1 := by rw [hi1]
        _ = 1 := syracuseIter_one _
    rw [syracuseIter_mul_period hper (i + 1)] at hret
    omega
  exact ⟨hodd, by omega⟩

/-- Automatic valley lower bound for `IsMCircuitCycle`: every intermediate valley at step
`i` (in particular `mCircuitK (cs.take j)`) is odd and satisfies `3 ≤ syracuseIter i n`. -/
theorem mCircuit_valley_three_le {cs : List (Nat × Nat)} {n : Nat}
    (h : IsMCircuitCycle cs n) (i : Nat) :
    syracuseIter i n % 2 = 1 ∧ 3 ≤ syracuseIter i n :=
  syracuseIter_three_le_of_cycle h.mCircuitK_pos h.one_lt_n h.period_eq i

/-- Compatibility bridge: `IsTwoCircuitCycle n k₁ e₁ k₂ e₂` is equivalent to
`IsMCircuitCycle [(k₁, e₁), (k₂, e₂)] n`. -/
theorem isTwoCircuitCycle_iff_isMCircuitCycle {n k₁ e₁ k₂ e₂ : Nat} :
    IsTwoCircuitCycle n k₁ e₁ k₂ e₂ ↔ IsMCircuitCycle [(k₁, e₁), (k₂, e₂)] n := by
  constructor
  · intro h
    refine ⟨h.one_lt_n, by simp, ?_, ?_, ?_⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨h.k₁_pos, h.two_le_e₁⟩
      · exact ⟨h.k₂_pos, h.two_le_e₂⟩
    · simpa [mCircuitK] using h.period_eq
    · simpa [mCircuitK, mCircuitVec_two] using h.valVec_eq
  · intro h
    have hk₁ := h.canonical (k₁, e₁) (by simp)
    have hk₂ := h.canonical (k₂, e₂) (by simp)
    exact ⟨h.one_lt_n, hk₁.1, hk₁.2, hk₂.1, hk₂.2,
      by simpa [mCircuitK] using h.period_eq,
      by simpa [mCircuitK, mCircuitVec_two] using h.valVec_eq⟩

/-- Compatibility bridge: `IsThreeCircuitCycle n k₁ e₁ k₂ e₂ k₃ e₃` is equivalent to
`IsMCircuitCycle [(k₁, e₁), (k₂, e₂), (k₃, e₃)] n`. -/
theorem isThreeCircuitCycle_iff_isMCircuitCycle {n k₁ e₁ k₂ e₂ k₃ e₃ : Nat} :
    IsThreeCircuitCycle n k₁ e₁ k₂ e₂ k₃ e₃ ↔
      IsMCircuitCycle [(k₁, e₁), (k₂, e₂), (k₃, e₃)] n := by
  constructor
  · intro h
    refine ⟨h.one_lt_n, by simp, ?_, ?_, ?_⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨h.k₁_pos, h.two_le_e₁⟩
      · exact ⟨h.k₂_pos, h.two_le_e₂⟩
      · exact ⟨h.k₃_pos, h.two_le_e₃⟩
    · simpa [mCircuitK, Nat.add_assoc] using h.period_eq
    · simpa [mCircuitK, Nat.add_assoc, mCircuitVec_three] using h.valVec_eq
  · intro h
    have hk₁ := h.canonical (k₁, e₁) (by simp)
    have hk₂ := h.canonical (k₂, e₂) (by simp)
    have hk₃ := h.canonical (k₃, e₃) (by simp)
    exact ⟨h.one_lt_n, hk₁.1, hk₁.2, hk₂.1, hk₂.2, hk₃.1, hk₃.2,
      by simpa [mCircuitK, Nat.add_assoc] using h.period_eq,
      by simpa [mCircuitK, Nat.add_assoc, mCircuitVec_three] using h.valVec_eq⟩

/-! ### 4. Universal Simons–de Weger `m`-Circuit Band Bound (`3^m * 2^S < 4^m * 3^K`) -/

private theorem oneCircuit_block_three_le {k e a : Nat} (hk : 1 ≤ k) (ha : 3 ≤ a)
    (hvec : syracuseValVec k a = oneCircuitVec (k - 1) e) :
    3 * 2 ^ (k + e - 1) * syracuseIter k a < 4 * 3 ^ k * a := by
  have haff := syracuse_affine_vec_eq k a
  rw [hvec, paritySum_oneCircuitVec, parityOffset_oneCircuitVec] at haff
  have hsub : k - 1 + e = k + e - 1 := by omega
  have hinc : k - 1 + 1 = k := by omega
  rw [hsub, hinc] at haff
  have h23 : 2 ^ k < 3 ^ k := two_pow_lt_three_pow hk
  have hlt : 2 ^ (k + e - 1) * syracuseIter k a < 3 ^ k * (a + 1) := by
    have := Nat.two_pow_pos k
    rw [haff, Nat.mul_add, Nat.mul_one]
    omega
  have h3a : 3 * (a + 1) ≤ 4 * a := by omega
  calc 3 * 2 ^ (k + e - 1) * syracuseIter k a
      = 3 * (2 ^ (k + e - 1) * syracuseIter k a) := by rw [Nat.mul_assoc]
    _ < 3 * (3 ^ k * (a + 1)) := (Nat.mul_lt_mul_left (by decide : 0 < 3)).mpr hlt
    _ = 3 ^ k * (3 * (a + 1)) := by rw [Nat.mul_left_comm]
    _ ≤ 3 ^ k * (4 * a) := Nat.mul_le_mul_left _ h3a
    _ = 4 * 3 ^ k * a := by rw [Nat.mul_left_comm, ← Nat.mul_assoc]

private theorem mCircuit_path_bound_step {k e : Nat} {rest : List (Nat × Nat)} {a : Nat}
    (hk : 1 ≤ k) (ha3 : 3 ≤ a) (hv1 : syracuseValVec k a = oneCircuitVec (k - 1) e)
    (hih : 3 ^ rest.length * 2 ^ mCircuitS rest *
        syracuseIter (mCircuitK rest) (syracuseIter k a) ≤
      4 ^ rest.length * 3 ^ mCircuitK rest * syracuseIter k a) :
    3 ^ ((k, e) :: rest).length * 2 ^ mCircuitS ((k, e) :: rest) *
      syracuseIter (mCircuitK ((k, e) :: rest)) a <
    4 ^ ((k, e) :: rest).length * 3 ^ mCircuitK ((k, e) :: rest) * a := by
  have hblk := oneCircuit_block_three_le hk ha3 hv1
  have hc_pos : 0 < 4 ^ rest.length * 3 ^ mCircuitK rest :=
    Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
  have hstrict :
      3 ^ (rest.length + 1) * 2 ^ ((k + e - 1) + mCircuitS rest) *
        syracuseIter (mCircuitK rest) (syracuseIter k a) <
      4 ^ (rest.length + 1) * 3 ^ (k + mCircuitK rest) * a := by
    calc 3 ^ (rest.length + 1) * 2 ^ ((k + e - 1) + mCircuitS rest) *
          syracuseIter (mCircuitK rest) (syracuseIter k a)
        = (3 * 2 ^ (k + e - 1)) *
            (3 ^ rest.length * 2 ^ mCircuitS rest *
              syracuseIter (mCircuitK rest) (syracuseIter k a)) := by
            rw [Nat.pow_succ, Nat.pow_add, Nat.mul_comm (3 ^ rest.length) 3,
              mul_four_rearrange_m, Nat.mul_assoc]
      _ ≤ (3 * 2 ^ (k + e - 1)) * (4 ^ rest.length * 3 ^ mCircuitK rest * syracuseIter k a) :=
            Nat.mul_le_mul_left _ hih
      _ = (4 ^ rest.length * 3 ^ mCircuitK rest) * (3 * 2 ^ (k + e - 1) * syracuseIter k a) := by
            rw [Nat.mul_left_comm (3 * 2 ^ (k + e - 1)) (4 ^ rest.length * 3 ^ mCircuitK rest)]
      _ < (4 ^ rest.length * 3 ^ mCircuitK rest) * (4 * 3 ^ k * a) :=
            (Nat.mul_lt_mul_left hc_pos).mpr hblk
      _ = 4 ^ (rest.length + 1) * 3 ^ (k + mCircuitK rest) * a := by
            rw [← Nat.mul_assoc (4 ^ rest.length * 3 ^ mCircuitK rest) (4 * 3 ^ k) a,
              mul_four_rearrange_m (4 ^ rest.length) (3 ^ mCircuitK rest) 4 (3 ^ k),
              Nat.mul_comm (3 ^ mCircuitK rest) (3 ^ k), ← Nat.pow_succ, ← Nat.pow_add]
  simpa [List.length_cons, mCircuitS, mCircuitK_cons, syracuseIter_add] using hstrict

private theorem mCircuit_path_bound_aux (cs : List (Nat × Nat)) (a : Nat)
    (hpos : ∀ p ∈ cs, 1 ≤ p.1)
    (hvec : syracuseValVec (mCircuitK cs) a = mCircuitVec cs)
    (h3 : ∀ i : Nat, i < mCircuitK cs → 3 ≤ syracuseIter i a) :
    3 ^ cs.length * 2 ^ mCircuitS cs * syracuseIter (mCircuitK cs) a ≤
      4 ^ cs.length * 3 ^ mCircuitK cs * a ∧
    (cs ≠ [] →
      3 ^ cs.length * 2 ^ mCircuitS cs * syracuseIter (mCircuitK cs) a <
        4 ^ cs.length * 3 ^ mCircuitK cs * a) := by
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
    have h3rest : ∀ i, i < mCircuitK rest → 3 ≤ syracuseIter i (syracuseIter k a) := by
      intro i hi
      rw [syracuseIter_add]
      exact h3 (k + i) (by simp only [mCircuitK_cons]; omega)
    have hstrict := mCircuit_path_bound_step hk (h3 0 (by simp only [mCircuitK_cons]; omega)) hv1
      (ih (syracuseIter k a) hrest hvrest h3rest).1
    exact ⟨Nat.le_of_lt hstrict, fun _ => hstrict⟩

/-- **THE UNIVERSAL SIMONS–DE WEGER `m`-CIRCUIT BAND BOUND (2005):**
For EVERY non-trivial positive `m`-circuit cycle `IsMCircuitCycle cs n` (with `m = cs.length`,
`K = mCircuitK cs`, `S = mCircuitS cs`),
`3 ^ cs.length * 2 ^ mCircuitS cs < 4 ^ cs.length * 3 ^ mCircuitK cs`. -/
theorem mCircuit_simons_de_weger_bound {cs : List (Nat × Nat)} {n : Nat}
    (h : IsMCircuitCycle cs n) :
    3 ^ cs.length * 2 ^ mCircuitS cs < 4 ^ cs.length * 3 ^ mCircuitK cs := by
  have hpath := (mCircuit_path_bound_aux cs n (fun p hp => (h.canonical p hp).1)
    h.valVec_eq (fun i _ => (mCircuit_valley_three_le h i).2)).2 h.cs_nonempty
  rw [h.period_eq] at hpath
  exact Nat.lt_of_mul_lt_mul_right hpath

/-- **Exact 4-Circuit Band Corollary (certifying `search/mcircuit_hunter/mcircuit_hunter.c`):**
every non-trivial 4-circuit satisfies `81 * 2 ^ S < 256 * 3 ^ K`. -/
theorem fourCircuit_simons_de_weger_bound {cs : List (Nat × Nat)} {n : Nat}
    (hm : cs.length = 4) (h : IsMCircuitCycle cs n) :
    81 * 2 ^ mCircuitS cs < 256 * 3 ^ mCircuitK cs := by
  have hbd := mCircuit_simons_de_weger_bound h
  rwa [hm] at hbd

/-- **Exact 5-Circuit Band Corollary (certifying `search/mcircuit_hunter` for `m = 5`):**
every non-trivial 5-circuit satisfies `243 * 2 ^ S < 1024 * 3 ^ K`. -/
theorem fiveCircuit_simons_de_weger_bound {cs : List (Nat × Nat)} {n : Nat}
    (hm : cs.length = 5) (h : IsMCircuitCycle cs n) :
    243 * 2 ^ mCircuitS cs < 1024 * 3 ^ mCircuitK cs := by
  have hbd := mCircuit_simons_de_weger_bound h
  rwa [hm] at hbd

private theorem four_pow_lt_two_mul_three_pow {m : Nat} (hm : 0 < m) :
    4 ^ m < 2 ^ m * 3 ^ m := by
  rw [← Nat.mul_pow]
  induction m with
  | zero => exact absurd hm (Nat.lt_irrefl 0)
  | succ m ih =>
    cases m with
    | zero => decide
    | succ m =>
      have hprev : 4 ^ (m + 1) < (2 * 3) ^ (m + 1) := ih (Nat.succ_pos m)
      rw [Nat.pow_succ, Nat.pow_succ]
      have h4 : 0 < 4 ^ (m + 1) := Nat.pow_pos (by decide)
      omega

/-- **General Exponential Band Bound (`2 ^ S < 2 ^ m * 3 ^ K`):**
derived from `3^m * 2^S < 4^m * 3^K` via `4^m < 6^m = 2^m * 3^m`. -/
theorem mCircuit_two_pow_lt_pow_mul {cs : List (Nat × Nat)} {n : Nat}
    (h : IsMCircuitCycle cs n) :
    2 ^ mCircuitS cs < 2 ^ cs.length * 3 ^ mCircuitK cs := by
  have hm : 0 < cs.length := by
    cases cs with
    | nil => exact absurd rfl h.cs_nonempty
    | cons _ _ => exact Nat.succ_pos _
  have hbd := mCircuit_simons_de_weger_bound h
  have h46 := four_pow_lt_two_mul_three_pow hm
  have hcomb : 3 ^ cs.length * 2 ^ mCircuitS cs <
      3 ^ cs.length * (2 ^ cs.length * 3 ^ mCircuitK cs) := by
    calc 3 ^ cs.length * 2 ^ mCircuitS cs
        < 4 ^ cs.length * 3 ^ mCircuitK cs := hbd
      _ < (2 ^ cs.length * 3 ^ cs.length) * 3 ^ mCircuitK cs :=
            (Nat.mul_lt_mul_right (Nat.pow_pos (by decide))).mpr h46
      _ = 3 ^ cs.length * (2 ^ cs.length * 3 ^ mCircuitK cs) := by
            rw [Nat.mul_left_comm, Nat.mul_assoc]
  exact Nat.lt_of_mul_lt_mul_left hcomb

private theorem two_pow_minHalvings_pred_le_m {k : Nat} (hk : 0 < k) :
    1 ≤ minHalvings k ∧ 2 ^ (minHalvings k - 1) ≤ 3 ^ k := by
  have hspec :=
    findTwoExpAux_spec (2 * k + 1) (3 ^ k) 0 (Or.inl rfl)
      (by simpa [Nat.zero_add] using three_pow_lt_two_pow_double_succ k)
  have hgt : 3 ^ k < 2 ^ minHalvings k := by simpa [minHalvings] using hspec.1
  have hlo : minHalvings k = 0 ∨ 2 ^ (minHalvings k - 1) ≤ 3 ^ k := by
    simpa [minHalvings] using hspec.2
  have h3ge : 3 ≤ 3 ^ k := by simpa using Nat.pow_le_pow_right (by decide) hk
  have hne0 : minHalvings k ≠ 0 := by
    intro h0; rw [h0] at hgt; omega
  rcases hlo with h0 | hle
  · exact absurd h0 hne0
  · exact ⟨Nat.pos_of_ne_zero hne0, hle⟩

/-- **Universal `minHalvings` Search Window for Arbitrary `m`:**
every non-trivial `m`-circuit cycle satisfies
`minHalvings K ≤ S ∧ S < minHalvings K + m` (and hence `S ≤ minHalvings K + m - 1`). -/
theorem mCircuit_totalVal_window {cs : List (Nat × Nat)} {n : Nat}
    (h : IsMCircuitCycle cs n) :
    minHalvings (mCircuitK cs) ≤ mCircuitS cs ∧
      mCircuitS cs < minHalvings (mCircuitK cs) + cs.length := by
  let k := mCircuitK cs
  let s := mCircuitS cs
  let m := cs.length
  have hk : 0 < k := h.mCircuitK_pos
  have hlow : 3 ^ k < 2 ^ s := h.pow_lt
  have hhi : 2 ^ s < 2 ^ m * 3 ^ k := mCircuit_two_pow_lt_pow_mul h
  obtain ⟨hmpos, hpred⟩ := two_pow_minHalvings_pred_le_m hk
  have hge : minHalvings k ≤ s := by
    by_cases hle : minHalvings k ≤ s
    · exact hle
    · have hle' : s ≤ minHalvings k - 1 := by omega
      have hpow : 2 ^ s ≤ 2 ^ (minHalvings k - 1) := Nat.pow_le_pow_right (by decide) hle'
      omega
  have hlt : s < minHalvings k + m := by
    by_cases hlt' : s < minHalvings k + m
    · exact hlt'
    · have hge' : minHalvings k + m ≤ s := by omega
      have hpow : 2 ^ (minHalvings k + m) ≤ 2 ^ s := Nat.pow_le_pow_right (by decide) hge'
      have hm_lt : 3 ^ k < 2 ^ minHalvings k := lt_two_pow_minHalvings k
      have hmul : 2 ^ m * 3 ^ k < 2 ^ (minHalvings k + m) := by
        rw [Nat.pow_add, Nat.mul_comm (2 ^ minHalvings k)]
        exact (Nat.mul_lt_mul_left (Nat.two_pow_pos m)).mpr hm_lt
      omega
  exact ⟨hge, hlt⟩

/-- Weakened window corollary `mCircuitS cs ≤ minHalvings (mCircuitK cs) + cs.length`. -/
theorem mCircuit_totalVal_le_minHalvings_add {cs : List (Nat × Nat)} {n : Nat}
    (h : IsMCircuitCycle cs n) :
    mCircuitS cs ≤ minHalvings (mCircuitK cs) + cs.length :=
  Nat.le_of_lt (mCircuit_totalVal_window h).2

/-- **Tight 4-Circuit Band (`2 ^ S < 4 * 3 ^ K`):** since `81 * 4 = 324 > 256`, every
non-trivial 4-circuit satisfies `2 ^ S < 4 * 3 ^ K`. -/
theorem fourCircuit_two_pow_lt_four_mul {cs : List (Nat × Nat)} {n : Nat}
    (hm : cs.length = 4) (h : IsMCircuitCycle cs n) :
    2 ^ mCircuitS cs < 4 * 3 ^ mCircuitK cs := by
  have h81 := fourCircuit_simons_de_weger_bound hm h
  omega

/-- **Sharp Two-Value 4-Circuit Window (certifying `mcircuit_hunter.c`):**
every non-trivial 4-circuit satisfies `S = minHalvings K ∨ S = minHalvings K + 1`. -/
theorem fourCircuit_totalVal_eq_minHalvings_or_succ {cs : List (Nat × Nat)} {n : Nat}
    (hm : cs.length = 4) (h : IsMCircuitCycle cs n) :
    mCircuitS cs = minHalvings (mCircuitK cs) ∨
      mCircuitS cs = minHalvings (mCircuitK cs) + 1 := by
  have hwin := mCircuit_totalVal_window h
  have h4 := fourCircuit_two_pow_lt_four_mul hm h
  by_cases hle : mCircuitS cs ≤ minHalvings (mCircuitK cs) + 1
  · omega
  · have hge2 : minHalvings (mCircuitK cs) + 2 ≤ mCircuitS cs := by omega
    have hpow : 2 ^ (minHalvings (mCircuitK cs) + 2) ≤ 2 ^ mCircuitS cs :=
      Nat.pow_le_pow_right (by decide) hge2
    have hm_lt : 3 ^ mCircuitK cs < 2 ^ minHalvings (mCircuitK cs) :=
      lt_two_pow_minHalvings (mCircuitK cs)
    rw [Nat.pow_add] at hpow
    omega

/-! ### 5. Kernel-Verified Bounded 4-Circuit Elimination (`K ≤ 12`, kernel `decide`) -/

/-- Inner kernel check for a single 4-circuit candidate with precomputed partial numerator
`base123` and accumulated halving power `p2_123`. -/
def fourCircuitTupleFast (d d3 base123 p2_123 c4 : Nat) : Bool :=
  let c := base123 + p2_123 * c4
  decide (c < d3 ∨ c % d ≠ 0)

/-- Check all `e₃` with `2 ≤ e₃ ≤ bound` for fixed `(e₁, e₂)` and precomputed terms. -/
def checkFourE₃Fast (d d3 base123 p2_base3 c4 : Nat) : Nat → Bool
  | 0 => true
  | e₃ + 1 =>
    (e₃ + 1 < 2 || fourCircuitTupleFast d d3 base123 (p2_base3 * 2 ^ (e₃ + 1)) c4) &&
      checkFourE₃Fast d d3 base123 p2_base3 c4 e₃

/-- Check all `e₂` with `2 ≤ e₂ ≤ bound` for fixed `e₁` and precomputed `(k₁, k₂, k₃)`. -/
def checkFourE₂Fast (k s d d3 k₂ k₃ base1 p2_1 c2 c3 c4 e₁ : Nat) : Nat → Bool
  | 0 => true
  | e₂ + 1 =>
    let p2_12 := p2_1 * 2 ^ (k₂ + (e₂ + 1) - 1)
    (e₂ + 1 < 2 || checkFourE₃Fast d d3 (base1 + p2_1 * c2 + p2_12 * c3)
      (p2_12 * 2 ^ (k₃ - 1)) c4 (s + 2 - k - e₁ - (e₂ + 1))) &&
      checkFourE₂Fast k s d d3 k₂ k₃ base1 p2_1 c2 c3 c4 e₁ e₂

/-- Check all `e₁` with `2 ≤ e₁ ≤ bound` for fixed `(k₁, k₂, k₃)`. -/
def checkFourE₁Fast (k s d d3 k₁ k₂ k₃ base1 c2 c3 c4 : Nat) : Nat → Bool
  | 0 => true
  | e₁ + 1 =>
    (e₁ + 1 < 2 || checkFourE₂Fast k s d d3 k₂ k₃ base1 (2 ^ (k₁ + (e₁ + 1) - 1))
      c2 c3 c4 (e₁ + 1) (s - k - (e₁ + 1))) &&
      checkFourE₁Fast k s d d3 k₁ k₂ k₃ base1 c2 c3 c4 e₁

/-- Check all `k₃` with `1 ≤ k₃ ≤ bound` for fixed `(k₁, k₂)`. -/
def checkFourK₃Fast (k s d d3 k₁ k₂ base1 c2 : Nat) : Nat → Bool
  | 0 => true
  | k₃ + 1 =>
    let k₄ := k - k₁ - k₂ - (k₃ + 1)
    let c3 := 3 ^ k₄ * (3 ^ (k₃ + 1) - 2 ^ (k₃ + 1))
    let c4 := 3 ^ k₄ - 2 ^ k₄
    checkFourE₁Fast k s d d3 k₁ k₂ (k₃ + 1) base1 c2 c3 c4 (s - k - 2) &&
      checkFourK₃Fast k s d d3 k₁ k₂ base1 c2 k₃

/-- Check all `k₂` with `1 ≤ k₂ ≤ bound` for fixed `k₁`. -/
def checkFourK₂Fast (k s d d3 k₁ base1 : Nat) : Nat → Bool
  | 0 => true
  | k₂ + 1 =>
    let c2 := 3 ^ (k - k₁ - (k₂ + 1)) * (3 ^ (k₂ + 1) - 2 ^ (k₂ + 1))
    checkFourK₃Fast k s d d3 k₁ (k₂ + 1) base1 c2 (k - k₁ - (k₂ + 1) - 1) &&
      checkFourK₂Fast k s d d3 k₁ base1 k₂

/-- Check all `k₁` with `1 ≤ k₁ ≤ bound` for fixed `(k, s)`. -/
def checkFourK₁Fast (k s d d3 : Nat) : Nat → Bool
  | 0 => true
  | k₁ + 1 =>
    let base1 := 3 ^ (k - (k₁ + 1)) * (3 ^ (k₁ + 1) - 2 ^ (k₁ + 1))
    checkFourK₂Fast k s d d3 (k₁ + 1) base1 (k - (k₁ + 1) - 2) &&
      checkFourK₁Fast k s d d3 k₁

/-- Kernel-computable check at `(k, s)` for 4-circuits: band exclusion, `s < k + 4`, or all
canonical 4-circuit tuples fail `3 * D ≤ C ∧ D ∣ C`. -/
def fourCircuitKSRuledOut (k s : Nat) : Bool :=
  let d := 2 ^ s - 3 ^ k
  decide (256 * 3 ^ k ≤ 81 * 2 ^ s) || decide (s < k + 4) ||
    checkFourK₁Fast k s d (3 * d) (k - 3)

/-- Kernel-computable test certifying that no non-trivial 4-circuit cycle of odd length `k`
exists, checking both `s = minHalvings k` and `s = minHalvings k + 1`. -/
def fourCircuitKRuledOut (k : Nat) : Bool :=
  let s := minHalvings k
  fourCircuitKSRuledOut k s && fourCircuitKSRuledOut k (s + 1)

/-- Kernel-computable test certifying that no non-trivial 4-circuit cycle exists for any
`4 ≤ k ≤ K`. -/
def allFourCircuitsRuledOut : Nat → Bool
  | 0 => true
  | 1 => true
  | 2 => true
  | 3 => true
  | k + 1 => fourCircuitKRuledOut (k + 1) && allFourCircuitsRuledOut k

private theorem fourCircuitOffset_eq_fast {k₁ e₁ k₂ e₂ k₃ e₃ k₄ e₄ : Nat} (hk₃ : 1 ≤ k₃) :
    mCircuitOffset [(k₁, e₁), (k₂, e₂), (k₃, e₃), (k₄, e₄)] =
      (3 ^ ((k₁ + k₂ + k₃ + k₄) - k₁) * (3 ^ k₁ - 2 ^ k₁) +
        2 ^ (k₁ + e₁ - 1) * (3 ^ ((k₁ + k₂ + k₃ + k₄) - k₁ - k₂) * (3 ^ k₂ - 2 ^ k₂)) +
        (2 ^ (k₁ + e₁ - 1) * 2 ^ (k₂ + e₂ - 1)) * (3 ^ k₄ * (3 ^ k₃ - 2 ^ k₃))) +
      ((2 ^ (k₁ + e₁ - 1) * 2 ^ (k₂ + e₂ - 1) * 2 ^ (k₃ - 1)) * 2 ^ e₃) *
        (3 ^ k₄ - 2 ^ k₄) := by
  have hk₃e₃ : k₃ - 1 + e₃ = k₃ + e₃ - 1 := by omega
  have h1 : k₁ + k₂ + k₃ + k₄ - k₁ = k₂ + (k₃ + k₄) := by omega
  have h2 : k₂ + (k₃ + k₄) - k₂ = k₃ + k₄ := by omega
  simp only [mCircuitOffset, mCircuitK, List.map, List.sum_cons, List.sum_nil, Nat.add_zero,
    Nat.pow_zero, Nat.one_mul, Nat.mul_zero, h1, h2]
  rw [Nat.mul_assoc (2 ^ (k₁ + e₁ - 1) * 2 ^ (k₂ + e₂ - 1)) (2 ^ (k₃ - 1)) (2 ^ e₃),
    ← Nat.pow_add 2 (k₃ - 1) e₃, hk₃e₃]
  simp only [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

private theorem checkFourE₃Fast_sound (d d3 base123 p2_base3 c4 bound : Nat)
    (h : checkFourE₃Fast d d3 base123 p2_base3 c4 bound = true) :
    ∀ e₃ : Nat, 2 ≤ e₃ → e₃ ≤ bound →
      fourCircuitTupleFast d d3 base123 (p2_base3 * 2 ^ e₃) c4 = true := by
  induction bound with
  | zero => intro e₃ he₃ hle; omega
  | succ b ih =>
    simp only [checkFourE₃Fast, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    intro e₃ he₃ hle
    by_cases heq : e₃ = b + 1
    · subst heq
      rcases h.1 with hlt | hok
      · omega
      · exact hok
    · exact ih h.2 e₃ he₃ (by omega)

private theorem checkFourE₂Fast_sound (k s d d3 k₂ k₃ base1 p2_1 c2 c3 c4 e₁ bound : Nat)
    (h : checkFourE₂Fast k s d d3 k₂ k₃ base1 p2_1 c2 c3 c4 e₁ bound = true) :
    ∀ e₂ e₃ : Nat, 2 ≤ e₂ → e₂ ≤ bound → 2 ≤ e₃ → e₃ ≤ s + 2 - k - e₁ - e₂ →
      fourCircuitTupleFast d d3 (base1 + p2_1 * c2 + (p2_1 * 2 ^ (k₂ + e₂ - 1)) * c3)
        ((p2_1 * 2 ^ (k₂ + e₂ - 1) * 2 ^ (k₃ - 1)) * 2 ^ e₃) c4 = true := by
  induction bound with
  | zero => intro e₂ _ he₂ hle; omega
  | succ b ih =>
    simp only [checkFourE₂Fast, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    intro e₂ e₃ he₂ hle he₃ he₃le
    by_cases heq : e₂ = b + 1
    · subst heq
      rcases h.1 with hlt | hok
      · omega
      · exact checkFourE₃Fast_sound d d3 _ _ c4 (s + 2 - k - e₁ - (b + 1)) hok e₃ he₃ he₃le
    · exact ih h.2 e₂ e₃ he₂ (by omega) he₃ he₃le

private theorem checkFourE₁Fast_sound (k s d d3 k₁ k₂ k₃ base1 c2 c3 c4 bound : Nat)
    (h : checkFourE₁Fast k s d d3 k₁ k₂ k₃ base1 c2 c3 c4 bound = true) :
    ∀ e₁ e₂ e₃ : Nat, 2 ≤ e₁ → e₁ ≤ bound → 2 ≤ e₂ → e₂ ≤ s - k - e₁ →
      2 ≤ e₃ → e₃ ≤ s + 2 - k - e₁ - e₂ →
      fourCircuitTupleFast d d3
        (base1 + 2 ^ (k₁ + e₁ - 1) * c2 + (2 ^ (k₁ + e₁ - 1) * 2 ^ (k₂ + e₂ - 1)) * c3)
        ((2 ^ (k₁ + e₁ - 1) * 2 ^ (k₂ + e₂ - 1) * 2 ^ (k₃ - 1)) * 2 ^ e₃) c4 = true := by
  induction bound with
  | zero => intro e₁ _ _ he₁ hle; omega
  | succ b ih =>
    simp only [checkFourE₁Fast, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    intro e₁ e₂ e₃ he₁ hle he₂ he₂le he₃ he₃le
    by_cases heq : e₁ = b + 1
    · subst heq
      rcases h.1 with hlt | hok
      · omega
      · exact checkFourE₂Fast_sound k s d d3 k₂ k₃ base1 (2 ^ (k₁ + (b + 1) - 1))
          c2 c3 c4 (b + 1) (s - k - (b + 1)) hok e₂ e₃ he₂ he₂le he₃ he₃le
    · exact ih h.2 e₁ e₂ e₃ he₁ (by omega) he₂ he₂le he₃ he₃le

private theorem checkFourK₃Fast_sound (k s d d3 k₁ k₂ base1 c2 bound : Nat)
    (h : checkFourK₃Fast k s d d3 k₁ k₂ base1 c2 bound = true) :
    ∀ k₃ e₁ e₂ e₃ : Nat, 1 ≤ k₃ → k₃ ≤ bound →
      2 ≤ e₁ → e₁ ≤ s - k - 2 → 2 ≤ e₂ → e₂ ≤ s - k - e₁ →
      2 ≤ e₃ → e₃ ≤ s + 2 - k - e₁ - e₂ →
      let k₄ := k - k₁ - k₂ - k₃
      let c3 := 3 ^ k₄ * (3 ^ k₃ - 2 ^ k₃)
      let c4 := 3 ^ k₄ - 2 ^ k₄
      fourCircuitTupleFast d d3
        (base1 + 2 ^ (k₁ + e₁ - 1) * c2 + (2 ^ (k₁ + e₁ - 1) * 2 ^ (k₂ + e₂ - 1)) * c3)
        ((2 ^ (k₁ + e₁ - 1) * 2 ^ (k₂ + e₂ - 1) * 2 ^ (k₃ - 1)) * 2 ^ e₃) c4 = true := by
  induction bound with
  | zero => intro k₃ _ _ _ hk₃ hle; omega
  | succ b ih =>
    simp only [checkFourK₃Fast, Bool.and_eq_true] at h
    intro k₃ e₁ e₂ e₃ hk₃ hle he₁ he₁le he₂ he₂le he₃ he₃le
    by_cases heq : k₃ = b + 1
    · subst heq
      exact checkFourE₁Fast_sound k s d d3 k₁ k₂ (b + 1) base1 c2 _ _ (s - k - 2) h.1
        e₁ e₂ e₃ he₁ he₁le he₂ he₂le he₃ he₃le
    · exact ih h.2 k₃ e₁ e₂ e₃ hk₃ (by omega) he₁ he₁le he₂ he₂le he₃ he₃le

private theorem checkFourK₂Fast_sound (k s d d3 k₁ base1 bound : Nat)
    (h : checkFourK₂Fast k s d d3 k₁ base1 bound = true) :
    ∀ k₂ k₃ e₁ e₂ e₃ : Nat, 1 ≤ k₂ → k₂ ≤ bound → 1 ≤ k₃ → k₃ ≤ k - k₁ - k₂ - 1 →
      2 ≤ e₁ → e₁ ≤ s - k - 2 → 2 ≤ e₂ → e₂ ≤ s - k - e₁ →
      2 ≤ e₃ → e₃ ≤ s + 2 - k - e₁ - e₂ →
      let k₄ := k - k₁ - k₂ - k₃
      let c2 := 3 ^ (k - k₁ - k₂) * (3 ^ k₂ - 2 ^ k₂)
      let c3 := 3 ^ k₄ * (3 ^ k₃ - 2 ^ k₃)
      let c4 := 3 ^ k₄ - 2 ^ k₄
      fourCircuitTupleFast d d3
        (base1 + 2 ^ (k₁ + e₁ - 1) * c2 + (2 ^ (k₁ + e₁ - 1) * 2 ^ (k₂ + e₂ - 1)) * c3)
        ((2 ^ (k₁ + e₁ - 1) * 2 ^ (k₂ + e₂ - 1) * 2 ^ (k₃ - 1)) * 2 ^ e₃) c4 = true := by
  induction bound with
  | zero => intro k₂ _ _ _ _ hk₂ hle; omega
  | succ b ih =>
    simp only [checkFourK₂Fast, Bool.and_eq_true] at h
    intro k₂ k₃ e₁ e₂ e₃ hk₂ hle hk₃ hk₃le he₁ he₁le he₂ he₂le he₃ he₃le
    by_cases heq : k₂ = b + 1
    · subst heq
      exact checkFourK₃Fast_sound k s d d3 k₁ (b + 1) base1 _ (k - k₁ - (b + 1) - 1) h.1
        k₃ e₁ e₂ e₃ hk₃ hk₃le he₁ he₁le he₂ he₂le he₃ he₃le
    · exact ih h.2 k₂ k₃ e₁ e₂ e₃ hk₂ (by omega) hk₃ hk₃le he₁ he₁le he₂ he₂le he₃ he₃le

private theorem checkFourK₁Fast_sound (k s d d3 bound : Nat)
    (h : checkFourK₁Fast k s d d3 bound = true) :
    ∀ k₁ k₂ k₃ e₁ e₂ e₃ : Nat, 1 ≤ k₁ → k₁ ≤ bound → 1 ≤ k₂ → k₂ ≤ k - k₁ - 2 →
      1 ≤ k₃ → k₃ ≤ k - k₁ - k₂ - 1 → 2 ≤ e₁ → e₁ ≤ s - k - 2 →
      2 ≤ e₂ → e₂ ≤ s - k - e₁ → 2 ≤ e₃ → e₃ ≤ s + 2 - k - e₁ - e₂ →
      let k₄ := k - k₁ - k₂ - k₃
      let base1 := 3 ^ (k - k₁) * (3 ^ k₁ - 2 ^ k₁)
      let c2 := 3 ^ (k - k₁ - k₂) * (3 ^ k₂ - 2 ^ k₂)
      let c3 := 3 ^ k₄ * (3 ^ k₃ - 2 ^ k₃)
      let c4 := 3 ^ k₄ - 2 ^ k₄
      fourCircuitTupleFast d d3
        (base1 + 2 ^ (k₁ + e₁ - 1) * c2 + (2 ^ (k₁ + e₁ - 1) * 2 ^ (k₂ + e₂ - 1)) * c3)
        ((2 ^ (k₁ + e₁ - 1) * 2 ^ (k₂ + e₂ - 1) * 2 ^ (k₃ - 1)) * 2 ^ e₃) c4 = true := by
  induction bound with
  | zero => intro k₁ _ _ _ _ _ hk₁ hle; omega
  | succ b ih =>
    simp only [checkFourK₁Fast, Bool.and_eq_true] at h
    intro k₁ k₂ k₃ e₁ e₂ e₃ hk₁ hle hk₂ hk₂le hk₃ hk₃le he₁ he₁le he₂ he₂le he₃ he₃le
    by_cases heq : k₁ = b + 1
    · subst heq
      exact checkFourK₂Fast_sound k s d d3 (b + 1) _ (k - (b + 1) - 2) h.1
        k₂ k₃ e₁ e₂ e₃ hk₂ hk₂le hk₃ hk₃le he₁ he₁le he₂ he₂le he₃ he₃le
    · exact ih h.2 k₁ k₂ k₃ e₁ e₂ e₃ hk₁ (by omega) hk₂ hk₂le hk₃ hk₃le he₁ he₁le
        he₂ he₂le he₃ he₃le

/-- Soundness of `allFourCircuitsRuledOut` for all `4 ≤ k ≤ K`. -/
theorem allFourCircuitsRuledOut_sound (K : Nat) (h : allFourCircuitsRuledOut K = true) :
    ∀ k : Nat, 4 ≤ k → k ≤ K → fourCircuitKRuledOut k = true := by
  induction K with
  | zero => intro k hk hle; omega
  | succ K ih =>
    by_cases hlt : K < 3
    · intro k hk hle; omega
    · have hK : allFourCircuitsRuledOut (K + 1) =
          (fourCircuitKRuledOut (K + 1) && allFourCircuitsRuledOut K) := by
        obtain ⟨m, rfl⟩ : ∃ m, K = m + 3 := ⟨K - 3, by omega⟩
        rfl
      rw [hK, Bool.and_eq_true] at h
      intro k hk hle
      by_cases heq : k = K + 1
      · subst heq; exact h.1
      · exact ih h.2 k hk (by omega)

private theorem no_nontrivial_fourCircuit_of_ruledOut_tuple {n k₁ e₁ k₂ e₂ k₃ e₃ k₄ e₄ : Nat}
    (hcheck : fourCircuitKRuledOut (k₁ + k₂ + k₃ + k₄) = true) :
    ¬ IsMCircuitCycle [(k₁, e₁), (k₂, e₂), (k₃, e₃), (k₄, e₄)] n := by
  intro hcyc
  let k := k₁ + k₂ + k₃ + k₄
  let s := mCircuitS [(k₁, e₁), (k₂, e₂), (k₃, e₃), (k₄, e₄)]
  have hk_eq : mCircuitK [(k₁, e₁), (k₂, e₂), (k₃, e₃), (k₄, e₄)] = k := by
    simp only [mCircuitK, List.map, List.sum_cons, List.sum_nil, k]; omega
  have hc1 := hcyc.canonical (k₁, e₁) (by simp)
  have hc2 := hcyc.canonical (k₂, e₂) (by simp)
  have hc3 := hcyc.canonical (k₃, e₃) (by simp)
  have hc4 := hcyc.canonical (k₄, e₄) (by simp)
  dsimp only at hc1 hc2 hc3 hc4
  have hs_band := fourCircuit_totalVal_eq_minHalvings_or_succ rfl hcyc
  rw [hk_eq] at hs_band
  have hks : fourCircuitKSRuledOut k s = true := by
    simp only [fourCircuitKRuledOut, Bool.and_eq_true] at hcheck
    rcases hs_band with hs0 | hs1
    · rw [show s = minHalvings k from hs0]; exact hcheck.1
    · rw [show s = minHalvings k + 1 from hs1]; exact hcheck.2
  have hsim : 81 * 2 ^ s < 256 * 3 ^ k := by
    simpa [hk_eq] using fourCircuit_simons_de_weger_bound rfl hcyc
  have hs_eq : s = k + e₁ + e₂ + e₃ + e₄ - 4 := by simp only [s, mCircuitS, k]; omega
  have hs_ge : k + 4 ≤ s := by omega
  simp only [fourCircuitKSRuledOut, Bool.or_eq_true, decide_eq_true_eq] at hks
  have hchk1 : checkFourK₁Fast k s (2 ^ s - 3 ^ k) (3 * (2 ^ s - 3 ^ k)) (k - 3) = true := by
    rcases hks with (hge | hlt) | hok <;> first | exact hok | omega
  have htup := checkFourK₁Fast_sound k s (2 ^ s - 3 ^ k) (3 * (2 ^ s - 3 ^ k)) (k - 3) hchk1
    k₁ k₂ k₃ e₁ e₂ e₃ hc1.1 (by omega) hc2.1 (by omega) hc3.1 (by omega)
    hc1.2 (by omega) hc2.2 (by omega) hc3.2 (by omega)
  have hk₄eq : k - k₁ - k₂ - k₃ = k₄ := by omega
  simp only [fourCircuitTupleFast, hk₄eq, decide_eq_true_eq] at htup
  rw [show k = k₁ + k₂ + k₃ + k₄ from rfl, ← fourCircuitOffset_eq_fast (e₄ := e₄) hc3.1] at htup
  have h3d : 3 * (2 ^ s - 3 ^ (k₁ + k₂ + k₃ + k₄)) ≤
      mCircuitOffset [(k₁, e₁), (k₂, e₂), (k₃, e₃), (k₄, e₄)] := by
    simpa [hk_eq, k] using mCircuit_three_mul_denom_le hcyc
  have hmod :
      mCircuitOffset [(k₁, e₁), (k₂, e₂), (k₃, e₃), (k₄, e₄)] %
        (2 ^ s - 3 ^ (k₁ + k₂ + k₃ + k₄)) = 0 := by
    simpa [hk_eq, k] using Nat.mod_eq_zero_of_dvd (mCircuit_cycle_dvd hcyc)
  rcases htup with hlt | hne
  · omega
  · exact hne hmod

/-- General bounded 4-circuit elimination driven by `allFourCircuitsRuledOut`. -/
theorem no_nontrivial_fourCircuit_of_allRuledOut (K : Nat)
    (hcheck : allFourCircuitsRuledOut K = true) :
    ∀ cs : List (Nat × Nat), ∀ n : Nat,
      cs.length = 4 → mCircuitK cs ≤ K → ¬ IsMCircuitCycle cs n := by
  intro cs n hlen hk hcyc
  match cs, hlen with
  | [(k₁, e₁), (k₂, e₂), (k₃, e₃), (k₄, e₄)], _ =>
    have hk4 : 4 ≤ k₁ + k₂ + k₃ + k₄ := by
      have hc1 := hcyc.canonical (k₁, e₁) (by simp)
      have hc2 := hcyc.canonical (k₂, e₂) (by simp)
      have hc3 := hcyc.canonical (k₃, e₃) (by simp)
      have hc4 := hcyc.canonical (k₄, e₄) (by simp)
      omega
    have hk' : k₁ + k₂ + k₃ + k₄ ≤ K := by simpa [mCircuitK, Nat.add_assoc] using hk
    exact no_nontrivial_fourCircuit_of_ruledOut_tuple
      (allFourCircuitsRuledOut_sound K hcheck (k₁ + k₂ + k₃ + k₄) hk4 hk') hcyc

/-- **Exact Bounded 4-Circuit Elimination (`k₁ + k₂ + k₃ + k₄ ≤ 12`, kernel-verified):**
there is no non-trivial positive 4-circuit Collatz cycle with `mCircuitK cs ≤ 12`. -/
theorem no_nontrivial_fourCircuit_le_12 :
    ∀ cs : List (Nat × Nat), ∀ n : Nat,
      cs.length = 4 → mCircuitK cs ≤ 12 → ¬ IsMCircuitCycle cs n :=
  no_nontrivial_fourCircuit_of_allRuledOut 12 (by decide)

/-- Tuple-parameter form of `no_nontrivial_fourCircuit_le_12`. -/
theorem no_nontrivial_fourCircuit_tuple_le_12 :
    ∀ n k₁ e₁ k₂ e₂ k₃ e₃ k₄ e₄ : Nat, k₁ + k₂ + k₃ + k₄ ≤ 12 →
      ¬ IsMCircuitCycle [(k₁, e₁), (k₂, e₂), (k₃, e₃), (k₄, e₄)] n := by
  intro n k₁ e₁ k₂ e₂ k₃ e₃ k₄ e₄ hle
  exact no_nontrivial_fourCircuit_le_12 [(k₁, e₁), (k₂, e₂), (k₃, e₃), (k₄, e₄)] n rfl
    (by simpa [mCircuitK, Nat.add_assoc] using hle)

/-! ### 6. Explicit Barrier Separations (`Barriers 1–5`) -/

/-- **Barrier 1 Separation (`3n - 1` on `ℕ⁺`):**
Both `n = 5` (`5 → 7 → 5`, `k = 2, S = 3`) and the 2-circuit `n = 17` with `cs = [(4, 2), (3, 4)]`
(`K = 7, S = 11`) satisfy the `3n - 1` `m`-circuit equation `(3^K - 2^S) * n = mCircuitOffset cs`
yet violate `3^K < 2^S`. -/
theorem barrier1_mCircuit_three_n_minus_one :
    (Barriers.genIter 3 (-1) 5 5 = 5 ∧ ¬ (3 ^ 2 < 2 ^ 3)) ∧
    (Barriers.genIter 3 (-1) 18 17 = 17 ∧
      (3 ^ mCircuitK [(4, 2), (3, 4)] - 2 ^ mCircuitS [(4, 2), (3, 4)]) * 17 =
        mCircuitOffset [(4, 2), (3, 4)] ∧
      ¬ (3 ^ mCircuitK [(4, 2), (3, 4)] < 2 ^ mCircuitS [(4, 2), (3, 4)])) := by
  exact ⟨⟨Barriers.three_n_minus_one_cycle_5.1, by decide⟩,
    ⟨by decide, by decide, by decide⟩⟩

/-- **Barrier 2 Separation (`5n + 1` on `ℕ⁺`):**
`n = 13` (`K = 3, S = 7`) forms a positive `5n + 1` cycle satisfying `5^3 < 2^7` yet violating
`3^m * 2^S < 4^m * 3^K` at `m = 1, 2, 3, 4`, showing `mCircuit_simons_de_weger_bound` depends
on `3n + 1`'s negative drift `log₂(3/4) < 0` on every block. -/
theorem barrier2_mCircuit_five_n_plus_one :
    Barriers.genIter 5 1 10 13 = 13 ∧
    5 ^ 3 < 2 ^ 7 ∧
    ¬ (3 ^ 1 * 2 ^ 7 < 4 ^ 1 * 3 ^ 3) ∧
    ¬ (3 ^ 2 * 2 ^ 7 < 4 ^ 2 * 3 ^ 3) ∧
    ¬ (3 ^ 3 * 2 ^ 7 < 4 ^ 3 * 3 ^ 3) ∧
    ¬ (3 ^ 4 * 2 ^ 7 < 4 ^ 4 * 3 ^ 3) := by
  exact ⟨Barriers.five_n_plus_one_cycle_13.1, by decide, by decide, by decide, by decide, by decide⟩

/-- **Barrier 3 Separation (`3n + 1` on `ℤ_{<0}`):**
Both `n = -5` (`k = 2, S = 3`) and the negative 2-circuit `n = -17` (`cs = [(4, 2), (3, 4)]`,
`K = 7, S = 11`) satisfy the signed `m`-circuit equation yet violate positivity (`3 ≤ n`) and
`3^K < 2^S`. -/
theorem barrier3_mCircuit_neg_int :
    (Barriers.genIter 3 1 5 (-5) = -5 ∧ ¬ (3 ^ 2 < 2 ^ 3)) ∧
    (Barriers.genIter 3 1 18 (-17) = -17 ∧
      ((2 : Int) ^ mCircuitS [(4, 2), (3, 4)] - (3 : Int) ^ mCircuitK [(4, 2), (3, 4)]) * (-17) =
        (mCircuitOffset [(4, 2), (3, 4)] : Int) ∧
      ¬ (3 ^ mCircuitK [(4, 2), (3, 4)] < 2 ^ mCircuitS [(4, 2), (3, 4)])) := by
  exact ⟨⟨Barriers.neg_int_cycle_neg5.1, by decide⟩,
    ⟨by decide, by decide, by decide⟩⟩

/-- **Barrier 4 Separation (`ℤ₂` rational 4-circuit periodic points):**
For `cs = [(1, 2), (1, 2), (2, 2), (2, 2)]` (`m = 4, K = 6, S = 10`, `v = [2, 2, 1, 2, 1, 2]`),
`x = 1927 / 295 ∈ ℤ_(2) ⊂ ℤ₂` satisfies BOTH `3^6 < 2^10` AND the Simons–de Weger 4-circuit
band bound `81 * 2^10 < 256 * 3^6` (as well as `3 * 295 ≤ 1927`), has exact Syracuse period `6`
with halving vector `v`, yet fails global integrality (`¬ ∃ m : Int, x.Equiv (ofInt m)`). -/
theorem barrier4_mCircuit_twoAdic :
    let cs := [(1, 2), (1, 2), (2, 2), (2, 2)]
    let v := mCircuitVec cs
    let x := periodicPoint v (by decide)
    3 ^ mCircuitK cs < 2 ^ mCircuitS cs ∧
    81 * 2 ^ mCircuitS cs < 256 * 3 ^ mCircuitK cs ∧
    x = ⟨1927, 295, by decide⟩ ∧
    OddDenomRat.syracuseIter 6 x = x ∧
    OddDenomRat.syracuseValVec 6 x = v ∧
    (¬ ∃ m : Int, x.Equiv (OddDenomRat.ofInt m)) := by
  have hv : IsValidParityVec (mCircuitVec [(1, 2), (1, 2), (2, 2), (2, 2)]) :=
    mCircuitVec_valid (by simp) (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> decide)
  rcases universal_twoAdic_periodicPoint hv with ⟨_, _, hcyc, hvec, _, _⟩
  have hx :
      periodicPoint (mCircuitVec [(1, 2), (1, 2), (2, 2), (2, 2)]) (by decide) =
        ⟨1927, 295, by decide⟩ := by decide
  have hnotInt :
      ¬ ∃ m : Int,
        (periodicPoint (mCircuitVec [(1, 2), (1, 2), (2, 2), (2, 2)]) (by decide)).Equiv
          (OddDenomRat.ofInt m) := by
    rintro ⟨m, hm⟩
    rw [hx] at hm
    unfold OddDenomRat.Equiv OddDenomRat.ofInt at hm
    simp only at hm
    omega
  exact ⟨by decide, by decide, hx, hcyc, hvec, hnotInt⟩

/-- **Barrier 5 Separation (Conway 1972 undecidability vs structured `3n + 1` `m`-circuits):**
General periodic piecewise-affine maps can simulate arbitrary Minsky machines, whereas
`mCircuit_simons_de_weger_bound` applies specifically to canonical `3n + 1` `m`-circuits where
each block satisfies `3 * 2^(k + e - 1) * v_{j+1} < 4 * 3^k * v_j`, yielding `3^m * 2^S < 4^m * 3^K`
(instantiated at `m = 4` by `81 * 2^S < 256 * 3^K` and `no_nontrivial_fourCircuit_le_12`). -/
theorem barrier5_mCircuit_conway_separation :
    (∀ cs : List (Nat × Nat), ∀ n : Nat,
      IsMCircuitCycle cs n → 3 ^ cs.length * 2 ^ mCircuitS cs < 4 ^ cs.length * 3 ^ mCircuitK cs) ∧
    (∀ cs : List (Nat × Nat), ∀ n : Nat,
      cs.length = 4 → mCircuitK cs ≤ 12 → ¬ IsMCircuitCycle cs n) :=
  ⟨fun _ _ h => mCircuit_simons_de_weger_bound h, no_nontrivial_fourCircuit_le_12⟩

end SolveCollatz
