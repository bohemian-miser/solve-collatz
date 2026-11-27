/-
Copyright (c) 2026 The solve-collatz contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Collatz.Known.TerrasParity

/-!
# Terras (1976) & Everett (1977) Natural Density 1 of Finite Stopping Times (`KNOWN-001`, Part 2)

Pure Lean 4 core formalization (zero Mathlib, zero reals) of the Terras/Everett density-1
theorem for Collatz finite stopping times:
- `HasFiniteStoppingTime` and the Terras dropping criterion `terras_lt_of_low_ones`.
- Exact bijection between residues mod `2^k` and all length-`k` Boolean parity vectors
  `allBitVecs k`, yielding `badCount_eq_filter_allBitVecs`.
- Elementary pure-`Nat` integer Chernoff exponential decay bound for `k = 5 * m`:
  `badCount (5 * m) * 108 ^ m ≤ 3125 ^ m`, giving
  `badCount (5 * m) * 3456 ^ m ≤ 3125 ^ m * 2 ^ (5 * m)`,
  and `badCount (5 * m) * D < 2 ^ (5 * m)` for every `D > 0` (`3125 < 3456`).
- Full natural density 1 theorems (`terras_bounded_drop_density` and `terras_natural_density_one`):
  for every `D > 0`, there exists `N₀` such that for all `N ≥ N₀`, the count of `n < N` failing
  `HasFiniteStoppingTime n` satisfies `exceptionalCount N * D < N`.
-/

@[expose] public section

namespace SolveCollatz

/-! ### 1. Terras Dropping Criterion -/

/-- A natural number `n` has a finite stopping time if some positive iterate under `collatzIter`
drops strictly below `n`. -/
def HasFiniteStoppingTime (n : Nat) : Prop :=
  ∃ k : Nat, 0 < k ∧ collatzIter k n < n

/-- Any strict drop under `terrasIter k` with `0 < k` yields a finite stopping time for the
frozen `Challenge.collatzIter`. -/
theorem hasFiniteStoppingTime_of_terras_lt {k n : Nat} (hk : 0 < k)
    (hlt : terrasIter k n < n) : HasFiniteStoppingTime n := by
  refine ⟨k + countOnes (terrasParityVec k n), by omega, ?_⟩
  rw [collatzIter_eq_terrasIter k n]
  exact hlt

/-- **Terras Dropping Criterion (`Terras 1976`):** if `3 ^ c < 2 ^ k` where
`c = countOnes (terrasParityVec k r)` and `terrasIter k r < (2 ^ k - 3 ^ c) * q`, then
`terrasIter k (r + 2 ^ k * q) < r + 2 ^ k * q` and `HasFiniteStoppingTime (r + 2 ^ k * q)`. -/
theorem terras_lt_of_low_ones {k r q : Nat}
    (hlow : 3 ^ countOnes (terrasParityVec k r) < 2 ^ k)
    (hq : terrasIter k r < (2 ^ k - 3 ^ countOnes (terrasParityVec k r)) * q) :
    terrasIter k (r + 2 ^ k * q) < r + 2 ^ k * q ∧
      HasFiniteStoppingTime (r + 2 ^ k * q) := by
  let c := countOnes (terrasParityVec k r)
  change 3 ^ c < 2 ^ k at hlow
  change terrasIter k r < (2 ^ k - 3 ^ c) * q at hq
  have h3pos : 0 < 3 ^ c := Nat.pow_pos (by decide)
  have hk : 0 < k := by
    cases k with
    | zero => simp only [Nat.pow_zero] at hlow; omega
    | succ k' => exact Nat.succ_pos k'
  have hcong := (terrasParityVec_mod_two_pow k r q).2
  have hsum : (2 ^ k - 3 ^ c) * q + 3 ^ c * q = 2 ^ k * q := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt hlow)]
  have hlt : terrasIter k (r + 2 ^ k * q) < r + 2 ^ k * q := by
    rw [hcong]
    change terrasIter k r + 3 ^ c * q < r + 2 ^ k * q
    omega
  exact ⟨hlt, hasFiniteStoppingTime_of_terras_lt hk hlt⟩

/-- Coarse step bound `terrasStep n ≤ 2 * n` valid for every `n : Nat`. -/
private theorem terrasStep_le_two_mul (n : Nat) : terrasStep n ≤ 2 * n := by
  by_cases heven : n % 2 = 0
  · rw [terrasStep_even heven]; omega
  · rw [terrasStep_odd (by omega)]; omega

/-- Coarse iterate bound `terrasIter k n ≤ 2 ^ k * n`. -/
theorem terrasIter_le_two_pow_mul (k n : Nat) : terrasIter k n ≤ 2 ^ k * n := by
  induction k generalizing n with
  | zero => simp [terrasIter]
  | succ k ih =>
    have hstep := terrasStep_le_two_mul n
    have hmul : 2 ^ k * terrasStep n ≤ 2 ^ k * (2 * n) := Nat.mul_le_mul_left (2 ^ k) hstep
    have hpow : 2 ^ (k + 1) * n = 2 ^ k * (2 * n) := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    calc terrasIter (k + 1) n
        = terrasIter k (terrasStep n) := rfl
      _ ≤ 2 ^ k * terrasStep n := ih (terrasStep n)
      _ ≤ 2 ^ (k + 1) * n := by rw [hpow]; exact hmul

/-- Every residue `r < 2 ^ k` satisfies `terrasIter k r < 2 ^ (2 * k)`. -/
theorem terrasIter_lt_two_pow_two_mul {k r : Nat} (hr : r < 2 ^ k) :
    terrasIter k r < 2 ^ (2 * k) := by
  have hle := terrasIter_le_two_pow_mul k r
  have hkpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hmul : 2 ^ k * r < 2 ^ k * 2 ^ k := Nat.mul_lt_mul_of_pos_left hr hkpos
  have hpow : 2 ^ (2 * k) = 2 ^ k * 2 ^ k := by
    rw [Nat.two_mul, Nat.pow_add]
  rw [hpow]
  exact Nat.lt_of_le_of_lt hle hmul

/-- Any `n ≥ 2 ^ (3 * k)` whose residue mod `2 ^ k` has `3 ^ c < 2 ^ k` drops within `k`
Terras steps and hence satisfies `HasFiniteStoppingTime n`. -/
theorem terras_lt_of_large_low_ones {k n : Nat} (hn : 2 ^ (3 * k) ≤ n)
    (hlow : 3 ^ countOnes (terrasParityVec k (n % 2 ^ k)) < 2 ^ k) :
    terrasIter k n < n ∧ HasFiniteStoppingTime n := by
  let r := n % 2 ^ k
  let q := n / 2 ^ k
  let c := countOnes (terrasParityVec k r)
  have hkpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hr : r < 2 ^ k := Nat.mod_lt n hkpos
  have hpow3 : 2 ^ (3 * k) = 2 ^ k * 2 ^ (2 * k) := by
    rw [show 3 * k = k + 2 * k by omega, Nat.pow_add]
  have hq_ge : 2 ^ (2 * k) ≤ q := by
    have hmul_le : 2 ^ k * 2 ^ (2 * k) ≤ n := by rw [← hpow3]; exact hn
    rw [Nat.mul_comm] at hmul_le
    exact (Nat.le_div_iff_mul_le hkpos).mpr hmul_le
  have hlow' : 3 ^ c < 2 ^ k := hlow
  have hdiff : 1 ≤ 2 ^ k - 3 ^ c := by omega
  have hq_le : q ≤ (2 ^ k - 3 ^ c) * q := by
    calc q = 1 * q := (Nat.one_mul q).symm
      _ ≤ (2 ^ k - 3 ^ c) * q := Nat.mul_le_mul_right q hdiff
  have hiter_lt : terrasIter k r < (2 ^ k - 3 ^ c) * q :=
    Nat.lt_of_lt_of_le (terrasIter_lt_two_pow_two_mul hr) (Nat.le_trans hq_ge hq_le)
  have hdrop := terras_lt_of_low_ones hlow hiter_lt
  have hdecomp : r + 2 ^ k * q = n := Nat.mod_add_div n (2 ^ k)
  rw [hdecomp] at hdrop
  exact hdrop

/-! ### 2. Pure-`Nat` Counting and Periodicity Helpers -/

/-- Count of natural numbers `i < n` satisfying Boolean predicate `p`. -/
def countLt (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => countLt p n + (if p n then 1 else 0)

/-- `countLt p n` never exceeds `n`. -/
theorem countLt_le (p : Nat → Bool) (n : Nat) : countLt p n ≤ n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    simp only [countLt]
    split <;> omega

/-- Pointwise implication on `[0, n)` implies monotonicity of `countLt`. -/
theorem countLt_mono_pred {p q : Nat → Bool} (n : Nat)
    (h : ∀ i : Nat, i < n → p i = true → q i = true) :
    countLt p n ≤ countLt q n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    have hih := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    simp only [countLt]
    cases hp : p n
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      cases q n <;> simp <;> omega
    · have hq : q n = true := h n (Nat.lt_succ_self n) hp
      simp [hq]; omega

/-- `countLt p` is monotone in its upper bound. -/
theorem countLt_mono_bound (p : Nat → Bool) {a b : Nat} (hab : a ≤ b) :
    countLt p a ≤ countLt p b := by
  induction b with
  | zero =>
    have ha : a = 0 := Nat.eq_zero_of_le_zero hab
    subst ha; exact Nat.le_refl 0
  | succ b ih =>
    by_cases hle : a ≤ b
    · have hih := ih hle
      simp only [countLt]
      split <;> omega
    · have heq : a = b + 1 := by omega
      subst heq
      exact Nat.le_refl _

/-- Union bound for `countLt` under Boolean disjunction. -/
theorem countLt_or_le (p q : Nat → Bool) (n : Nat) :
    countLt (fun i => p i || q i) n ≤ countLt p n + countLt q n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    simp only [countLt]
    by_cases hp : p n <;> by_cases hq : q n <;> simp [hp, hq] <;> omega

/-- At most `m` indices below `n` satisfy `i < m`. -/
theorem countLt_lt_bound (m n : Nat) :
    countLt (fun i => decide (i < m)) n ≤ m := by
  induction n with
  | zero => exact Nat.zero_le m
  | succ n ih =>
    simp only [countLt]
    by_cases hlt : n < m
    · have hle : countLt (fun i => decide (i < m)) n ≤ n := countLt_le _ n
      simp [hlt]; omega
    · simp [hlt]; exact ih

/-- Shifting rule for `countLt` across `[0, a)` and `[a, a + b)`. -/
theorem countLt_add (p : Nat → Bool) (a b : Nat) :
    countLt p (a + b) = countLt p a + countLt (fun i => p (a + i)) b := by
  induction b with
  | zero => simp [countLt]
  | succ b ih =>
    rw [← Nat.add_assoc, countLt, ih, countLt]
    omega

/-- Periodicity of `p` with period `M` gives `p (M * q + i) = p i`. -/
private theorem periodic_add_mul (p : Nat → Bool) (M q : Nat)
    (hper : ∀ i : Nat, p (i + M) = p i) (i : Nat) : p (M * q + i) = p i := by
  induction q generalizing i with
  | zero => simp
  | succ q ih =>
    have heq : M * (q + 1) + i = (M * q + i) + M := by
      rw [Nat.mul_succ]; omega
    rw [heq, hper, ih]

/-- Exact block counting for periodic predicates: `countLt p (M * q) = countLt p M * q`. -/
theorem countLt_mul_periodic (p : Nat → Bool) (M q : Nat)
    (hper : ∀ i : Nat, p (i + M) = p i) :
    countLt p (M * q) = countLt p M * q := by
  induction q with
  | zero => simp [countLt]
  | succ q ih =>
    rw [Nat.mul_succ, countLt_add, ih]
    have hblock : countLt (fun i => p (M * q + i)) M = countLt p M := by
      have heq : (fun i => p (M * q + i)) = p := funext (periodic_add_mul p M q hper)
      rw [heq]
    rw [hblock, Nat.mul_succ]

/-- Periodic counting bound for arbitrary `N`:
`countLt p N ≤ countLt p M * (N / M) + countLt p M`. -/
theorem countLt_periodic_le (p : Nat → Bool) {M : Nat} (hM : 0 < M)
    (hper : ∀ i : Nat, p (i + M) = p i) (N : Nat) :
    countLt p N ≤ countLt p M * (N / M) + countLt p M := by
  have hdecomp : M * (N / M) + N % M = N := Nat.div_add_mod N M
  conv => lhs; rw [← hdecomp, countLt_add]
  rw [countLt_mul_periodic p M (N / M) hper]
  have htail_eq : countLt (fun i => p (M * (N / M) + i)) (N % M) = countLt p (N % M) := by
    have heq : (fun i => p (M * (N / M) + i)) = p :=
      funext (periodic_add_mul p M (N / M) hper)
    rw [heq]
  rw [htail_eq]
  have hrem : countLt p (N % M) ≤ countLt p M :=
    countLt_mono_bound p (Nat.le_of_lt (Nat.mod_lt N hM))
  omega

/-- Equivalence between `countLt p n` and `((List.range n).filter p).length`. -/
theorem countLt_eq_filter_range (p : Nat → Bool) (n : Nat) :
    countLt p n = ((List.range n).filter p).length := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [countLt, List.range_succ, List.filter_append, List.length_append, ih]
    cases hp : p n <;> simp [hp]

/-! ### 3. Bijection Between Residues Mod `2^k` and Length-`k` Bitvectors -/

/-- All `2 ^ k` Boolean lists of length `k`. -/
def allBitVecs : Nat → List (List Bool)
  | 0 => [[]]
  | k + 1 => (allBitVecs k).map (false :: ·) ++ (allBitVecs k).map (true :: ·)

/-- `allBitVecs k` contains precisely the Boolean lists of length `k`. -/
theorem mem_allBitVecs_iff (k : Nat) (v : List Bool) :
    v ∈ allBitVecs k ↔ v.length = k := by
  induction k generalizing v with
  | zero =>
    simp [allBitVecs]
  | succ k ih =>
    cases v with
    | nil => simp [allBitVecs]
    | cons b bs =>
      cases b <;> simp [allBitVecs, ih]

/-- Mapping an injective-on-`l` function preserves `List.Nodup`. -/
private theorem nodup_map_on {α β : Type} {f : α → β} {l : List α} (hl : l.Nodup)
    (hinj : ∀ a : α, a ∈ l → ∀ b : α, b ∈ l → f a = f b → a = b) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons, List.nodup_cons]
    rw [List.nodup_cons] at hl
    refine ⟨?_, ih hl.2 (fun a ha b hb =>
      hinj a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb))⟩
    intro hmem
    rw [List.mem_map] at hmem
    rcases hmem with ⟨y, hy, hxy⟩
    exact hl.1 ((hinj y (List.mem_cons_of_mem x hy) x List.mem_cons_self hxy) ▸ hy)

/-- `allBitVecs k` has no duplicate parity vectors. -/
theorem allBitVecs_nodup (k : Nat) : (allBitVecs k).Nodup := by
  induction k with
  | zero => simp [allBitVecs]
  | succ k ih =>
    have h0 : ((allBitVecs k).map (false :: ·)).Nodup :=
      nodup_map_on ih (fun _ _ _ _ h => (List.cons.inj h).2)
    have h1 : ((allBitVecs k).map (true :: ·)).Nodup :=
      nodup_map_on ih (fun _ _ _ _ h => (List.cons.inj h).2)
    rw [allBitVecs, List.nodup_append]
    refine ⟨h0, h1, ?_⟩
    intro u hu v hv heq
    simp only [List.mem_map] at hu hv
    rcases hu with ⟨u', _, rfl⟩
    rcases hv with ⟨v', _, rfl⟩
    cases heq

/-- Two duplicate-free lists with the same membership set are permutations of each other. -/
private theorem nodup_perm_of_mem_iff {α : Type} [BEq α] [LawfulBEq α] {l₁ l₂ : List α}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (hmem : ∀ a : α, a ∈ l₁ ↔ a ∈ l₂) : l₁.Perm l₂ := by
  rw [List.perm_iff_count]
  intro a
  by_cases ha : a ∈ l₁
  · have ha2 : a ∈ l₂ := (hmem a).mp ha
    rw [List.Nodup.count h₁, List.Nodup.count h₂]
    simp [ha, ha2]
  · have ha2 : a ∉ l₂ := fun h => ha ((hmem a).mpr h)
    rw [List.count_eq_zero_of_not_mem ha, List.count_eq_zero_of_not_mem ha2]

/-- Mapping `terrasParityVec k` over `[0, 2 ^ k)` produces a duplicate-free list. -/
private theorem map_terrasParityVec_nodup (k : Nat) :
    ((List.range (2 ^ k)).map (terrasParityVec k)).Nodup := by
  refine nodup_map_on List.nodup_range ?_
  intro a ha b hb heq
  rw [List.mem_range] at ha hb
  exact terrasParityVec_inj_mod_two_pow ha hb heq

/-- **Bijection as List Permutation:** mapping `terrasParityVec k` over `List.range (2 ^ k)`
is a permutation of `allBitVecs k`. -/
theorem map_terrasParityVec_perm_allBitVecs (k : Nat) :
    ((List.range (2 ^ k)).map (terrasParityVec k)).Perm (allBitVecs k) := by
  refine nodup_perm_of_mem_iff (map_terrasParityVec_nodup k) (allBitVecs_nodup k) (fun v => ?_)
  constructor
  · intro hv
    simp only [List.mem_map, List.mem_range] at hv
    rcases hv with ⟨r, _, rfl⟩
    exact (mem_allBitVecs_iff k _).mpr (terrasParityVec_length k r)
  · intro hv
    have hlen := (mem_allBitVecs_iff k v).mp hv
    rcases terrasParityVec_surj_mod_two_pow k v hlen with ⟨r, hr, hvec, _⟩
    simp only [List.mem_map, List.mem_range]
    exact ⟨r, hr, hvec⟩

/-- Boolean indicator that residue `r` has too many ones (`2 ^ k ≤ 3 ^ c`) over `k` steps. -/
def badResidue (k r : Nat) : Bool :=
  decide (2 ^ k ≤ 3 ^ countOnes (terrasParityVec k r))

/-- Number of bad residues `r < 2 ^ k` with `2 ^ k ≤ 3 ^ countOnes (terrasParityVec k r)`. -/
def badCount (k : Nat) : Nat :=
  countLt (badResidue k) (2 ^ k)

/-- `badResidue k (n % 2 ^ k)` is periodic with period `2 ^ k`. -/
theorem badResidue_mod_periodic (k : Nat) (i : Nat) :
    badResidue k ((i + 2 ^ k) % 2 ^ k) = badResidue k (i % 2 ^ k) := by
  rw [Nat.add_mod_right]

/-- `badCount k` equals the number of length-`k` bitvectors `v` with `2 ^ k ≤ 3 ^ countOnes v`. -/
theorem badCount_eq_filter_allBitVecs (k : Nat) :
    badCount k =
      ((allBitVecs k).filter (fun v => decide (2 ^ k ≤ 3 ^ countOnes v))).length := by
  let p : List Bool → Bool := fun v => decide (2 ^ k ≤ 3 ^ countOnes v)
  have hperm := (map_terrasParityVec_perm_allBitVecs k).filter p
  have hlen : (((List.range (2 ^ k)).map (terrasParityVec k)).filter p).length =
      ((allBitVecs k).filter p).length := hperm.length_eq
  rw [List.filter_map, List.length_map] at hlen
  have hcomp : p ∘ terrasParityVec k = badResidue k := rfl
  rw [badCount, countLt_eq_filter_range, ← hcomp, hlen]

/-! ### 4. Elementary Pure-`Nat` Integer Chernoff Exponential Decay Bound -/

/-- Sum of a `Nat`-valued weight function over a list. -/
def listSum {α : Type} (f : α → Nat) : List α → Nat
  | [] => 0
  | x :: xs => f x + listSum f xs

/-- `listSum` distributes over list append. -/
private theorem listSum_append {α : Type} (f : α → Nat) (l₁ l₂ : List α) :
    listSum f (l₁ ++ l₂) = listSum f l₁ + listSum f l₂ := by
  induction l₁ with
  | nil => simp [listSum]
  | cons x xs ih => simp [listSum, ih, Nat.add_assoc]

/-- `listSum` commutes with `List.map`. -/
private theorem listSum_map {α β : Type} (f : β → Nat) (g : α → β) (l : List α) :
    listSum f (l.map g) = listSum (f ∘ g) l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [listSum, ih]

/-- **Pure-`Nat` Integer Markov Inequality:** if every `x ∈ l` satisfying `p x = true` has
weight `T ≤ f x`, then `(l.filter p).length * T ≤ listSum f l`. -/
private theorem listSum_markov {α : Type} (p : α → Bool) (f : α → Nat) (T : Nat)
    (l : List α) (hle : ∀ x : α, x ∈ l → p x = true → T ≤ f x) :
    (l.filter p).length * T ≤ listSum f l := by
  induction l with
  | nil => simp [listSum]
  | cons x xs ih =>
    have hih := ih (fun y hy => hle y (List.mem_cons_of_mem x hy))
    cases hp : p x
    · simp only [List.filter, hp, listSum]
      omega
    · have hx : T ≤ f x := hle x List.mem_cons_self hp
      simp only [List.filter, hp, listSum, List.length_cons, Nat.succ_mul]
      omega

/-- Exact binomial weight `3 ^ countOnes v * 2 ^ (k - countOnes v)` of a bitvector `v`. -/
def bitVecWeight (k : Nat) (v : List Bool) : Nat :=
  3 ^ countOnes v * 2 ^ (k - countOnes v)

/-- Prepending `false` doubles `bitVecWeight` when `countOnes v ≤ k`. -/
private theorem bitVecWeight_cons_false {k : Nat} {v : List Bool} (hv : countOnes v ≤ k) :
    bitVecWeight (k + 1) (false :: v) = 2 * bitVecWeight k v := by
  simp only [bitVecWeight, countOnes, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
  have hsub : k + 1 - countOnes v = (k - countOnes v) + 1 := by omega
  rw [hsub, Nat.pow_succ, Nat.mul_comm (2 ^ (k - countOnes v)) 2]
  rw [Nat.mul_left_comm]

/-- Prepending `true` triples `bitVecWeight`. -/
private theorem bitVecWeight_cons_true (k : Nat) (v : List Bool) :
    bitVecWeight (k + 1) (true :: v) = 3 * bitVecWeight k v := by
  simp only [bitVecWeight, countOnes, ↓reduceIte]
  have hsub : k + 1 - (1 + countOnes v) = k - countOnes v := by omega
  rw [hsub, Nat.add_comm 1 (countOnes v), Nat.pow_succ]
  rw [Nat.mul_assoc, Nat.mul_left_comm (3 ^ countOnes v) 3 (2 ^ (k - countOnes v))]

/-- `listSum` of `(c * f x)` equals `c * listSum f l`. -/
private theorem listSum_mul_left {α : Type} (c : Nat) (f : α → Nat) (l : List α) :
    listSum (fun x => c * f x) l = c * listSum f l := by
  induction l with
  | nil => simp [listSum]
  | cons x xs ih => simp [listSum, ih, Nat.mul_add]

/-- `listSum` depends only on values on elements of `l`. -/
private theorem listSum_congr {α : Type} {f g : α → Nat} {l : List α}
    (h : ∀ x : α, x ∈ l → f x = g x) : listSum f l = listSum g l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [listSum]
    rw [h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-- **Exact Pure-`Nat` Binomial Sum:**
`∑_{v ∈ allBitVecs k} 3 ^ countOnes v * 2 ^ (k - countOnes v) = 5 ^ k`. -/
theorem bitVecWeight_allBitVecs_sum (k : Nat) :
    listSum (bitVecWeight k) (allBitVecs k) = 5 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [allBitVecs, listSum_append, listSum_map, listSum_map]
    have hfalse : listSum (bitVecWeight (k + 1) ∘ (false :: ·)) (allBitVecs k) =
        2 * listSum (bitVecWeight k) (allBitVecs k) := by
      rw [← listSum_mul_left]
      refine listSum_congr (fun v hv => ?_)
      have hlen := (mem_allBitVecs_iff k v).mp hv
      exact bitVecWeight_cons_false (hlen ▸ countOnes_le_length v)
    have htrue : listSum (bitVecWeight (k + 1) ∘ (true :: ·)) (allBitVecs k) =
        3 * listSum (bitVecWeight k) (allBitVecs k) := by
      rw [← listSum_mul_left]
      refine listSum_congr (fun v _ => bitVecWeight_cons_true k v)
    rw [hfalse, htrue, ih, Nat.pow_succ]
    omega

/-- Key exponent implication for `k = 5 * m`: `2 ^ (5 * m) ≤ 3 ^ c` implies `3 * m ≤ c`
(because `3 ^ 3 = 27 < 32 = 2 ^ 5`). -/
theorem three_pow_ge_two_pow_five_mul_imp {m c : Nat} (h : 2 ^ (5 * m) ≤ 3 ^ c) :
    3 * m ≤ c := by
  have hpow3 : (2 ^ (5 * m)) ^ 3 ≤ (3 ^ c) ^ 3 := Nat.pow_le_pow_left h 3
  have hleft : (2 ^ (5 * m)) ^ 3 = 2 ^ (15 * m) := by
    rw [← Nat.pow_mul, show 5 * m * 3 = 15 * m by omega]
  have hright : (3 ^ c) ^ 3 = 27 ^ c := by
    rw [← Nat.pow_mul, Nat.mul_comm c 3, Nat.pow_mul]
  have h27 : 27 ^ c ≤ (2 ^ 5) ^ c := Nat.pow_le_pow_left (by decide : 27 ≤ 2 ^ 5) c
  have h32 : (2 ^ 5) ^ c = 2 ^ (5 * c) := by rw [← Nat.pow_mul]
  have h2pow : 2 ^ (15 * m) ≤ 2 ^ (5 * c) := by
    rw [← hleft, ← h32]
    exact Nat.le_trans hpow3 (by rw [hright]; exact h27)
  by_cases hlt : 3 * m ≤ c
  · exact hlt
  · exfalso
    have hlt' : 5 * c < 15 * m := by omega
    have hpow_lt := Nat.pow_lt_pow_right (by decide : 1 < 2) hlt'
    omega

/-- Chernoff lower bound per bad vector: when `3 * m ≤ c ≤ 5 * m`,
`108 ^ m ≤ 3 ^ c * 2 ^ (5 * m - c)`. -/
theorem one_hundred_eight_pow_le {m c : Nat} (hlo : 3 * m ≤ c) (hhi : c ≤ 5 * m) :
    108 ^ m ≤ 3 ^ c * 2 ^ (5 * m - c) := by
  let d := c - 3 * m
  have hc_eq : c = 3 * m + d := (Nat.add_sub_of_le hlo).symm
  have h2m_eq : 2 * m = d + (5 * m - c) := by omega
  have h108 : 108 ^ m = 3 ^ (3 * m) * 2 ^ (2 * m) := by
    have hbase : 108 = 3 ^ 3 * 2 ^ 2 := by decide
    rw [hbase, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul]
  have h2le3 : 2 ^ d ≤ 3 ^ d := Nat.pow_le_pow_left (by decide : 2 ≤ 3) d
  have hmul_le : 2 ^ d * 2 ^ (5 * m - c) ≤ 3 ^ d * 2 ^ (5 * m - c) :=
    Nat.mul_le_mul_right _ h2le3
  calc 108 ^ m
      = 3 ^ (3 * m) * (2 ^ d * 2 ^ (5 * m - c)) := by rw [h108, h2m_eq, Nat.pow_add]
    _ ≤ 3 ^ (3 * m) * (3 ^ d * 2 ^ (5 * m - c)) := Nat.mul_le_mul_left _ hmul_le
    _ = 3 ^ c * 2 ^ (5 * m - c) := by rw [← Nat.mul_assoc, ← Nat.pow_add, ← hc_eq]

/-- **Integer Markov / Chernoff Bound:** `badCount (5 * m) * 108 ^ m ≤ 3125 ^ m`. -/
theorem badCount_five_mul_chernoff (m : Nat) :
    badCount (5 * m) * 108 ^ m ≤ 3125 ^ m := by
  rw [badCount_eq_filter_allBitVecs]
  have hmarkov := listSum_markov
    (fun v => decide (2 ^ (5 * m) ≤ 3 ^ countOnes v))
    (bitVecWeight (5 * m))
    (108 ^ m)
    (allBitVecs (5 * m))
    (fun v hv hp => by
      have hlen := (mem_allBitVecs_iff (5 * m) v).mp hv
      have hhi : countOnes v ≤ 5 * m := hlen ▸ countOnes_le_length v
      have hge : 2 ^ (5 * m) ≤ 3 ^ countOnes v := of_decide_eq_true hp
      have hlo : 3 * m ≤ countOnes v := three_pow_ge_two_pow_five_mul_imp hge
      exact one_hundred_eight_pow_le hlo hhi)
  have h5 : 5 ^ 5 = 3125 := by decide
  have hsum : listSum (bitVecWeight (5 * m)) (allBitVecs (5 * m)) = 3125 ^ m := by
    rw [bitVecWeight_allBitVecs_sum (5 * m), Nat.pow_mul, h5]
  rw [hsum] at hmarkov
  exact hmarkov

/-- **Exponential Decay Ratio (`3125 < 3456`):**
`badCount (5 * m) * 3456 ^ m ≤ 3125 ^ m * 2 ^ (5 * m)`. -/
theorem badCount_five_mul_decay (m : Nat) :
    badCount (5 * m) * 3456 ^ m ≤ 3125 ^ m * 2 ^ (5 * m) := by
  have hcher := Nat.mul_le_mul_right (2 ^ (5 * m)) (badCount_five_mul_chernoff m)
  have h3456 : 108 ^ m * 2 ^ (5 * m) = 3456 ^ m := by
    rw [Nat.pow_mul 2 5 m]
    have h25 : 2 ^ 5 = 32 := by decide
    have hmul : 108 * 32 = 3456 := by decide
    rw [h25, ← Nat.mul_pow, hmul]
  rw [Nat.mul_assoc, h3456] at hcher
  exact hcher

/-- Elementary binomial-like lower bound `(a + m) * a ^ m ≤ (a + 1) ^ m * a` for all `a, m`. -/
private theorem succ_pow_mul_ge (a m : Nat) : (a + m) * a ^ m ≤ (a + 1) ^ m * a := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hstep : (a + 1) * ((a + m) * a ^ m) ≤ (a + 1) * ((a + 1) ^ m * a) :=
      Nat.mul_le_mul_left (a + 1) ih
    have hquad : (a + (m + 1)) * a ≤ (a + 1) * (a + m) := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
      rw [Nat.mul_comm m a]
      omega
    have hmul_a : (a + (m + 1)) * a ^ (m + 1) ≤ (a + 1) * ((a + m) * a ^ m) := by
      calc (a + (m + 1)) * a ^ (m + 1)
          = ((a + (m + 1)) * a) * a ^ m := by
              rw [Nat.pow_succ, Nat.mul_comm (a ^ m) a, Nat.mul_assoc]
        _ ≤ ((a + 1) * (a + m)) * a ^ m := Nat.mul_le_mul_right (a ^ m) hquad
        _ = (a + 1) * ((a + m) * a ^ m) := Nat.mul_assoc _ _ _
    have hrhs : (a + 1) * ((a + 1) ^ m * a) = (a + 1) ^ (m + 1) * a := by
      rw [← Nat.mul_assoc, ← Nat.pow_succ', Nat.pow_succ]
    rw [hrhs] at hstep
    exact Nat.le_trans hmul_a hstep

/-- Pure-`Nat` exponential overtaking: if `0 < a < b` and `0 < D`, then there exists `m > 0`
with `a ^ m * D < b ^ m`. -/
theorem pow_mul_lt_pow_of_lt {a b D : Nat} (ha : 0 < a) (hab : a < b) (_hD : 0 < D) :
    ∃ m : Nat, 0 < m ∧ a ^ m * D < b ^ m := by
  let m := a * D + 1
  refine ⟨m, Nat.succ_pos _, ?_⟩
  have h1 : (a ^ m * D) * a < (a + m) * a ^ m := by
    have hlt : a * D < a + m := by dsimp [m]; omega
    have hpow_pos : 0 < a ^ m := Nat.pow_pos ha
    calc (a ^ m * D) * a = a * (a ^ m * D) := Nat.mul_comm _ a
      _ = (a * D) * a ^ m := by rw [← Nat.mul_assoc, Nat.mul_right_comm a (a ^ m) D]
      _ < (a + m) * a ^ m := Nat.mul_lt_mul_of_pos_right hlt hpow_pos
  have h2 := Nat.lt_of_lt_of_le h1 (succ_pow_mul_ge a m)
  have h3 : a ^ m * D < (a + 1) ^ m := Nat.lt_of_mul_lt_mul_right h2
  have h4 : (a + 1) ^ m ≤ b ^ m := Nat.pow_le_pow_left hab m
  exact Nat.lt_of_lt_of_le h3 h4

/-- **Chernoff Arbitrarily Small Bad Fraction:** for every `D > 0`, there exists `m > 0` such that
`badCount (5 * m) * D < 2 ^ (5 * m)`. -/
theorem badCount_five_mul_lt_div (D : Nat) (hD : 0 < D) :
    ∃ m : Nat, 0 < m ∧ badCount (5 * m) * D < 2 ^ (5 * m) := by
  rcases pow_mul_lt_pow_of_lt (by decide : 0 < 3125) (by decide : 3125 < 3456) hD with
    ⟨m, hm, hdom⟩
  refine ⟨m, hm, ?_⟩
  have hdec := Nat.mul_le_mul_right D (badCount_five_mul_decay m)
  have hleft : (badCount (5 * m) * D) * 3456 ^ m ≤ (3125 ^ m * D) * 2 ^ (5 * m) := by
    calc (badCount (5 * m) * D) * 3456 ^ m
        = (badCount (5 * m) * 3456 ^ m) * D := Nat.mul_right_comm _ D _
      _ ≤ (3125 ^ m * 2 ^ (5 * m)) * D := hdec
      _ = (3125 ^ m * D) * 2 ^ (5 * m) := Nat.mul_right_comm _ (2 ^ (5 * m)) D
  have hkpos : 0 < 2 ^ (5 * m) := Nat.two_pow_pos (5 * m)
  have hright : (3125 ^ m * D) * 2 ^ (5 * m) < 2 ^ (5 * m) * 3456 ^ m := by
    rw [Nat.mul_comm (3125 ^ m * D) (2 ^ (5 * m))]
    exact Nat.mul_lt_mul_of_pos_left hdom hkpos
  exact Nat.lt_of_mul_lt_mul_right (Nat.lt_of_le_of_lt hleft hright)

/-! ### 5. Full Natural Density 1 Theorems -/

/-- Exact period count of `badResidue k (n % 2 ^ k)` over `[0, 2 ^ k)`. -/
private theorem countLt_badResidue_mod_eq (k : Nat) :
    countLt (fun n => badResidue k (n % 2 ^ k)) (2 ^ k) = badCount k := by
  have h1 : countLt (fun n => badResidue k (n % 2 ^ k)) (2 ^ k) ≤ badCount k :=
    countLt_mono_pred (2 ^ k) (fun i hi h => by rw [Nat.mod_eq_of_lt hi] at h; exact h)
  have h2 : badCount k ≤ countLt (fun n => badResidue k (n % 2 ^ k)) (2 ^ k) :=
    countLt_mono_pred (2 ^ k) (fun i hi h => by rw [Nat.mod_eq_of_lt hi]; exact h)
  omega

/-- Explicit upper bound on the number of `n < N` failing `terrasIter k n < n`. -/
private theorem countLt_fails_terras_le (k N : Nat) :
    countLt (fun n => decide (¬ terrasIter k n < n)) N ≤
      2 ^ (3 * k) + badCount k * (N / 2 ^ k) + 2 ^ k := by
  have hMpos : 0 < 2 ^ k := Nat.two_pow_pos k
  let badPred : Nat → Bool := fun n => decide (n < 2 ^ (3 * k)) || badResidue k (n % 2 ^ k)
  have hmono : countLt (fun n => decide (¬ terrasIter k n < n)) N ≤ countLt badPred N := by
    refine countLt_mono_pred N (fun n _ hn => ?_)
    have hnot : ¬ terrasIter k n < n := of_decide_eq_true hn
    by_cases hsmall : n < 2 ^ (3 * k)
    · simp [badPred, hsmall]
    · have hge : 2 ^ (3 * k) ≤ n := Nat.le_of_not_lt hsmall
      by_cases hbadres : badResidue k (n % 2 ^ k) = true
      · simp [badPred, hbadres]
      · exfalso
        have hlow : 3 ^ countOnes (terrasParityVec k (n % 2 ^ k)) < 2 ^ k := by
          by_cases hge_pow : 2 ^ k ≤ 3 ^ countOnes (terrasParityVec k (n % 2 ^ k))
          · exact absurd (decide_eq_true hge_pow) hbadres
          · exact Nat.lt_of_not_le hge_pow
        exact hnot (terras_lt_of_large_low_ones hge hlow).1
  have hor := countLt_or_le (fun n => decide (n < 2 ^ (3 * k)))
    (fun n => badResidue k (n % 2 ^ k)) N
  dsimp only [badPred] at hmono
  have hsmall_bd : countLt (fun n => decide (n < 2 ^ (3 * k))) N ≤ 2 ^ (3 * k) :=
    countLt_lt_bound (2 ^ (3 * k)) N
  have hper_bd := countLt_periodic_le (fun n => badResidue k (n % 2 ^ k)) hMpos
    (badResidue_mod_periodic k) N
  rw [countLt_badResidue_mod_eq k] at hper_bd
  have hbad_le_M : badCount k ≤ 2 ^ k := countLt_le _ (2 ^ k)
  omega

/-- **Terras-Everett Density 1 (Constructive Bounded-Step Version):** for every `D > 0`, there
exist `k > 0` and `N₀` such that for all `N ≥ N₀`, the count of `n < N` failing `terrasIter k n < n`
satisfies `count * D < N`. -/
theorem terras_bounded_drop_density (D : Nat) (hD : 0 < D) :
    ∃ k N₀ : Nat, 0 < k ∧ ∀ N : Nat, N₀ ≤ N →
      countLt (fun n => decide (¬ terrasIter k n < n)) N * D < N := by
  rcases badCount_five_mul_lt_div (2 * D) (by omega) with ⟨m, hm, hbad⟩
  let k := 5 * m
  let M := 2 ^ k
  have hk : 0 < k := by dsimp [k]; omega
  have hMpos : 0 < M := Nat.two_pow_pos k
  let C := (2 ^ (3 * k) + M) * D
  let N₀ := M * (2 * C + 1)
  refine ⟨k, N₀, hk, fun N hN => ?_⟩
  let q := N / M
  have hcount_bd : countLt (fun n => decide (¬ terrasIter k n < n)) N * D ≤
      badCount k * D * q + C := by
    have hsum := countLt_fails_terras_le k N
    calc countLt (fun n => decide (¬ terrasIter k n < n)) N * D
        ≤ (2 ^ (3 * k) + badCount k * q + M) * D := Nat.mul_le_mul_right D hsum
      _ = badCount k * q * D + C := by
          dsimp [C, M, q]; rw [Nat.add_mul, Nat.add_mul, Nat.add_mul]; omega
      _ = badCount k * D * q + C := by rw [Nat.mul_right_comm (badCount k) q D]
  have hq_ge : 2 * C + 1 ≤ q := (Nat.le_div_iff_mul_le hMpos).mpr (by rw [Nat.mul_comm]; exact hN)
  have hA : 2 * (badCount k * D * q) ≤ M * q := by
    have h2 : badCount k * (2 * D) ≤ M := Nat.le_of_lt hbad
    calc 2 * (badCount k * D * q)
        = 2 * (badCount k * D) * q := (Nat.mul_assoc _ _ _).symm
      _ = (badCount k * (2 * D)) * q := by rw [Nat.mul_left_comm 2 (badCount k) D]
      _ ≤ M * q := Nat.mul_le_mul_right q h2
  have hC_lt : 2 * C < M * q := by
    have h1 : 2 * C + 1 ≤ 1 * q := by rw [Nat.one_mul]; exact hq_ge
    have h2 : 1 * q ≤ M * q := Nat.mul_le_mul_right q hMpos
    omega
  have hMq_le_N : M * q ≤ N := Nat.mul_div_le N M
  omega

/-- Exact count of natural numbers `n < N` that do not have a finite stopping time. -/
noncomputable def exceptionalCount (N : Nat) : Nat :=
  countLt (fun n => @decide (¬ HasFiniteStoppingTime n) (Classical.propDecidable _)) N

/-- Every failure of `HasFiniteStoppingTime` also fails `terrasIter k n < n` for `0 < k`. -/
theorem exceptionalCount_le_terras (k N : Nat) (hk : 0 < k) :
    exceptionalCount N ≤ countLt (fun n => decide (¬ terrasIter k n < n)) N := by
  unfold exceptionalCount
  refine countLt_mono_pred N (fun n _ hn => ?_)
  have hnot : ¬ HasFiniteStoppingTime n :=
    @of_decide_eq_true (¬ HasFiniteStoppingTime n) (Classical.propDecidable _) hn
  exact decide_eq_true (fun hlt => hnot (hasFiniteStoppingTime_of_terras_lt hk hlt))

/-- **Terras (1976) / Everett (1977) Natural Density 1 Theorem (`KNOWN-001`):**
the set of natural numbers with finite stopping time has natural density `1` — for every `D > 0`,
there exists `N₀` such that for all `N ≥ N₀`, `exceptionalCount N * D < N`. -/
theorem terras_natural_density_one (D : Nat) (hD : 0 < D) :
    ∃ N₀ : Nat, ∀ N : Nat, N₀ ≤ N → exceptionalCount N * D < N := by
  rcases terras_bounded_drop_density D hD with ⟨k, N₀, hk, hbd⟩
  refine ⟨N₀, fun N hN => ?_⟩
  have hle := Nat.mul_le_mul_right D (exceptionalCount_le_terras k N hk)
  exact Nat.lt_of_le_of_lt hle (hbd N hN)

/-- Exact count of positive integers `1 ≤ n ≤ N` that do not have a finite stopping time. -/
noncomputable def exceptionalCountPos (N : Nat) : Nat :=
  countLt
    (fun n => @decide (1 ≤ n ∧ ¬ HasFiniteStoppingTime n) (Classical.propDecidable _)) (N + 1)

/-- Natural density 1 over positive integers `1 ≤ n ≤ N`: for every `D > 0`, there exists `N₀`
such that for all `N ≥ N₀`, `exceptionalCountPos N * D < N`. -/
theorem terras_natural_density_one_pos (D : Nat) (hD : 0 < D) :
    ∃ N₀ : Nat, ∀ N : Nat, N₀ ≤ N → exceptionalCountPos N * D < N := by
  rcases terras_natural_density_one (2 * D) (by omega) with ⟨N₀, hbd⟩
  refine ⟨N₀ + 1, fun N hN => ?_⟩
  have hle_exc : exceptionalCountPos N ≤ exceptionalCount (N + 1) := by
    unfold exceptionalCountPos exceptionalCount
    refine countLt_mono_pred (N + 1) (fun n _ hn => ?_)
    have h1 : 1 ≤ n ∧ ¬ HasFiniteStoppingTime n :=
      @of_decide_eq_true (1 ≤ n ∧ ¬ HasFiniteStoppingTime n) (Classical.propDecidable _) hn
    exact @decide_eq_true (¬ HasFiniteStoppingTime n) (Classical.propDecidable _) h1.2
  have hmul : exceptionalCountPos N * (2 * D) < N + 1 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right (2 * D) hle_exc) (hbd (N + 1) (by omega))
  have hmul' : 2 * (exceptionalCountPos N * D) < N + 1 := by
    rw [← Nat.mul_assoc, Nat.mul_comm 2, Nat.mul_assoc]; exact hmul
  omega

end SolveCollatz
