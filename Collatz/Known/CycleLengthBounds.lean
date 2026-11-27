/-
Copyright (c) 2026 The solve-collatz contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Collatz.Known.SteinerCircuit
public import Collatz.Known.TerrasDensity

/-!
# Eliahou (1993) & Simons-de Weger (2005) Cycle-Length Bounds (`KNOWN-003`)

Formalization of the minimal-element Syracuse cycle inequalities of:
- S. Eliahou (1993), *The 3x+1 problem: new lower bounds on nontrivial cycle lengths*,
  Discrete Mathematics 118, pp. 45-56.
- J. Simons and B. de Weger (2005), *Theoretical and computational bounds for m-cycles of the
  3n+1-problem*, Acta Arithmetica 117, pp. 51-70.

Main results (pure Lean 4 core, zero Mathlib):
1. Minimal-element `SyracuseCycle` framework on `n_min`, bridged to `HasNontrivialCycle`.
2. Exact Eliahou product identity `∏_{i < k} (3 * n_i + 1) = 2 ^ S * ∏_{i < k} n_i`,
   `3 ^ k < 2 ^ S`, and strict upper bound `2 ^ S * M ^ k < (3 * M + 1) ^ k` (`0 < M ≤ n_min`).
3. Gap bounds: `(2^S - 3^k) * M^k < (3M+1)^k - (3M)^k`, `(2^S - 3^k)(3M - k) < k * 3^k` (`k ≤ 3M`),
   unconditional `3M(2^S - 3^k) < k * 2^S`, and elementary `M < k * 4^(k - 1)`.
4. Kernel-verified elimination (`decide`, zero `native_decide`): `M = 1000` (`k ≥ 41`, `len ≥ 106`)
   and `M = 10^6` (`k ≥ 1001`, `len ≥ 2588`), bridged to `HasNontrivialCycle` and
   `HasFiniteStoppingTime` (note fixed-`m`-circuit Baker reductions live in `PROVE-B1`).
-/

@[expose] public section

namespace SolveCollatz

/-! ### 1. Pure-`Nat` Products, Minimum Helpers, and Elementary Inequalities -/

/-- Finite product `∏_{i < k} f i` in `ℕ`. -/
def natProd : Nat → (Nat → Nat) → Nat
  | 0, _ => 1
  | k + 1, f => natProd k f * f k

/-- A finite product of positive natural numbers is positive. -/
theorem natProd_pos (k : Nat) (f : Nat → Nat) (hf : ∀ i : Nat, i < k → 0 < f i) :
    0 < natProd k f := by
  induction k with
  | zero => simp [natProd]
  | succ k ih =>
    exact Nat.mul_pos (ih (fun i hi => hf i (Nat.lt_succ_of_lt hi))) (hf k (Nat.lt_succ_self k))

/-- Left-peeling rule for `natProd (k + 1) f`. -/
theorem natProd_succ_left (k : Nat) (f : Nat → Nat) :
    natProd (k + 1) f = f 0 * natProd k (fun i => f (i + 1)) := by
  induction k with
  | zero => simp [natProd]
  | succ k ih => simp only [natProd] at ih ⊢; rw [ih, Nat.mul_assoc]

/-- Along a periodic function `f k = f 0` (`0 < k`), shifting `natProd` by `1` preserves it. -/
theorem natProd_shift_cycle {k : Nat} (hk : 0 < k) (f : Nat → Nat) (hcyc : f k = f 0) :
    natProd k (fun i => f (i + 1)) = natProd k f := by
  cases k with
  | zero => exact absurd hk (Nat.lt_irrefl 0)
  | succ m =>
    calc natProd (m + 1) (fun i => f (i + 1)) = natProd m (fun i => f (i + 1)) * f (m + 1) := rfl
      _ = f 0 * natProd m (fun i => f (i + 1)) := by rw [hcyc, Nat.mul_comm]
      _ = natProd (m + 1) f := (natProd_succ_left m f).symm

/-- Pointwise `f i * b ≤ c * g i` lifts to `natProd k f * b ^ k ≤ c ^ k * natProd k g`. -/
theorem natProd_mul_le_mul (k b c : Nat) (f g : Nat → Nat)
    (hle : ∀ i : Nat, i < k → f i * b ≤ c * g i) : natProd k f * b ^ k ≤ c ^ k * natProd k g := by
  induction k with
  | zero => simp [natProd]
  | succ k ih =>
    have hprev := ih (fun i hi => hle i (Nat.lt_succ_of_lt hi))
    have hstep := hle k (Nat.lt_succ_self k)
    calc natProd (k + 1) f * b ^ (k + 1)
        = (natProd k f * b ^ k) * (f k * b) := by simp only [natProd, Nat.pow_succ]; ac_rfl
      _ ≤ (c ^ k * natProd k g) * (c * g k) := Nat.mul_le_mul hprev hstep
      _ = c ^ (k + 1) * natProd (k + 1) g := by simp only [natProd, Nat.pow_succ]; ac_rfl

/-- Strict pointwise cross-multiplication at one index yields strict product inequality
`natProd k f * b ^ k < c ^ k * natProd k g`. -/
theorem natProd_mul_lt_mul (k b c : Nat) (f g : Nat → Nat)
    (hb : 0 < b) (hf : ∀ i : Nat, i < k → 0 < f i)
    (hle : ∀ i : Nat, i < k → f i * b ≤ c * g i)
    (hlt : ∃ i₀ : Nat, i₀ < k ∧ f i₀ * b < c * g i₀) :
    natProd k f * b ^ k < c ^ k * natProd k g := by
  induction k with
  | zero => rcases hlt with ⟨i₀, hi₀, _⟩; exact absurd hi₀ (Nat.not_lt_zero i₀)
  | succ k ih =>
    have hprev_le := natProd_mul_le_mul k b c f g (fun i hi => hle i (Nat.lt_succ_of_lt hi))
    have hstep_le := hle k (Nat.lt_succ_self k)
    have hlpos : 0 < natProd k f * b ^ k :=
      Nat.mul_pos (natProd_pos k f (fun i hi => hf i (Nat.lt_succ_of_lt hi))) (Nat.pow_pos hb)
    have hmul : natProd (k + 1) f * b ^ (k + 1) = (natProd k f * b ^ k) * (f k * b) := by
      simp only [natProd, Nat.pow_succ]; ac_rfl
    have hmul' : c ^ (k + 1) * natProd (k + 1) g = (c ^ k * natProd k g) * (c * g k) := by
      simp only [natProd, Nat.pow_succ]; ac_rfl
    rw [hmul, hmul']
    rcases hlt with ⟨i₀, hi₀, hstrict⟩
    by_cases heq : i₀ = k
    · subst heq
      exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ hprev_le)
        (Nat.mul_lt_mul_of_pos_left hstrict (Nat.lt_of_lt_of_le hlpos hprev_le))
    · have hprev_lt := ih (fun i hi => hf i (Nat.lt_succ_of_lt hi))
        (fun i hi => hle i (Nat.lt_succ_of_lt hi))
        ⟨i₀, by omega, hstrict⟩
      exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hprev_lt
        (Nat.mul_pos (hf k (Nat.lt_succ_self k)) hb)) (Nat.mul_le_mul_left _ hstep_le)

/-- Minimum of `f 0, f 1, ..., f k`. -/
def minFinVal (f : Nat → Nat) : Nat → Nat
  | 0 => f 0
  | k + 1 => min (minFinVal f k) (f (k + 1))

/-- Every `f j` with `j ≤ k` is at least `minFinVal f k`. -/
theorem minFinVal_le (f : Nat → Nat) (k j : Nat) (hj : j ≤ k) : minFinVal f k ≤ f j := by
  induction k with
  | zero => rw [show j = 0 by omega]; exact Nat.le_refl _
  | succ k ih =>
    by_cases hjk : j ≤ k
    · exact Nat.le_trans (Nat.min_le_left _ _) (ih hjk)
    · rw [show j = k + 1 by omega]; exact Nat.min_le_right _ _

/-- The minimum `minFinVal f k` is attained at some index `j ≤ k`. -/
theorem minFinVal_mem (f : Nat → Nat) (k : Nat) :
    ∃ j : Nat, j ≤ k ∧ minFinVal f k = f j := by
  induction k with
  | zero => exact ⟨0, Nat.le_refl 0, rfl⟩
  | succ k ih =>
    rcases ih with ⟨j, hj, hmin⟩
    by_cases hle : minFinVal f k ≤ f (k + 1)
    · exact ⟨j, Nat.le_succ_of_le hj, by rw [minFinVal, Nat.min_eq_left hle, hmin]⟩
    · exact ⟨k + 1, Nat.le_refl (k + 1), by simp only [minFinVal, Nat.min_eq_right
        (Nat.le_of_not_ge hle)]⟩

/-- For every `d : Nat`, `2 ^ d ≤ 3 ^ d`. -/
theorem two_pow_le_three_pow (d : Nat) : 2 ^ d ≤ 3 ^ d := by
  cases d with
  | zero => decide
  | succ d => exact Nat.le_of_lt (two_pow_lt_three_pow (Nat.succ_pos d))

/-- Reverse-Bernoulli inequality on `ℕ`: `(N + 1) ^ k * (N - k) ≤ N ^ (k + 1)` for `k ≤ N`. -/
theorem succ_pow_mul_sub_le (N k : Nat) (hk : k ≤ N) :
    (N + 1) ^ k * (N - k) ≤ N ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hprev := ih (by omega)
    have hstep : (N + 1) * (N - (k + 1)) ≤ N * (N - k) := by
      have hsub : N - k = (N - (k + 1)) + 1 := by omega
      rw [hsub, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]; omega
    calc (N + 1) ^ (k + 1) * (N - (k + 1))
        = (N + 1) ^ k * ((N + 1) * (N - (k + 1))) := by rw [Nat.pow_succ, Nat.mul_assoc]
      _ ≤ (N + 1) ^ k * (N * (N - k)) := Nat.mul_le_mul_left _ hstep
      _ = N * ((N + 1) ^ k * (N - k)) := by rw [Nat.mul_left_comm]
      _ ≤ N * N ^ (k + 1) := Nat.mul_le_mul_left _ hprev
      _ = N ^ (k + 2) := (Nat.pow_succ N (k + 1)).symm ▸ Nat.mul_comm N (N ^ (k + 1))

/-- Difference-of-powers identity:
`b ^ (k + 1) - a ^ (k + 1) = b ^ k * (b - a) + a * (b ^ k - a ^ k)` for `a ≤ b`. -/
theorem pow_succ_sub_pow_succ (a b k : Nat) (hab : a ≤ b) :
    b ^ (k + 1) - a ^ (k + 1) = b ^ k * (b - a) + a * (b ^ k - a ^ k) := by
  have hapow : a ^ k ≤ b ^ k := Nat.pow_le_pow_left hab k
  have h1 : b ^ (k + 1) = a ^ (k + 1) + (b ^ k * (b - a) + a * (b ^ k - a ^ k)) := by
    calc b ^ (k + 1) = b ^ k * (a + (b - a)) := by rw [Nat.pow_succ, Nat.add_sub_of_le hab]
      _ = b ^ k * a + b ^ k * (b - a) := Nat.mul_add _ _ _
      _ = (a ^ k + (b ^ k - a ^ k)) * a + b ^ k * (b - a) := by rw [Nat.add_sub_of_le hapow]
      _ = a ^ (k + 1) + (b ^ k * (b - a) + a * (b ^ k - a ^ k)) := by
            rw [Nat.add_mul, Nat.pow_succ, Nat.mul_comm (b ^ k - a ^ k) a]; omega
  omega

/-- Difference-of-powers upper bound: `b ^ k - a ^ k ≤ k * b ^ (k - 1) * (b - a)` for `a ≤ b`. -/
theorem pow_sub_pow_le (a b k : Nat) (hab : a ≤ b) :
    b ^ k - a ^ k ≤ k * b ^ (k - 1) * (b - a) := by
  induction k with
  | zero => simp
  | succ k ih =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [Nat.add_sub_cancel] at ih ⊢
      have h2 : a * (b ^ (k + 1) - a ^ (k + 1)) ≤ (k + 1) * b ^ (k + 1) * (b - a) := by
        have hmul := Nat.mul_le_mul hab ih
        rwa [show b * ((k + 1) * b ^ k * (b - a)) = (k + 1) * b ^ (k + 1) * (b - a) by
          rw [Nat.pow_succ]; ac_rfl] at hmul
      calc b ^ (k + 2) - a ^ (k + 2)
          = b ^ (k + 1) * (b - a) + a * (b ^ (k + 1) - a ^ (k + 1)) :=
              pow_succ_sub_pow_succ a b (k + 1) hab
        _ ≤ b ^ (k + 1) * (b - a) + (k + 1) * b ^ (k + 1) * (b - a) :=
              Nat.add_le_add_left h2 _
        _ = (k + 2) * b ^ (k + 1) * (b - a) := by
              rw [show k + 2 = 1 + (k + 1) by omega, Nat.add_mul 1 (k + 1), Nat.one_mul,
                Nat.add_mul (b ^ (k + 1))]

/-! ### 2. Minimal-Element `SyracuseCycle` Framework & Bridge to `HasNontrivialCycle` -/

/-- Minimal-element `SyracuseCycle` anchored at `n_min` (`1 < n_min`, odd, `k` steps). -/
structure SyracuseCycle where
  /-- Minimum element along the cycle (`1 < n_min` and `n_min` is odd). -/
  n_min : Nat
  /-- Number of odd Syracuse steps in one full period (`0 < k`). -/
  k : Nat
  /-- Non-triviality `1 < n_min`. -/ one_lt : 1 < n_min
  /-- Minimality forces `n_min` odd. -/ odd : n_min % 2 = 1
  /-- Period positivity `0 < k`. -/ k_pos : 0 < k
  /-- Periodicity under `k` steps. -/ cycle : syracuseIter k n_min = n_min
  /-- Orbit-wide minimality of `n_min`. -/ min_le : ∀ i : Nat, n_min ≤ syracuseIter i n_min

/-- Positivity of `C.n_min`. -/
theorem SyracuseCycle.pos (C : SyracuseCycle) : 0 < C.n_min := by have := C.one_lt; omega
/-- Total number of halvings `S` in one full period of `C`. -/
def SyracuseCycle.totalVal (C : SyracuseCycle) : Nat := syracuseTotalVal C.k C.n_min
/-- Total number of standard Collatz steps `k + S` in one full period of `C`. -/
def SyracuseCycle.collatzLen (C : SyracuseCycle) : Nat := C.totalVal + C.k
/-- Archimedean power lower bound `3 ^ k < 2 ^ S` for any `SyracuseCycle`. -/
theorem SyracuseCycle.pow_lt (C : SyracuseCycle) : 3 ^ C.k < 2 ^ C.totalVal :=
  syracuse_cycle_pow_lt C.k_pos C.cycle

/-- The first Syracuse iterate strictly exceeds `n_min` (`n_min < syracuseStep n_min`), since a
1-step cycle forces `n_min = 1`. -/
theorem SyracuseCycle.n_min_lt_step (C : SyracuseCycle) : C.n_min < syracuseStep C.n_min := by
  by_cases hlt : C.n_min < syracuseStep C.n_min
  · exact hlt
  · have heq : syracuseIter 1 C.n_min = C.n_min := by
      have := C.min_le 1; simpa [syracuseIter] using Nat.le_antisymm (Nat.le_of_not_lt hlt) this
    have hcyc := syracuse_cycle_equation heq
    have hpow := syracuse_cycle_pow_lt (by decide : 0 < 1) heq
    simp only [syracuseOffset, Nat.pow_one, Nat.pow_zero] at hcyc hpow
    have hm := Nat.mul_le_mul_left (2 ^ syracuseTotalVal 1 C.n_min - 3)
      (by have := C.one_lt; omega : 2 ≤ C.n_min)
    omega

/-- Every non-trivial `SyracuseCycle` has at least `2` odd steps (`2 ≤ C.k`). -/
theorem SyracuseCycle.two_le_k (C : SyracuseCycle) : 2 ≤ C.k := by
  by_cases h2 : 2 ≤ C.k
  · exact h2
  · have hk1 : C.k = 1 := by have := C.k_pos; omega
    have hcyc : syracuseStep C.n_min = C.n_min := by
      have h := C.cycle; rw [hk1] at h; simpa [syracuseIter] using h
    have hlt := C.n_min_lt_step; omega

/-- **Track B Bridge (`SyracuseCycle → HasNontrivialCycle`):** every `SyracuseCycle` yields a
`HasNontrivialCycle` witness in frozen `Challenge.lean`. -/
theorem SyracuseCycle.hasNontrivialCycle (C : SyracuseCycle) : HasNontrivialCycle := by
  refine hasNontrivialCycle_of_syracuse_cycle C.k_pos C.cycle ?_
  intro i _; have hge := C.min_le i; have h1 := C.one_lt; omega

/-- Total standard Collatz steps elapsed after `i` Syracuse steps starting from `n`. -/
def syracuseTime (i n : Nat) : Nat := syracuseTotalVal i n + i

/-- Any standard Collatz iterate strictly between `syracuseTime i n` and `syracuseTime (i + 1) n`
equals `syracuseStep (syracuseIter i n) * 2 ^ (v - r)` for some `r < v`. -/
theorem collatzIter_between_syracuseTime {i n t : Nat} (hn : n % 2 = 1)
    (hlo : syracuseTime i n < t) (hhi : t < syracuseTime (i + 1) n) :
    ∃ r : Nat, r < syracuseVal (syracuseIter i n) ∧ collatzIter t n =
      syracuseStep (syracuseIter i n) * 2 ^ (syracuseVal (syracuseIter i n) - r) := by
  let m := syracuseIter i n
  have hadd : syracuseTotalVal (i + 1) n = syracuseTotalVal i n + syracuseVal m := by
    rw [syracuseTotalVal_add i 1 n]; simp [syracuseTotalVal, m]
  let r := t - syracuseTime i n - 1
  simp only [syracuseTime] at hlo hhi; rw [hadd] at hhi
  have hr_lt : r < syracuseVal m := by simp only [r, syracuseTime]; omega
  have hm_odd : m % 2 = 1 := syracuseIter_odd_of_odd i hn
  refine ⟨r, hr_lt, ?_⟩
  rw [show t = syracuseTime i n + (r + 1) by simp only [r, syracuseTime]; omega,
    ← collatzIter_add, show syracuseTime i n = syracuseTotalVal i n + i from rfl,
    collatzIter_eq_syracuseIter i hn, collatzIter,
    show collatzStep m = 3 * m + 1 from by rw [collatzStep, ite_eq_right (by omega)]]
  conv => lhs; rw [← oddPart_mul_two_pow (3 * m + 1)]
  exact collatzIter_mul_two_pow_sub (syracuseStep m) (syracuseVal m) r (Nat.le_of_lt hr_lt)

/-- Any standard Collatz iterate strictly between `syracuseTime i n` and `syracuseTime (i + 1) n`
is even. -/
theorem collatzIter_between_syracuseTime_even {i n t : Nat} (hn : n % 2 = 1)
    (hlo : syracuseTime i n < t) (hhi : t < syracuseTime (i + 1) n) :
    collatzIter t n % 2 = 0 := by
  rcases collatzIter_between_syracuseTime hn hlo hhi with ⟨r, hr_lt, heq⟩
  rw [heq, show syracuseVal (syracuseIter i n) - r =
    (syracuseVal (syracuseIter i n) - r - 1) + 1 from by omega, Nat.pow_succ, ← Nat.mul_assoc]
  omega

/-- Existence of a Syracuse return step count `k > 0` hitting an odd Collatz period `K > 0`. -/
theorem exists_syracuseTime_eq {n K : Nat} (hn : n % 2 = 1) (hK : 0 < K)
    (hoddK : collatzIter K n % 2 = 1) : ∃ k : Nat, 0 < k ∧ syracuseTime k n = K := by
  have hex : ∀ m : Nat, K ≤ syracuseTime m n → ∃ k : Nat, 0 < k ∧ syracuseTime k n = K := by
    intro m; induction m with
    | zero => intro hle; simp only [syracuseTime, syracuseTotalVal] at hle; omega
    | succ m ih =>
      intro hle
      by_cases hprev : K ≤ syracuseTime m n
      · exact ih hprev
      · have hlo : syracuseTime m n < K := Nat.lt_of_not_ge hprev
        by_cases heq : syracuseTime (m + 1) n = K
        · exact ⟨m + 1, Nat.succ_pos m, heq⟩
        · have heven := collatzIter_between_syracuseTime_even hn hlo (by omega); omega
  exact hex K (by have := syracuseTotalVal_ge K hn; simp only [syracuseTime]; omega)

/-- Extract `n_min` and its Collatz orbit invariants from a non-trivial Collatz cycle. -/
theorem minCycleWitness {n K : Nat} (hn : 0 < n) (hK : 0 < K)
    (hcyc : collatzIter K n = n) (hne : ∀ j : Nat, j < K → collatzIter j n ≠ 1) :
    ∃ n_min : Nat, 1 < n_min ∧ n_min % 2 = 1 ∧ collatzIter K n_min = n_min ∧
      ∀ t : Nat, n_min ≤ collatzIter t n_min := by
  let f := fun j => collatzIter j n
  rcases minFinVal_mem f (K - 1) with ⟨j₀, _, hmin_eq⟩
  let n_min := minFinVal f (K - 1)
  have hmin_eq' : n_min = collatzIter j₀ n := hmin_eq
  have hfor_t : ∀ t : Nat, n_min ≤ collatzIter t n_min ∧ collatzIter t n_min ≠ 1 := by
    intro t
    have heq : collatzIter t n_min = f ((j₀ + t) % K) := by
      rw [hmin_eq', collatzIter_add, collatzIter_mod_of_cycle hK hcyc]
    rw [heq]
    exact ⟨minFinVal_le f (K - 1) _ (by have := Nat.mod_lt (j₀ + t) hK; omega),
      hne _ (Nat.mod_lt _ hK)⟩
  have hpos : 0 < n_min := by rw [hmin_eq']; exact collatzIter_pos j₀ hn
  have h1 : 1 < n_min := by have hne0 := (hfor_t 0).2; simp [collatzIter] at hne0; omega
  have hodd : n_min % 2 = 1 := by
    by_cases ho : n_min % 2 = 1
    · exact ho
    · have hstep : collatzIter 1 n_min = n_min / 2 := by
        simp [collatzIter, collatzStep, show n_min % 2 = 0 by omega]
      have hge1 := (hfor_t 1).1; omega
  have hcyc' : collatzIter K n_min = n_min := by
    calc collatzIter K n_min = collatzIter (j₀ + K) n := by rw [hmin_eq', collatzIter_add]
      _ = collatzIter j₀ (collatzIter K n) := by
            rw [Nat.add_comm]; exact (collatzIter_add K j₀ n).symm
      _ = n_min := by rw [hcyc, hmin_eq']
  exact ⟨n_min, h1, hodd, hcyc', fun t => (hfor_t t).1⟩

/-- Every non-trivial Collatz cycle `(n, K)` yields a `SyracuseCycle` with `C.collatzLen = K`. -/
theorem exists_syracuseCycle_of_collatz_cycle {n K : Nat} (hn : 0 < n) (hK : 0 < K)
    (hcyc : collatzIter K n = n) (hne : ∀ j : Nat, j < K → collatzIter j n ≠ 1) :
    ∃ C : SyracuseCycle, C.collatzLen = K := by
  rcases minCycleWitness hn hK hcyc hne with ⟨n_min, h1, hodd, hcyc', hmin⟩
  rcases exists_syracuseTime_eq hodd hK (by rw [hcyc']; exact hodd) with ⟨k, hk, htime⟩
  have hscyc : syracuseIter k n_min = n_min := by
    rw [← collatzIter_eq_syracuseIter k hodd, show syracuseTotalVal k n_min + k = K from htime]
    exact hcyc'
  exact ⟨⟨n_min, k, h1, hodd, hk, hscyc,
    fun i => by rw [← collatzIter_eq_syracuseIter i hodd]; exact hmin _⟩, htime⟩

/-- **Equivalence with Frozen `Challenge.lean`:** `HasNontrivialCycle` holds if and only if
there exists a minimal-element `SyracuseCycle`. -/
theorem hasNontrivialCycle_iff_nonempty_syracuseCycle :
    HasNontrivialCycle ↔ Nonempty SyracuseCycle := by
  constructor
  · rintro ⟨n, K, hn, hK, hcyc, hne⟩
    rcases exists_syracuseCycle_of_collatz_cycle hn hK hcyc hne with ⟨C, _⟩; exact ⟨C⟩
  · rintro ⟨C⟩; exact C.hasNontrivialCycle

/-! ### 3. Eliahou (1993) Product Identity & Two-Sided Integer Bounds -/

/-- Stepwise product identity along any `k` Syracuse steps starting from `n`:
`∏_{i < k} (3 * n_i + 1) = 2 ^ S * ∏_{i < k} n_{i+1}`. -/
theorem syracuse_prod_step_eq (k n : Nat) :
    natProd k (fun i => 3 * syracuseIter i n + 1) =
      2 ^ syracuseTotalVal k n * natProd k (fun i => syracuseIter (i + 1) n) := by
  induction k with
  | zero => simp [natProd, syracuseTotalVal]
  | succ k ih =>
    have hval : syracuseTotalVal (k + 1) n =
        syracuseTotalVal k n + syracuseVal (syracuseIter k n) := by
      rw [syracuseTotalVal_add k 1 n]; simp [syracuseTotalVal]
    have hstep : 3 * syracuseIter k n + 1 =
        2 ^ syracuseVal (syracuseIter k n) * syracuseIter (k + 1) n := by
      rw [syracuseIter_succ_right]; exact (two_pow_mul_syracuseStep (syracuseIter k n)).symm
    calc natProd (k + 1) (fun i => 3 * syracuseIter i n + 1)
        = natProd k (fun i => 3 * syracuseIter i n + 1) * (3 * syracuseIter k n + 1) := rfl
      _ = (2 ^ syracuseTotalVal k n * natProd k (fun i => syracuseIter (i + 1) n)) *
            (2 ^ syracuseVal (syracuseIter k n) * syracuseIter (k + 1) n) := by rw [ih, hstep]
      _ = 2 ^ syracuseTotalVal (k + 1) n *
            natProd (k + 1) (fun i => syracuseIter (i + 1) n) := by
            rw [hval, Nat.pow_add]; simp only [natProd]; ac_rfl

/-- **Eliahou (1993) Product Identity:** `∏_{i < k} (3 * n_i + 1) = 2 ^ S * ∏_{i < k} n_i`. -/
theorem eliahou_product_eq (C : SyracuseCycle) :
    natProd C.k (fun i => 3 * syracuseIter i C.n_min + 1) =
      2 ^ C.totalVal * natProd C.k (fun i => syracuseIter i C.n_min) := by
  rw [syracuse_prod_step_eq]
  simpa [SyracuseCycle.totalVal] using congrArg (fun p => 2 ^ C.totalVal * p)
    (natProd_shift_cycle C.k_pos (fun i => syracuseIter i C.n_min) C.cycle)

/-- Cross-multiplication monotonicity: `m ≤ n → (3 * n + 1) * m ≤ (3 * m + 1) * n`. -/
theorem eliahou_cross_mul_le {m n : Nat} (hle : m ≤ n) : (3 * n + 1) * m ≤ (3 * m + 1) * n := by
  rw [Nat.add_mul, Nat.add_mul, Nat.one_mul, Nat.one_mul]
  have hmul : 3 * n * m = 3 * m * n := by ac_rfl
  omega

/-- Strict cross-multiplication: `m < n → (3 * n + 1) * m < (3 * m + 1) * n`. -/
theorem eliahou_cross_mul_lt {m n : Nat} (hlt : m < n) : (3 * n + 1) * m < (3 * m + 1) * n := by
  rw [Nat.add_mul, Nat.add_mul, Nat.one_mul, Nat.one_mul]
  have hmul : 3 * n * m = 3 * m * n := by ac_rfl
  omega

/-- **Eliahou (1993) Upper Bound (Lower-Threshold Form):** for `0 < M ≤ C.n_min`,
`2 ^ S * M ^ k < (3 * M + 1) ^ k`. -/
theorem eliahou_upper_bound_lt (C : SyracuseCycle) {M : Nat}
    (hMpos : 0 < M) (hM : M ≤ C.n_min) : 2 ^ C.totalVal * M ^ C.k < (3 * M + 1) ^ C.k := by
  let f := fun i => 3 * syracuseIter i C.n_min + 1
  let g := fun i => syracuseIter i C.n_min
  have hprod_lt := natProd_mul_lt_mul C.k M (3 * M + 1) f g hMpos
    (fun _ _ => Nat.succ_pos _)
    (fun i _ => eliahou_cross_mul_le (Nat.le_trans hM (C.min_le i)))
    ⟨1, C.two_le_k, eliahou_cross_mul_lt (Nat.lt_of_le_of_lt hM
      (by simpa [g, syracuseIter] using C.n_min_lt_step))⟩
  have hmul_lt : (2 ^ C.totalVal * M ^ C.k) * natProd C.k g <
      (3 * M + 1) ^ C.k * natProd C.k g := by
    calc (2 ^ C.totalVal * M ^ C.k) * natProd C.k g
        = (2 ^ C.totalVal * natProd C.k g) * M ^ C.k := by ac_rfl
      _ = natProd C.k f * M ^ C.k := by rw [← eliahou_product_eq C]
      _ < (3 * M + 1) ^ C.k * natProd C.k g := hprod_lt
  exact Nat.lt_of_mul_lt_mul_right hmul_lt

/-- **Eliahou (1993) Upper Bound (Exact `n_min` Form):**
`2 ^ S * n_min ^ k < (3 * n_min + 1) ^ k`. -/
theorem eliahou_n_min_bound (C : SyracuseCycle) :
    2 ^ C.totalVal * C.n_min ^ C.k < (3 * C.n_min + 1) ^ C.k :=
  eliahou_upper_bound_lt C C.pos (Nat.le_refl C.n_min)

/-! ### 4. Eliahou & Simons-de Weger Gap / Cycle-Length Inequalities -/

/-- **Eliahou Gap Bound:** for any `0 < M ≤ C.n_min`,
`(2 ^ S - 3 ^ k) * M ^ k < (3 * M + 1) ^ k - 3 ^ k * M ^ k`. -/
theorem eliahou_gap_bound (C : SyracuseCycle) {M : Nat}
    (hMpos : 0 < M) (hM : M ≤ C.n_min) :
    (2 ^ C.totalVal - 3 ^ C.k) * M ^ C.k < (3 * M + 1) ^ C.k - 3 ^ C.k * M ^ C.k := by
  have hub := eliahou_upper_bound_lt C hMpos hM
  have hle : 3 ^ C.k * M ^ C.k ≤ 2 ^ C.totalVal * M ^ C.k :=
    Nat.mul_le_mul_right _ (Nat.le_of_lt C.pow_lt)
  rw [Nat.sub_mul]; omega

/-- **Eliahou Sub-`k` Gap Inequality (`k ≤ 3 * M`):**
`(2 ^ S - 3 ^ k) * (3 * M - k) < k * 3 ^ k`. -/
theorem eliahou_sub_k_gap_bound (C : SyracuseCycle) {M : Nat}
    (hMpos : 0 < M) (hM : M ≤ C.n_min) (hk : C.k ≤ 3 * M) :
    (2 ^ C.totalVal - 3 ^ C.k) * (3 * M - C.k) < C.k * 3 ^ C.k := by
  by_cases heq : C.k = 3 * M
  · have h3pos : 0 < 3 ^ C.k := Nat.pow_pos (by decide)
    rw [heq]; simp; exact Nat.mul_pos (by have := C.k_pos; omega) (by rw [← heq]; exact h3pos)
  · have hsub_pos : 0 < 3 * M - C.k := by omega
    have hcomb : (2 ^ C.totalVal * (3 * M - C.k)) * M ^ C.k < (3 * M * 3 ^ C.k) * M ^ C.k := by
      calc (2 ^ C.totalVal * (3 * M - C.k)) * M ^ C.k
          = (2 ^ C.totalVal * M ^ C.k) * (3 * M - C.k) := by ac_rfl
        _ < (3 * M + 1) ^ C.k * (3 * M - C.k) :=
            Nat.mul_lt_mul_of_pos_right (eliahou_upper_bound_lt C hMpos hM) hsub_pos
        _ ≤ (3 * M) ^ (C.k + 1) := succ_pow_mul_sub_le (3 * M) C.k hk
        _ = (3 * M * 3 ^ C.k) * M ^ C.k := by rw [Nat.pow_succ, Nat.mul_pow]; ac_rfl
    have h2lt : 2 ^ C.totalVal * (3 * M - C.k) < 3 * M * 3 ^ C.k :=
      Nat.lt_of_mul_lt_mul_right hcomb
    have h3eq : 3 * M * 3 ^ C.k - 3 ^ C.k * (3 * M - C.k) = C.k * 3 ^ C.k := by
      rw [Nat.mul_comm (3 * M) (3 ^ C.k), ← Nat.mul_sub (3 ^ C.k),
        show 3 * M - (3 * M - C.k) = C.k by omega, Nat.mul_comm]
    have hle : 3 ^ C.k * (3 * M - C.k) ≤ 2 ^ C.totalVal * (3 * M - C.k) :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt C.pow_lt)
    rw [Nat.sub_mul]; omega

/-- **Unconditional Eliahou/Simons-de Weger Linear Gap Bound (All `k`):**
`3 * M * (2 ^ S - 3 ^ k) < k * 2 ^ S`. -/
theorem eliahou_universal_gap_bound (C : SyracuseCycle) {M : Nat}
    (hMpos : 0 < M) (hM : M ≤ C.n_min) :
    3 * M * (2 ^ C.totalVal - 3 ^ C.k) < C.k * 2 ^ C.totalVal := by
  by_cases hk : C.k ≤ 3 * M
  · have hsub := eliahou_sub_k_gap_bound C hMpos hM hk
    have hadd : 3 * M * (2 ^ C.totalVal - 3 ^ C.k) =
        (2 ^ C.totalVal - 3 ^ C.k) * (3 * M - C.k) + C.k * (2 ^ C.totalVal - 3 ^ C.k) := by
      rw [Nat.mul_comm (3 * M), Nat.mul_comm C.k, ← Nat.mul_add, Nat.sub_add_cancel hk]
    have hrhs : C.k * 3 ^ C.k + C.k * (2 ^ C.totalVal - 3 ^ C.k) = C.k * 2 ^ C.totalVal := by
      rw [← Nat.mul_add, Nat.add_sub_of_le (Nat.le_of_lt C.pow_lt)]
    omega
  · have hgt : 3 * M < C.k := Nat.lt_of_not_ge hk
    have hpow := C.pow_lt; have h3pos : 0 < 3 ^ C.k := Nat.pow_pos (by decide)
    exact Nat.lt_trans (Nat.mul_lt_mul_of_pos_left (by omega) (by omega))
      (Nat.mul_lt_mul_of_pos_right hgt (Nat.two_pow_pos _))

/-- **Elementary Exponential Cycle-Length Bound:** for `0 < M ≤ C.n_min`, `M < k * 4 ^ (k - 1)`. -/
theorem eliahou_elementary_k_bound (C : SyracuseCycle) {M : Nat}
    (hMpos : 0 < M) (hM : M ≤ C.n_min) : M < C.k * 4 ^ (C.k - 1) := by
  have h1 : M ^ C.k ≤ (2 ^ C.totalVal - 3 ^ C.k) * M ^ C.k := by
    have hpos : 0 < 2 ^ C.totalVal - 3 ^ C.k := by have := C.pow_lt; omega
    simpa [Nat.one_mul] using Nat.mul_le_mul_right (M ^ C.k) hpos
  have hdiff := pow_sub_pow_le (3 * M) (3 * M + 1) C.k (by omega)
  rw [Nat.mul_pow, show 3 * M + 1 - 3 * M = 1 by omega, Nat.mul_one] at hdiff
  have hcomb : M ^ C.k < C.k * 4 ^ (C.k - 1) * M ^ (C.k - 1) := by
    calc M ^ C.k < (3 * M + 1) ^ C.k - 3 ^ C.k * M ^ C.k :=
          Nat.lt_of_le_of_lt h1 (eliahou_gap_bound C hMpos hM)
      _ ≤ C.k * (3 * M + 1) ^ (C.k - 1) := hdiff
      _ ≤ C.k * (4 * M) ^ (C.k - 1) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ = C.k * 4 ^ (C.k - 1) * M ^ (C.k - 1) := by rw [Nat.mul_pow, Nat.mul_assoc]
  have hsplit : M ^ C.k = M * M ^ (C.k - 1) := by
    have hk := C.k_pos
    conv => lhs; rw [show C.k = (C.k - 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
  rw [hsplit] at hcomb; exact Nat.lt_of_mul_lt_mul_right hcomb

/-! ### 5. Kernel-Verified Small-`k` Elimination & Bridges to `HasNontrivialCycle` -/

/-- Linking lemma to `SteinerCircuit.minHalvings`: if `3 ^ k < 2 ^ S` (`0 < k`), then
`minHalvings k ≤ S`. -/
theorem minHalvings_le_of_three_pow_lt {k S : Nat} (hk : 0 < k) (hpow : 3 ^ k < 2 ^ S) :
    minHalvings k ≤ S := by
  by_cases hle : minHalvings k ≤ S
  · exact hle
  · have hpow2 := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : S + 1 ≤ minHalvings k)
    have hup := two_pow_minHalvings_lt_two_mul hk
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ S) 2] at hpow2; omega

/-- Lower bound on total Collatz cycle length `C.collatzLen` from `k₀ ≤ C.k` and a witness
`2 ^ s₀ ≤ 3 ^ k₀` (yielding `k₀ + (s₀ + 1) ≤ C.collatzLen`). -/
theorem collatzLen_ge_of_k_ge (C : SyracuseCycle) (k₀ s₀ : Nat)
    (hk : k₀ ≤ C.k) (hpow : 2 ^ s₀ ≤ 3 ^ k₀) : k₀ + (s₀ + 1) ≤ C.collatzLen := by
  let d := C.k - k₀
  have hsplit : C.k = k₀ + d := (Nat.add_sub_of_le hk).symm
  have hlt : 2 ^ (s₀ + d) < 2 ^ C.totalVal := by
    calc 2 ^ (s₀ + d) = 2 ^ s₀ * 2 ^ d := Nat.pow_add _ _ _
      _ ≤ 3 ^ k₀ * 3 ^ d := Nat.mul_le_mul hpow (two_pow_le_three_pow d)
      _ = 3 ^ C.k := by rw [← Nat.pow_add, ← hsplit]
      _ < 2 ^ C.totalVal := C.pow_lt
  have hS : s₀ + d < C.totalVal := by
    by_cases h : s₀ + d < C.totalVal
    · exact h
    · have := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_lt h); omega
  simp only [SyracuseCycle.collatzLen]; omega

/-- Binary-exponentiation helper avoiding Lean's `exponentiation.threshold` during `decide`. -/
def fastPowAux : Nat → Nat → Nat → Nat → Nat
  | 0, acc, _, _ => acc
  | fuel + 1, acc, b, e =>
    if e = 0 then acc
    else fastPowAux fuel (if e % 2 = 1 then acc * b else acc) (b * b) (e / 2)

/-- Specification of `fastPowAux`: `e < 2 ^ fuel → fastPowAux fuel acc b e = acc * b ^ e`. -/
theorem fastPowAux_eq (fuel acc b e : Nat) (he : e < 2 ^ fuel) :
    fastPowAux fuel acc b e = acc * b ^ e := by
  induction fuel generalizing acc b e with
  | zero => rw [show e = 0 by omega]; simp [fastPowAux]
  | succ fuel ih =>
    unfold fastPowAux; split
    · rename_i he0; subst he0; simp
    · have hdiv_lt : e / 2 < 2 ^ fuel := by rw [Nat.pow_succ] at he; omega
      rw [ih _ (b * b) (e / 2) hdiv_lt,
        show (b * b) ^ (e / 2) = b ^ (2 * (e / 2)) by
          rw [← Nat.pow_two, ← Nat.pow_mul, Nat.mul_comm 2 (e / 2)]]
      split
      · rename_i hmod
        calc acc * b * b ^ (2 * (e / 2)) = acc * (b ^ (2 * (e / 2)) * b) := by ac_rfl
          _ = acc * b ^ e := by rw [← Nat.pow_succ, show (2 * (e / 2)).succ = e by omega]
      · rename_i hmod; rw [← show e = 2 * (e / 2) by omega]

/-- Fast binary exponentiation `a ^ e` for `e < 2 ^ 32`. -/
def fastPow (a e : Nat) : Nat := fastPowAux 32 1 a e

/-- `fastPow a e = a ^ e` whenever `e < 2 ^ 32`. -/
theorem fastPow_eq (a e : Nat) (he : e < 2 ^ 32) : fastPow a e = a ^ e := by
  simpa [fastPow] using fastPowAux_eq 32 1 a e he

/-- Binary search locating `s` with `2 ^ (s - 1) ≤ x < 2 ^ s` (verified at leaves). -/
def findMinPow2Exp : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, hi => hi
  | fuel + 1, x, lo, hi =>
    if hi ≤ lo + 1 then hi
    else if x < fastPow 2 ((lo + hi) / 2) then findMinPow2Exp fuel x lo ((lo + hi) / 2)
    else findMinPow2Exp fuel x ((lo + hi) / 2) hi

/-- Upper bound on the exponent returned by `findMinPow2Exp`. -/
theorem findMinPow2Exp_le (fuel x lo hi : Nat) (h : lo ≤ hi) :
    findMinPow2Exp fuel x lo hi ≤ hi := by
  induction fuel generalizing lo hi with
  | zero => exact Nat.le_refl hi
  | succ fuel ih =>
    unfold findMinPow2Exp; split
    · exact Nat.le_refl hi
    · split
      · exact Nat.le_trans (ih lo _ (by omega)) (by omega)
      · exact ih _ hi (by omega)

/-- Incremental checker verifying `(3 * M + 1) ^ k ≤ 2 ^ s * M ^ k` on `k ∈ [lo + 1, lo + len]`. -/
def cycleLenAux (M : Nat) : Nat → Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _, _ => true
  | rem + 1, pow3, pow2, powM, pow3M1 =>
    let pow3' := 3 * pow3
    let pow2' := if pow3' < 2 * pow2 then 2 * pow2 else 4 * pow2
    let powM' := powM * M
    let pow3M1' := pow3M1 * (3 * M + 1)
    decide (pow3M1' ≤ pow2' * powM') && cycleLenAux M rem pow3' pow2' powM' pow3M1'

/-- Leaf checker verifying `k ∈ [lo + 1, lo + len]`. -/
def cycleLenChunk (M lo len : Nat) : Bool :=
  let pow3 := fastPow 3 lo
  let s := findMinPow2Exp 16 pow3 0 (2 * lo + 1)
  let pow2 := fastPow 2 s
  decide (1 ≤ s ∧ fastPow 2 (s - 1) ≤ pow3 ∧ pow3 < pow2) &&
    cycleLenAux M len pow3 pow2 (fastPow M lo) (fastPow (3 * M + 1) lo)

/-- Divide-and-conquer kernel checker for `k ∈ [lo + 1, lo + len]` keeping depth `O(1)`. -/
def cycleLenTree : Nat → Nat → Nat → Nat → Bool
  | 0, M, lo, len => cycleLenChunk M lo len
  | depth + 1, M, lo, len =>
    if len ≤ 32 then cycleLenChunk M lo len
    else cycleLenTree depth M lo (len / 2) &&
      cycleLenTree depth M (lo + len / 2) (len - len / 2)

/-- One-step invariant update for `cycleLenAux_sound`. -/
theorem cycleLenAux_step_inv (lo s0 : Nat)
    (hs0 : 1 ≤ s0) (hlo : 2 ^ (s0 - 1) ≤ 3 ^ lo) (hhi : 3 ^ lo < 2 ^ s0) :
    let s' := if 3 * 3 ^ lo < 2 * 2 ^ s0 then s0 + 1 else s0 + 2
    1 ≤ s' ∧ 2 ^ (s' - 1) ≤ 3 ^ (lo + 1) ∧ 3 ^ (lo + 1) < 2 ^ s' ∧
      2 ^ s' = (if 3 * 3 ^ lo < 2 * 2 ^ s0 then 2 * 2 ^ s0 else 4 * 2 ^ s0) := by
  dsimp; split
  · rename_i hlt
    have h2s0 : 2 ^ s0 ≤ 2 * 3 ^ lo := by
      rw [show s0 = (s0 - 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]; omega
    refine ⟨by omega, ?_, ?_, ?_⟩
    · simp only [Nat.add_sub_cancel]; rw [Nat.pow_succ, Nat.mul_comm (3 ^ lo)]; omega
    · rw [Nat.pow_succ, Nat.mul_comm (3 ^ lo), Nat.pow_succ, Nat.mul_comm (2 ^ s0)]; exact hlt
    · rw [Nat.pow_succ, Nat.mul_comm]
  · refine ⟨by omega, ?_, ?_, ?_⟩
    · simp only [show s0 + 2 - 1 = s0 + 1 by omega, Nat.pow_succ, Nat.mul_comm (3 ^ lo)]
      rw [Nat.mul_comm (2 ^ s0) 2]; omega
    · rw [Nat.pow_succ, Nat.mul_comm (3 ^ lo), Nat.pow_succ, Nat.pow_succ]; omega
    · rw [Nat.pow_succ, Nat.pow_succ]; omega

/-- Soundness of `cycleLenAux` over `lo < k ≤ lo + rem`. -/
theorem cycleLenAux_sound (M rem lo s0 : Nat)
    (hs0 : 1 ≤ s0) (hlo : 2 ^ (s0 - 1) ≤ 3 ^ lo) (hhi : 3 ^ lo < 2 ^ s0)
    (hchk : cycleLenAux M rem (3 ^ lo) (2 ^ s0) (M ^ lo) ((3 * M + 1) ^ lo) = true) :
    ∀ k : Nat, lo < k → k ≤ lo + rem →
      ∃ s : Nat, 1 ≤ s ∧ 2 ^ (s - 1) ≤ 3 ^ k ∧ 3 ^ k < 2 ^ s ∧
        (3 * M + 1) ^ k ≤ 2 ^ s * M ^ k := by
  induction rem generalizing lo s0 with
  | zero => intro k hk1 hk2; omega
  | succ rem ih =>
    simp only [cycleLenAux, Bool.and_eq_true, decide_eq_true_eq] at hchk
    rcases hchk with ⟨hineq, hrest⟩
    rcases cycleLenAux_step_inv lo s0 hs0 hlo hhi with ⟨hs'_pos, hlo', hhi', h2pow'⟩
    let s' := if 3 * 3 ^ lo < 2 * 2 ^ s0 then s0 + 1 else s0 + 2
    have hrest' : cycleLenAux M rem (3 ^ (lo + 1)) (2 ^ s') (M ^ (lo + 1))
        ((3 * M + 1) ^ (lo + 1)) = true := by
      simpa [Nat.pow_succ, Nat.mul_comm (3 ^ lo) 3, ← h2pow'] using hrest
    intro k hk1 hk2
    by_cases heq : k = lo + 1
    · subst heq; refine ⟨s', hs'_pos, hlo', hhi', ?_⟩
      simpa [Nat.pow_succ, ← h2pow'] using hineq
    · exact ih (lo + 1) s' hs'_pos hlo' hhi' hrest' k (by omega) (by omega)

/-- Soundness of `cycleLenChunk` for `lo + len < 2 ^ 30`. -/
theorem cycleLenChunk_sound (M lo len : Nat) (hbound : lo + len < 2 ^ 30)
    (hchk : cycleLenChunk M lo len = true) :
    ∀ k : Nat, lo < k → k ≤ lo + len →
      ∃ s : Nat, 1 ≤ s ∧ 2 ^ (s - 1) ≤ 3 ^ k ∧ 3 ^ k < 2 ^ s ∧ (3 * M + 1) ^ k ≤ 2 ^ s * M ^ k := by
  unfold cycleLenChunk at hchk; simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
  generalize hs_eq : findMinPow2Exp 16 (fastPow 3 lo) 0 (2 * lo + 1) = s at hchk
  rcases hchk with ⟨⟨hs1, hlo_f, hhi_f⟩, haux⟩
  have hlo32 : lo < 2 ^ 32 := by omega
  have hs_le : s ≤ 2 * lo + 1 := by
    rw [← hs_eq]; exact findMinPow2Exp_le 16 (fastPow 3 lo) 0 (2 * lo + 1) (by omega)
  have hs32 : s < 2 ^ 32 := by omega
  have hsm32 : s - 1 < 2 ^ 32 := by omega
  rw [fastPow_eq 3 lo hlo32, fastPow_eq 2 (s - 1) hsm32] at hlo_f
  rw [fastPow_eq 3 lo hlo32, fastPow_eq 2 s hs32] at hhi_f
  rw [fastPow_eq 3 lo hlo32, fastPow_eq 2 s hs32, fastPow_eq M lo hlo32,
    fastPow_eq (3 * M + 1) lo hlo32] at haux
  exact cycleLenAux_sound M len lo s hs1 hlo_f hhi_f haux

/-- Soundness of `cycleLenTree` over `lo < k ≤ lo + len` for `lo + len < 2 ^ 30`. -/
theorem cycleLenTree_sound (depth M lo len : Nat) (hbound : lo + len < 2 ^ 30)
    (hchk : cycleLenTree depth M lo len = true) :
    ∀ k : Nat, lo < k → k ≤ lo + len →
      ∃ s : Nat, 1 ≤ s ∧ 2 ^ (s - 1) ≤ 3 ^ k ∧ 3 ^ k < 2 ^ s ∧ (3 * M + 1) ^ k ≤ 2 ^ s * M ^ k := by
  induction depth generalizing lo len with
  | zero => exact cycleLenChunk_sound M lo len hbound hchk
  | succ depth ih =>
    unfold cycleLenTree at hchk; split at hchk
    · exact cycleLenChunk_sound M lo len hbound hchk
    · simp only [Bool.and_eq_true] at hchk; intro k hk1 hk2
      by_cases hleft : k ≤ lo + len / 2
      · exact ih lo (len / 2) (by omega) hchk.1 k hk1 hleft
      · exact ih (lo + len / 2) (len - len / 2) (by omega) hchk.2 k (by omega) (by omega)

/-- Any `SyracuseCycle` with `M ≤ C.n_min` (`0 < M`) ruled out on `1 ≤ k ≤ K` has `K < C.k`. -/
theorem no_syracuseCycle_of_cycleLenTree (depth M K : Nat) (hMpos : 0 < M)
    (hbound : K < 2 ^ 30) (hchk : cycleLenTree depth M 0 K = true)
    (C : SyracuseCycle) (hM : M ≤ C.n_min) : K < C.k := by
  by_cases hgt : K < C.k
  · exact hgt
  · rcases cycleLenTree_sound depth M 0 K (by simpa using hbound) hchk C.k C.k_pos
        (by omega) with ⟨s, hs1, hlo, _, hineq⟩
    have hs_le_S : s ≤ C.totalVal := by
      by_cases hs : s ≤ C.totalVal
      · exact hs
      · have := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : C.totalVal ≤ s - 1)
        have := C.pow_lt; omega
    have hmul := Nat.mul_le_mul_right (M ^ C.k) (Nat.pow_le_pow_right (by decide : 0 < 2) hs_le_S)
    have hub := eliahou_upper_bound_lt C hMpos hM; omega

/-- Kernel-verified elimination up to `k ≤ 40` for `M = 1000` (zero `native_decide`). -/
theorem cycleLenTree_1000_40 : cycleLenTree 6 1000 0 40 = true := by decide
/-- Kernel-verified witness `2 ^ 64 ≤ 3 ^ 41`. -/
theorem two_pow_64_le_three_pow_41 : 2 ^ 64 ≤ 3 ^ 41 := by decide
/-- Kernel-verified elimination up to `k ≤ 1000` for `M = 10^6` (zero `native_decide`). -/
theorem cycleLenTree_1e6_1000 : cycleLenTree 6 1000000 0 1000 = true := by decide
/-- Kernel-verified witness `2 ^ 1586 ≤ 3 ^ 1001` via `fastPow`. -/
theorem two_pow_1586_le_three_pow_1001 : 2 ^ 1586 ≤ 3 ^ 1001 := by
  have h : fastPow 2 1586 ≤ fastPow 3 1001 := by decide
  rwa [fastPow_eq 2 1586 (by decide), fastPow_eq 3 1001 (by decide)] at h

/-- **Concrete Eliahou Threshold (`M = 1000`):** `1000 ≤ C.n_min` forces `41 ≤ C.k` and
`106 ≤ C.collatzLen`. -/
theorem syracuseCycle_bounds_of_ge_1000 (C : SyracuseCycle) (hM : 1000 ≤ C.n_min) :
    41 ≤ C.k ∧ 106 ≤ C.collatzLen := by
  have hk := no_syracuseCycle_of_cycleLenTree 6 1000 40 (by decide) (by decide)
    cycleLenTree_1000_40 C hM
  exact ⟨hk, collatzLen_ge_of_k_ge C 41 64 hk two_pow_64_le_three_pow_41⟩

/-- **Concrete Eliahou Threshold (`M = 10^6`):** `10^6 ≤ C.n_min` forces `1001 ≤ C.k` and
`2588 ≤ C.collatzLen`. -/
theorem syracuseCycle_bounds_of_ge_1e6 (C : SyracuseCycle) (hM : 1000000 ≤ C.n_min) :
    1001 ≤ C.k ∧ 2588 ≤ C.collatzLen := by
  have hk := no_syracuseCycle_of_cycleLenTree 6 1000000 1000 (by decide) (by decide)
    cycleLenTree_1e6_1000 C hM
  exact ⟨hk, collatzLen_ge_of_k_ge C 1001 1586 hk two_pow_1586_le_three_pow_1001⟩

/-- Every standard Collatz iterate of `C.n_min` is at least `C.n_min`. -/
theorem SyracuseCycle.min_le_collatzIter (C : SyracuseCycle) (t : Nat) :
    C.n_min ≤ collatzIter t C.n_min := by
  have haux : ∀ m : Nat, t < syracuseTime m C.n_min → C.n_min ≤ collatzIter t C.n_min := by
    intro m; induction m with
    | zero => intro hlt; simp [syracuseTime, syracuseTotalVal] at hlt
    | succ m ih =>
      intro hlt
      by_cases hprev : t < syracuseTime m C.n_min
      · exact ih hprev
      · by_cases heq : t = syracuseTime m C.n_min
        · subst heq; rw [syracuseTime, collatzIter_eq_syracuseIter m C.odd]; exact C.min_le m
        · rcases collatzIter_between_syracuseTime C.odd (by omega) hlt with ⟨r, _, hstep⟩
          have hsyr : C.n_min ≤ syracuseStep (syracuseIter m C.n_min) := by
            simpa [syracuseIter_succ_right] using C.min_le (m + 1)
          rw [hstep]
          exact Nat.le_trans hsyr (Nat.le_trans (by simp)
            (Nat.mul_le_mul_left _ (Nat.two_pow_pos _)))
  exact haux (t + 1) (by have := syracuseTotalVal_ge (t + 1) C.odd; simp [syracuseTime]; omega)

/-- If every `1 < n < M` has finite stopping time, then any `SyracuseCycle` has `M ≤ C.n_min`. -/
theorem syracuseCycle_min_ge_of_stopping (M : Nat)
    (hstop : ∀ n : Nat, 1 < n → n < M → HasFiniteStoppingTime n)
    (C : SyracuseCycle) : M ≤ C.n_min := by
  by_cases hM : M ≤ C.n_min
  · exact hM
  · rcases hstop C.n_min C.one_lt (Nat.lt_of_not_ge hM) with ⟨t, _, ht⟩
    have hge := C.min_le_collatzIter t; omega

/-- **Conditional Eliahou Cycle-Length Lower Bound (`M = 10^6`):** if all `1 < n < 10^6` have
finite stopping time, then any `SyracuseCycle` has `1001 ≤ C.k` and `2588 ≤ C.collatzLen`. -/
theorem eliahou_bounds_of_stopping_1e6
    (hstop : ∀ n : Nat, 1 < n → n < 1000000 → HasFiniteStoppingTime n)
    (C : SyracuseCycle) : 1001 ≤ C.k ∧ 2588 ≤ C.collatzLen :=
  syracuseCycle_bounds_of_ge_1e6 C (syracuseCycle_min_ge_of_stopping 1000000 hstop C)

/-- **Bridge to Frozen `Challenge.lean`:** if all `1 < m < 10^6` have finite stopping time, then
any non-trivial Collatz cycle `(n, L)` has total period `2588 ≤ L`. -/
theorem collatz_cycle_length_ge_of_stopping_1e6
    (hstop : ∀ m : Nat, 1 < m → m < 1000000 → HasFiniteStoppingTime m)
    {n L : Nat} (hn : 0 < n) (hL : 0 < L)
    (hcyc : collatzIter L n = n) (hne : ∀ j : Nat, j < L → collatzIter j n ≠ 1) :
    2588 ≤ L := by
  rcases exists_syracuseCycle_of_collatz_cycle hn hL hcyc hne with ⟨C, hlen⟩
  have hbd := eliahou_bounds_of_stopping_1e6 hstop C; omega

/-- **Bridge to Frozen `HasNontrivialCycle`:** assuming all `1 < m < 10^6` have finite stopping
time, `HasNontrivialCycle` forces a cycle of total Collatz length at least `2588`. -/
theorem hasNontrivialCycle_length_ge_2588
    (hstop : ∀ m : Nat, 1 < m → m < 1000000 → HasFiniteStoppingTime m)
    (h : HasNontrivialCycle) :
    ∃ n L : Nat, 0 < n ∧ 2588 ≤ L ∧ collatzIter L n = n ∧
      ∀ j : Nat, j < L → collatzIter j n ≠ 1 := by
  rcases h with ⟨n, L, hn, hL, hcyc, hne⟩
  exact ⟨n, L, hn, collatz_cycle_length_ge_of_stopping_1e6 hstop hn hL hcyc hne, hcyc, hne⟩

end SolveCollatz
