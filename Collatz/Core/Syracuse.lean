/-
Copyright (c) 2026 The solve-collatz contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Collatz.Core.Basic

/-!
# Accelerated Syracuse Map & Parity-Vector Affine Formula (`CORE-003`)

Shared core infrastructure for both Track A (`Collatz/Prove/`) and Track B (`Collatz/Disprove/`):
- Exact `2`-adic factorization on `ℕ`: `valuation2` and `oddPart` with
  `oddPart n * 2 ^ valuation2 n = n` and uniqueness on odd-times-power-of-two products.
- One-step accelerated Syracuse map `syracuseStep n = oddPart (3 * n + 1)` and halving exponent
  `syracuseVal n = valuation2 (3 * n + 1)`, bridged directly to frozen `Challenge.lean` via
  `collatzIter_eq_syracuseStep`.
- Iterated Syracuse orbit (`syracuseIter`, `syracuseTotalVal`, `syracuseOffset`) and explicit
  parity-vector functions (`syracuseValVec`, `paritySum`, `parityOffset`) satisfying the
  fundamental affine identity
  `2 ^ syracuseTotalVal k n * syracuseIter k n = 3 ^ k * n + syracuseOffset k n`.
- Orbit bridge `collatzIter_eq_syracuseIter`, cycle equation
  `(2 ^ S - 3 ^ k) * n = C(v)` with `3 ^ k < 2 ^ S`, and full bridges to `CollatzConjecture`
  and `HasNontrivialCycle`.
-/

@[expose] public section

namespace SolveCollatz

/-! ### 1. Exact `2`-adic Valuation and Odd Part -/

/-- The `2`-adic valuation `v₂(n)`: the number of factors of `2` dividing `n`
(with `valuation2 0 = 0`). -/
def valuation2 (n : Nat) : Nat :=
  if 0 < n ∧ n % 2 = 0 then
    valuation2 (n / 2) + 1
  else
    0
termination_by n
decreasing_by omega

/-- The odd part of `n`: the unique odd factor obtained by stripping all factors of `2`
(with `oddPart 0 = 0`). -/
def oddPart (n : Nat) : Nat :=
  if 0 < n ∧ n % 2 = 0 then
    oddPart (n / 2)
  else
    n
termination_by n
decreasing_by omega

/-- Unfolding rule for `valuation2` on positive even inputs. -/
theorem valuation2_of_even {n : Nat} (hn : 0 < n) (heven : n % 2 = 0) :
    valuation2 n = valuation2 (n / 2) + 1 := by
  rw [valuation2, ite_eq_left ⟨hn, heven⟩]

/-- Unfolding rule for `valuation2` on odd inputs. -/
theorem valuation2_of_odd {n : Nat} (hodd : n % 2 = 1) : valuation2 n = 0 := by
  rw [valuation2, ite_eq_right (by omega)]

/-- Unfolding rule for `oddPart` on positive even inputs. -/
theorem oddPart_of_even {n : Nat} (hn : 0 < n) (heven : n % 2 = 0) :
    oddPart n = oddPart (n / 2) := by
  rw [oddPart, ite_eq_left ⟨hn, heven⟩]

/-- Unfolding rule for `oddPart` on odd inputs. -/
theorem oddPart_of_odd {n : Nat} (hodd : n % 2 = 1) : oddPart n = n := by
  rw [oddPart, ite_eq_right (by omega)]

/-- Every natural number factors as `oddPart n * 2 ^ valuation2 n = n`. -/
theorem oddPart_mul_two_pow (n : Nat) : oddPart n * 2 ^ valuation2 n = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : 0 < n ∧ n % 2 = 0
    · rcases h with ⟨hn, heven⟩
      rw [oddPart_of_even hn heven, valuation2_of_even hn heven, Nat.pow_succ, ← Nat.mul_assoc]
      rw [ih (n / 2) (by omega)]
      omega
    · rw [oddPart, valuation2, ite_eq_right h, ite_eq_right h, Nat.pow_zero, Nat.mul_one]

/-- The odd part of any positive integer is odd (`oddPart n % 2 = 1`). -/
theorem oddPart_odd {n : Nat} (hn : 0 < n) : oddPart n % 2 = 1 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases heven : n % 2 = 0
    · rw [oddPart_of_even hn heven]
      exact ih (n / 2) (by omega) (by omega)
    · have hodd : n % 2 = 1 := by omega
      rw [oddPart_of_odd hodd]
      exact hodd

/-- The odd part of any positive integer is positive. -/
theorem oddPart_pos {n : Nat} (hn : 0 < n) : 0 < oddPart n := by
  have hodd := oddPart_odd hn
  omega

/-- Uniqueness of `valuation2` on products `m * 2 ^ e` with `m` odd. -/
theorem valuation2_mul_two_pow {m : Nat} (hm : m % 2 = 1) (e : Nat) :
    valuation2 (m * 2 ^ e) = e := by
  induction e with
  | zero =>
    rw [Nat.pow_zero, Nat.mul_one]
    exact valuation2_of_odd hm
  | succ e ih =>
    have hpos : 0 < m * 2 ^ (e + 1) := by
      have hmpos : 0 < m := by omega
      exact Nat.mul_pos hmpos (Nat.two_pow_pos (e + 1))
    have hmul : m * 2 ^ (e + 1) = (m * 2 ^ e) * 2 := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    have heven : (m * 2 ^ (e + 1)) % 2 = 0 := by
      rw [hmul]
      omega
    rw [valuation2_of_even hpos heven, hmul, Nat.mul_div_cancel _ (by decide), ih]

/-- Uniqueness of `oddPart` on products `m * 2 ^ e` with `m` odd. -/
theorem oddPart_mul_two_pow_eq {m : Nat} (hm : m % 2 = 1) (e : Nat) :
    oddPart (m * 2 ^ e) = m := by
  induction e with
  | zero =>
    rw [Nat.pow_zero, Nat.mul_one]
    exact oddPart_of_odd hm
  | succ e ih =>
    have hpos : 0 < m * 2 ^ (e + 1) := by
      have hmpos : 0 < m := by omega
      exact Nat.mul_pos hmpos (Nat.two_pow_pos (e + 1))
    have hmul : m * 2 ^ (e + 1) = (m * 2 ^ e) * 2 := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    have heven : (m * 2 ^ (e + 1)) % 2 = 0 := by
      rw [hmul]
      omega
    rw [oddPart_of_even hpos heven, hmul, Nat.mul_div_cancel _ (by decide), ih]

/-! ### 2. One-Step Syracuse Map and Bridge to `Challenge.lean` -/

/-- One step of the accelerated Syracuse map: `T(n) = oddPart (3 * n + 1)`. -/
def syracuseStep (n : Nat) : Nat :=
  oddPart (3 * n + 1)

/-- Number of consecutive halvings following the odd step `n ↦ 3 * n + 1`. -/
def syracuseVal (n : Nat) : Nat :=
  valuation2 (3 * n + 1)

/-- The image of any natural number under `syracuseStep` is odd. -/
theorem syracuseStep_odd (n : Nat) : syracuseStep n % 2 = 1 :=
  oddPart_odd (Nat.succ_pos (3 * n))

/-- The image of any natural number under `syracuseStep` is positive. -/
theorem syracuseStep_pos (n : Nat) : 0 < syracuseStep n :=
  oddPart_pos (Nat.succ_pos (3 * n))

/-- For odd `n`, `3 * n + 1` is even so at least one halving occurs (`1 ≤ syracuseVal n`). -/
theorem syracuseVal_pos {n : Nat} (hn : n % 2 = 1) : 0 < syracuseVal n := by
  have heven : (3 * n + 1) % 2 = 0 := by omega
  rw [syracuseVal, valuation2_of_even (Nat.succ_pos (3 * n)) heven]
  exact Nat.succ_pos _

/-- Exact one-step multiplicative identity: `2 ^ syracuseVal n * syracuseStep n = 3 * n + 1`. -/
theorem two_pow_mul_syracuseStep (n : Nat) :
    2 ^ syracuseVal n * syracuseStep n = 3 * n + 1 := by
  rw [Nat.mul_comm]
  exact oddPart_mul_two_pow (3 * n + 1)

/-- Fixed-point evaluation `syracuseVal 1 = 2`. -/
theorem syracuseVal_one : syracuseVal 1 = 2 := by
  simpa [syracuseVal] using valuation2_mul_two_pow (m := 1) (by decide) 2

/-- Fixed-point evaluation `syracuseStep 1 = 1`. -/
theorem syracuseStep_one : syracuseStep 1 = 1 := by
  simpa [syracuseStep] using oddPart_mul_two_pow_eq (m := 1) (by decide) 2

/-- Applying `r ≤ e` Collatz steps to `m * 2 ^ e` performs `r` consecutive halvings. -/
theorem collatzIter_mul_two_pow_sub (m e r : Nat) (hr : r ≤ e) :
    collatzIter r (m * 2 ^ e) = m * 2 ^ (e - r) := by
  induction r generalizing e with
  | zero => simp [collatzIter]
  | succ r ih =>
    cases e with
    | zero => omega
    | succ e =>
      have hmul : m * 2 ^ (e + 1) = (m * 2 ^ e) * 2 := by
        rw [Nat.pow_succ, Nat.mul_assoc]
      have hstep : collatzStep (m * 2 ^ (e + 1)) = m * 2 ^ e := by
        rw [collatzStep, hmul, ite_eq_left (by omega), Nat.mul_div_cancel _ (by decide)]
      rw [collatzIter, hstep, ih e (by omega)]
      simp only [Nat.succ_sub_succ_eq_sub]

/-- Applying `e` Collatz steps to `m * 2 ^ e` strips all `e` factors of `2`. -/
theorem collatzIter_mul_two_pow (m e : Nat) : collatzIter e (m * 2 ^ e) = m := by
  simpa [Nat.sub_self, Nat.pow_zero, Nat.mul_one] using
    collatzIter_mul_two_pow_sub m e e (Nat.le_refl e)

/-- Stripping `valuation2 n` Collatz halvings from `n` reaches `oddPart n`. -/
theorem collatzIter_valuation2 (n : Nat) : collatzIter (valuation2 n) n = oddPart n := by
  have h := collatzIter_mul_two_pow (oddPart n) (valuation2 n)
  rwa [oddPart_mul_two_pow n] at h

/-- **One-Step Bridge to `Challenge.lean`:** on odd `n`, one Syracuse step equals
`syracuseVal n + 1` standard Collatz steps. -/
theorem collatzIter_eq_syracuseStep {n : Nat} (hn : n % 2 = 1) :
    collatzIter (syracuseVal n + 1) n = syracuseStep n := by
  have hstep : collatzStep n = 3 * n + 1 := by
    rw [collatzStep, ite_eq_right (by omega)]
  rw [collatzIter, hstep]
  exact collatzIter_valuation2 (3 * n + 1)

/-! ### 3. Iterated Syracuse Map, Parity Vectors, and Affine Identity -/

/-- The `k`-th iterate of `syracuseStep` starting from `n`. -/
def syracuseIter : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => syracuseIter k (syracuseStep n)

/-- Total number of halvings `S` accumulated over `k` Syracuse steps starting from `n`. -/
def syracuseTotalVal : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n => syracuseVal n + syracuseTotalVal k (syracuseStep n)

/-- Exact affine numerator `C(v)` accumulated over `k` Syracuse steps starting from `n`,
satisfying `2 ^ syracuseTotalVal k n * syracuseIter k n = 3 ^ k * n + syracuseOffset k n`. -/
def syracuseOffset : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n => 3 ^ k + 2 ^ syracuseVal n * syracuseOffset k (syracuseStep n)

/-- The list of `k` halving exponents `[v₂(3n₀+1), …, v₂(3n_{k-1}+1)]` along the Syracuse orbit. -/
def syracuseValVec : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, n => syracuseVal n :: syracuseValVec k (syracuseStep n)

/-- Total halving sum `S(v) = ∑ eᵢ` of a parity exponent vector `v`. -/
def paritySum : List Nat → Nat
  | [] => 0
  | e :: es => e + paritySum es

/-- Affine cycle numerator `C(v) = ∑_{i=0}^{k-1} 3^{k-1-i} 2^{e₀ + … + e_{i-1}}` of a parity
exponent vector `v`. Matches `search/cycle_hunter.py` and `search/barrier_redteam.py`. -/
def parityOffset : List Nat → Nat
  | [] => 0
  | e :: es => 3 ^ es.length + 2 ^ e * parityOffset es

/-- `syracuseValVec k n` has length `k`. -/
theorem syracuseValVec_length (k n : Nat) : (syracuseValVec k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [syracuseValVec, ih]

/-- `paritySum` of the orbit exponent vector equals `syracuseTotalVal`. -/
theorem paritySum_syracuseValVec (k n : Nat) :
    paritySum (syracuseValVec k n) = syracuseTotalVal k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [syracuseValVec, paritySum, syracuseTotalVal, ih]

/-- `parityOffset` of the orbit exponent vector equals `syracuseOffset`. -/
theorem parityOffset_syracuseValVec (k n : Nat) :
    parityOffset (syracuseValVec k n) = syracuseOffset k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    simp [syracuseValVec, parityOffset, syracuseOffset, syracuseValVec_length, ih]

/-- `paritySum` is additive under list concatenation. -/
theorem paritySum_append (u v : List Nat) :
    paritySum (u ++ v) = paritySum u + paritySum v := by
  induction u with
  | nil => simp [paritySum]
  | cons e es ih =>
    simp only [List.cons_append, paritySum, ih, Nat.add_assoc]

/-- Cocycle concatenation law for `parityOffset` under appending parity vectors. -/
theorem parityOffset_append (u v : List Nat) :
    parityOffset (u ++ v) =
      3 ^ v.length * parityOffset u + 2 ^ paritySum u * parityOffset v := by
  induction u with
  | nil => simp [parityOffset, paritySum]
  | cons e es ih =>
    calc parityOffset ((e :: es) ++ v)
        = 3 ^ (es.length + v.length) + 2 ^ e * parityOffset (es ++ v) := by
            simp [parityOffset]
      _ = 3 ^ v.length * 3 ^ es.length +
            2 ^ e * (3 ^ v.length * parityOffset es + 2 ^ paritySum es * parityOffset v) := by
            rw [ih, Nat.pow_add, Nat.mul_comm (3 ^ es.length)]
      _ = 3 ^ v.length * (3 ^ es.length + 2 ^ e * parityOffset es) +
            2 ^ (e + paritySum es) * parityOffset v := by
            rw [Nat.mul_add, Nat.mul_add, Nat.pow_add, Nat.mul_assoc (2 ^ e),
              Nat.mul_left_comm (2 ^ e) (3 ^ v.length), Nat.add_assoc]
      _ = 3 ^ v.length * parityOffset (e :: es) +
            2 ^ paritySum (e :: es) * parityOffset v := rfl

/-- Composition law for `syracuseIter`. -/
theorem syracuseIter_add (k m n : Nat) :
    syracuseIter m (syracuseIter k n) = syracuseIter (k + m) n := by
  induction k generalizing n with
  | zero => simp [syracuseIter]
  | succ k ih =>
    simp only [syracuseIter, Nat.succ_add]
    exact ih (syracuseStep n)

/-- Right-stepping identity: `syracuseIter (k + 1) n = syracuseStep (syracuseIter k n)`. -/
theorem syracuseIter_succ_right (k n : Nat) :
    syracuseIter (k + 1) n = syracuseStep (syracuseIter k n) :=
  (syracuseIter_add k 1 n).symm

/-- Concatenation law for `syracuseValVec` along split orbits. -/
theorem syracuseValVec_add (k m n : Nat) :
    syracuseValVec (k + m) n = syracuseValVec k n ++ syracuseValVec m (syracuseIter k n) := by
  induction k generalizing n with
  | zero => simp [syracuseValVec, syracuseIter]
  | succ k ih =>
    simp only [Nat.succ_add, syracuseValVec, syracuseIter, List.cons_append]
    rw [ih (syracuseStep n)]

/-- Additivity of `syracuseTotalVal` along split orbits. -/
theorem syracuseTotalVal_add (k m n : Nat) :
    syracuseTotalVal (k + m) n =
      syracuseTotalVal k n + syracuseTotalVal m (syracuseIter k n) := by
  rw [← paritySum_syracuseValVec, syracuseValVec_add, paritySum_append,
    paritySum_syracuseValVec, paritySum_syracuseValVec]

/-- Cocycle composition law for `syracuseOffset` along split orbits. -/
theorem syracuseOffset_add (k m n : Nat) :
    syracuseOffset (k + m) n =
      3 ^ m * syracuseOffset k n +
        2 ^ syracuseTotalVal k n * syracuseOffset m (syracuseIter k n) := by
  rw [← parityOffset_syracuseValVec, syracuseValVec_add, parityOffset_append,
    syracuseValVec_length, parityOffset_syracuseValVec, paritySum_syracuseValVec,
    parityOffset_syracuseValVec]

/-- Every positive Syracuse iterate is odd, regardless of the parity of `n`. -/
theorem syracuseIter_odd {k : Nat} (hk : 0 < k) (n : Nat) : syracuseIter k n % 2 = 1 := by
  cases k with
  | zero => exact absurd hk (Nat.lt_irrefl 0)
  | succ k =>
    rw [syracuseIter_succ_right]
    exact syracuseStep_odd (syracuseIter k n)

/-- Iterates of an odd integer under `syracuseIter` remain odd for all `k ≥ 0`. -/
theorem syracuseIter_odd_of_odd (k : Nat) {n : Nat} (hn : n % 2 = 1) :
    syracuseIter k n % 2 = 1 := by
  cases k with
  | zero => exact hn
  | succ k => exact syracuseIter_odd (Nat.succ_pos k) n

/-- The trivial fixed point `1` is fixed by every iterate of `syracuseIter`. -/
theorem syracuseIter_one (k : Nat) : syracuseIter k 1 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [syracuseIter, syracuseStep_one, ih]

/-- For odd `n`, `k` Syracuse steps accumulate at least `k` halvings
(`k ≤ syracuseTotalVal k n`). -/
theorem syracuseTotalVal_ge (k : Nat) {n : Nat} (hn : n % 2 = 1) :
    k ≤ syracuseTotalVal k n := by
  induction k generalizing n with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have hval : 0 < syracuseVal n := syracuseVal_pos hn
    have hrest : k ≤ syracuseTotalVal k (syracuseStep n) := ih (syracuseStep_odd n)
    simp only [syracuseTotalVal]
    omega

/-- For any positive number of steps `k > 0`, the affine numerator `syracuseOffset k n`
is positive. -/
theorem syracuseOffset_pos {k : Nat} (hk : 0 < k) (n : Nat) : 0 < syracuseOffset k n := by
  cases k with
  | zero => exact absurd hk (Nat.lt_irrefl 0)
  | succ k =>
    have hpow : 0 < 3 ^ k := Nat.pow_pos (by decide)
    simp only [syracuseOffset]
    omega

/-- **Main Affine Formula (`CORE-003`):** along any `k`-step Syracuse orbit,
`2 ^ syracuseTotalVal k n * syracuseIter k n = 3 ^ k * n + syracuseOffset k n`. -/
theorem syracuse_affine_eq (k n : Nat) :
    2 ^ syracuseTotalVal k n * syracuseIter k n = 3 ^ k * n + syracuseOffset k n := by
  induction k generalizing n with
  | zero => simp [syracuseTotalVal, syracuseIter, syracuseOffset]
  | succ k ih =>
    calc 2 ^ syracuseTotalVal (k + 1) n * syracuseIter (k + 1) n
        = 2 ^ syracuseVal n *
            (2 ^ syracuseTotalVal k (syracuseStep n) * syracuseIter k (syracuseStep n)) := by
            simp only [syracuseTotalVal, syracuseIter, Nat.pow_add, Nat.mul_assoc]
      _ = 2 ^ syracuseVal n *
            (3 ^ k * syracuseStep n + syracuseOffset k (syracuseStep n)) := by
            rw [ih (syracuseStep n)]
      _ = 3 ^ k * (2 ^ syracuseVal n * syracuseStep n) +
            2 ^ syracuseVal n * syracuseOffset k (syracuseStep n) := by
            rw [Nat.mul_add, Nat.mul_left_comm (2 ^ syracuseVal n) (3 ^ k)]
      _ = 3 ^ k * (3 * n + 1) +
            2 ^ syracuseVal n * syracuseOffset k (syracuseStep n) := by
            rw [two_pow_mul_syracuseStep]
      _ = 3 ^ (k + 1) * n +
            (3 ^ k + 2 ^ syracuseVal n * syracuseOffset k (syracuseStep n)) := by
            rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, ← Nat.pow_succ, Nat.add_assoc]
      _ = 3 ^ (k + 1) * n + syracuseOffset (k + 1) n := rfl

/-- Explicit parity-vector form of `syracuse_affine_eq`:
`2 ^ S(v) * syracuseIter k n = 3 ^ k * n + C(v)` for `v = syracuseValVec k n`. -/
theorem syracuse_affine_vec_eq (k n : Nat) :
    2 ^ paritySum (syracuseValVec k n) * syracuseIter k n =
      3 ^ k * n + parityOffset (syracuseValVec k n) := by
  rw [paritySum_syracuseValVec, parityOffset_syracuseValVec]
  exact syracuse_affine_eq k n

/-! ### 4. Orbit Bridge to `Challenge.lean` and Cycle Equations -/

/-- **Orbit Bridge to `Challenge.lean`:** on odd `n`, `k` Syracuse steps equal
`syracuseTotalVal k n + k` standard Collatz steps. -/
theorem collatzIter_eq_syracuseIter (k : Nat) {n : Nat} (hn : n % 2 = 1) :
    collatzIter (syracuseTotalVal k n + k) n = syracuseIter k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    have hsplit :
        syracuseTotalVal (k + 1) n + (k + 1) =
          (syracuseVal n + 1) + (syracuseTotalVal k (syracuseStep n) + k) := by
      simp only [syracuseTotalVal]
      omega
    calc collatzIter (syracuseTotalVal (k + 1) n + (k + 1)) n
        = collatzIter ((syracuseVal n + 1) + (syracuseTotalVal k (syracuseStep n) + k)) n := by
            rw [hsplit]
      _ = collatzIter (syracuseTotalVal k (syracuseStep n) + k)
            (collatzIter (syracuseVal n + 1) n) :=
            (collatzIter_add (syracuseVal n + 1) _ n).symm
      _ = collatzIter (syracuseTotalVal k (syracuseStep n) + k) (syracuseStep n) := by
            rw [collatzIter_eq_syracuseStep hn]
      _ = syracuseIter k (syracuseStep n) := ih (syracuseStep_odd n)
      _ = syracuseIter (k + 1) n := rfl

/-- **Additive Cycle Identity:** any Syracuse cycle `syracuseIter k n = n` satisfies
`2 ^ S * n = 3 ^ k * n + C(v)`. -/
theorem syracuse_cycle_mul_eq {k n : Nat} (hcyc : syracuseIter k n = n) :
    2 ^ syracuseTotalVal k n * n = 3 ^ k * n + syracuseOffset k n := by
  have h := syracuse_affine_eq k n
  rw [hcyc] at h
  exact h

/-- **Archimedean Positivity Inequality for Cycles:** any positive-length Syracuse cycle
`syracuseIter k n = n` (`0 < k`) forces `3 ^ k < 2 ^ S`. -/
theorem syracuse_cycle_pow_lt {k n : Nat} (hk : 0 < k) (hcyc : syracuseIter k n = n) :
    3 ^ k < 2 ^ syracuseTotalVal k n := by
  have hmul : 2 ^ syracuseTotalVal k n * n = 3 ^ k * n + syracuseOffset k n :=
    syracuse_cycle_mul_eq hcyc
  have hoff : 0 < syracuseOffset k n := syracuseOffset_pos hk n
  have hlt : 3 ^ k * n < 2 ^ syracuseTotalVal k n * n := by omega
  exact Nat.lt_of_mul_lt_mul_right hlt

/-- **Cycle Equation Corollary:** any Syracuse cycle `syracuseIter k n = n` satisfies
`(2 ^ S - 3 ^ k) * n = syracuseOffset k n` (with `3 ^ k < 2 ^ S` whenever `0 < k`). -/
theorem syracuse_cycle_equation {k n : Nat} (hcyc : syracuseIter k n = n) :
    (2 ^ syracuseTotalVal k n - 3 ^ k) * n = syracuseOffset k n := by
  have hmul : 2 ^ syracuseTotalVal k n * n = 3 ^ k * n + syracuseOffset k n :=
    syracuse_cycle_mul_eq hcyc
  rw [Nat.sub_mul, hmul, Nat.add_sub_cancel_left]

/-- **Diophantine Divisibility Condition (`DISPROVE-002`):** any Syracuse cycle satisfies
`(2 ^ S - 3 ^ k) ∣ syracuseOffset k n`. -/
theorem syracuse_cycle_dvd {k n : Nat} (hcyc : syracuseIter k n = n) :
    (2 ^ syracuseTotalVal k n - 3 ^ k) ∣ syracuseOffset k n :=
  ⟨n, (syracuse_cycle_equation hcyc).symm⟩

/-- **Track A Bridge:** if every odd natural number reaches `1` under `syracuseIter`, then
`CollatzConjecture` holds. -/
theorem collatzConjecture_of_syracuse
    (h : ∀ n : Nat, n % 2 = 1 → ∃ k : Nat, syracuseIter k n = 1) : CollatzConjecture := by
  intro n hn
  rcases h (oddPart n) (oddPart_odd hn) with ⟨k, hk⟩
  refine ⟨valuation2 n + (syracuseTotalVal k (oddPart n) + k), ?_⟩
  rw [← collatzIter_add, collatzIter_valuation2,
    collatzIter_eq_syracuseIter k (oddPart_odd hn), hk]

/-- Intermediate halving iterates strictly before `syracuseStep n` are even and thus avoid `1`. -/
theorem collatzIter_ne_one_lt_syracuseStep {n j : Nat}
    (hn : n % 2 = 1) (hne : n ≠ 1) (hj : j < syracuseVal n + 1) :
    collatzIter j n ≠ 1 := by
  cases j with
  | zero => exact hne
  | succ r =>
    have hstep : collatzStep n = 3 * n + 1 := by
      rw [collatzStep, ite_eq_right (by omega)]
    have hr : r < syracuseVal n := Nat.lt_of_succ_lt_succ hj
    have heq : collatzIter (r + 1) n = syracuseStep n * 2 ^ (syracuseVal n - r) := by
      rw [collatzIter, hstep]
      conv => lhs; rw [← oddPart_mul_two_pow (3 * n + 1)]
      exact collatzIter_mul_two_pow_sub (syracuseStep n) (syracuseVal n) r (Nat.le_of_lt hr)
    rw [heq]
    have hsub : syracuseVal n - r = (syracuseVal n - r - 1) + 1 := by omega
    rw [hsub, Nat.pow_succ, ← Nat.mul_assoc]
    omega

/-- If no Syracuse iterate in `[0, k)` equals `1`, then no standard Collatz iterate in
`[0, syracuseTotalVal k n + k)` equals `1`. -/
theorem collatzIter_ne_one_of_syracuseIter (k : Nat) {n : Nat}
    (hn : n % 2 = 1) (hne : ∀ i : Nat, i < k → syracuseIter i n ≠ 1) :
    ∀ j : Nat, j < syracuseTotalVal k n + k → collatzIter j n ≠ 1 := by
  induction k generalizing n with
  | zero => intro j hj; exact absurd hj (Nat.not_lt_zero j)
  | succ k ih =>
    intro j hj
    by_cases hlt : j < syracuseVal n + 1
    · exact collatzIter_ne_one_lt_syracuseStep hn (hne 0 (Nat.succ_pos k)) hlt
    · have hge : syracuseVal n + 1 ≤ j := Nat.le_of_not_lt hlt
      have hrest : j - (syracuseVal n + 1) < syracuseTotalVal k (syracuseStep n) + k := by
        simp only [syracuseTotalVal] at hj
        omega
      have hne' : ∀ i : Nat, i < k → syracuseIter i (syracuseStep n) ≠ 1 := fun i hi =>
        hne (i + 1) (Nat.succ_lt_succ hi)
      have heq : collatzIter j n = collatzIter (j - (syracuseVal n + 1)) (syracuseStep n) := by
        calc collatzIter j n
            = collatzIter ((syracuseVal n + 1) + (j - (syracuseVal n + 1))) n := by
                rw [Nat.add_sub_of_le hge]
          _ = collatzIter (j - (syracuseVal n + 1)) (collatzIter (syracuseVal n + 1) n) :=
                (collatzIter_add (syracuseVal n + 1) _ n).symm
          _ = collatzIter (j - (syracuseVal n + 1)) (syracuseStep n) := by
                rw [collatzIter_eq_syracuseStep hn]
      rw [heq]
      exact ih (syracuseStep_odd n) hne' _ hrest

/-- **Track B Bridge:** any positive-length Syracuse cycle avoiding `1` yields a
`HasNontrivialCycle` witness (and hence `CollatzDisproof` via `CORE-001`). -/
theorem hasNontrivialCycle_of_syracuse_cycle {k n : Nat}
    (hk : 0 < k) (hcyc : syracuseIter k n = n)
    (hne : ∀ i : Nat, i < k → syracuseIter i n ≠ 1) : HasNontrivialCycle := by
  have hodd : n % 2 = 1 := by
    rw [← hcyc]
    exact syracuseIter_odd hk n
  have hnpos : 0 < n := by omega
  have hper : 0 < syracuseTotalVal k n + k := by omega
  have hret : collatzIter (syracuseTotalVal k n + k) n = n := by
    rw [collatzIter_eq_syracuseIter k hodd, hcyc]
  exact ⟨n, syracuseTotalVal k n + k, hnpos, hper, hret,
    collatzIter_ne_one_of_syracuseIter k hodd hne⟩

end SolveCollatz
