/-
Copyright (c) 2026 The solve-collatz contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Collatz.Known.Range

/-!
# Cycle-length bounds from the kernel-checked range `2^28` (`RANGE-003`)

`Collatz.Known.Range` proves that every `2 ≤ n < 2^28` has finite stopping time. So the smallest
element of a non-trivial cycle is at least `2^28`, and Eliahou's argument
(`eliahou_cf_elimination`) with the `log2 3` pair `1054/665`, `23673/14936` gives:

* at least `15601` odd steps,
* at least `24727` halvings,
* total length at least `40328`.
-/

public section

namespace SolveCollatz

/-- Numeric facts for `eliahou_cf_elimination` at `M = 2^28` with `(pL, qL) = (1054, 665)` and
`(pU, qU) = (23673, 14936)`, plus `2^24726 ≤ 3^15601` for the halving count. -/
theorem cf_witness_two_pow_28 :
    3 ^ 14936 < 2 ^ 23673 ∧
    14936 * 2 ^ 23673 ≤ (3 * 2 ^ 28 - (14936 + 665)) * (2 ^ 23673 - 3 ^ 14936) ∧
    2 ^ 24726 ≤ 3 ^ 15601 := by
  have h :
      fastPow 3 14936 < fastPow 2 23673 ∧
      14936 * fastPow 2 23673 ≤
          (3 * fastPow 2 28 - (14936 + 665)) * (fastPow 2 23673 - fastPow 3 14936) ∧
      fastPow 2 24726 ≤ fastPow 3 15601 := by decide +kernel
  rwa [fastPow_eq 3 14936 (by decide), fastPow_eq 2 23673 (by decide),
    fastPow_eq 2 28 (by decide), fastPow_eq 2 24726 (by decide),
    fastPow_eq 3 15601 (by decide)] at h

/-- The smallest element of a non-trivial Syracuse cycle is at least `2^28`. -/
theorem syracuseCycle_min_ge_two_pow_28 (C : SyracuseCycle) : 2 ^ 28 ≤ C.n_min :=
  syracuseCycle_min_ge_of_stopping (2 ^ 28)
    (fun _ hn hlt => Range.finiteStoppingTime_lt_two_pow_28 _ hn hlt) C

/-- A non-trivial Syracuse cycle has at least `15601` odd steps, at least `24727` halvings,
and total length at least `40328`. -/
theorem syracuseCycle_bounds_two_pow_28 (C : SyracuseCycle) :
    15601 ≤ C.k ∧ 24727 ≤ C.totalVal ∧ 40328 ≤ C.collatzLen := by
  have hk := eliahou_cf_elimination (2 ^ 28) 1054 665 23673 14936 (by decide) (by decide)
    log2ThreeCF_lower_exps.2.2.2.2 cf_witness_two_pow_28.1 (by decide) (by decide)
    cf_witness_two_pow_28.2.1 C (syracuseCycle_min_ge_two_pow_28 C)
  have hs := totalVal_ge_of_k_ge C 15601 24726 hk cf_witness_two_pow_28.2.2
  have hl := collatzLen_ge_of_k_ge C 15601 24726 hk cf_witness_two_pow_28.2.2
  exact ⟨hk, hs, hl⟩

/-- Every non-trivial cycle of the Collatz map in `Challenge.lean` has length at least
`40328`. -/
theorem collatzCycle_length_ge_40328 {n L : Nat} (hn : 0 < n) (hL : 0 < L)
    (hcyc : collatzIter L n = n) (hne : ∀ j : Nat, j < L → collatzIter j n ≠ 1) :
    40328 ≤ L := by
  rcases exists_syracuseCycle_of_collatz_cycle hn hL hcyc hne with ⟨C, hlen⟩
  have h := (syracuseCycle_bounds_two_pow_28 C).2.2
  omega

end SolveCollatz

end
