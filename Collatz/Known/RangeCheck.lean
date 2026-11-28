/-
Copyright (c) 2026 The solve-collatz contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Collatz.Known.EliahouLifted22

/-!
# Kernel range checks for any dyadic shell (`RANGE-001`)

`EliahouLifted22` checks `[2^20, 2^22)` with a residue-tree walker whose depths are fixed. This
file makes the same walker work for any shell `[2^s, 2^(s+1))`, split into buckets by `n % 2^t`,
so that each bucket is one `decide` and different buckets can be checked in different modules.

* `rangeWalk fuel rem` walks `rem` levels of the residue tree below depth `k`, pruning classes
  that provably drop, and checks each surviving `n` on the shell with `drop4x2`.
* `rangeTop lo hi fuel rem top` walks the first `top` levels from the root and keeps only the
  residues `r` mod `2^(top+1)` with `lo ≤ r < hi`.
* `rangeShell_bucket_sound` turns one successful bucket check into `HasFiniteStoppingTime n` for
  every odd `n` in the shell whose residue is in the bucket.

`search/range_cert/gen_shells.py` generates the per-shell bucket files.
-/

@[expose] public section

namespace SolveCollatz

/-- Residue-tree walker: `rem` levels of `stepChildren`, then `checkLeaf` on the shell. -/
def rangeWalk (fuel rem : Nat) : Nat → Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Bool)
    (checkLeaf fuel) (fun _ ih => stepChildren ih) rem

/-- Soundness of `rangeWalk` on the shell `[2^(k + rem), 2^(k + rem + 1))`. -/
theorem rangeWalk_sound (fuel rem : Nat) :
    ∀ k r : Nat, 0 < k → r < 2 ^ k →
      rangeWalk fuel rem r (terrasIter k r)
        (3 ^ countOnes (terrasParityVec k r)) (2 ^ k) = true →
      ∀ n : Nat, 2 ^ (k + rem) ≤ n → n < 2 ^ (k + rem + 1) → n % 2 ^ k = r →
        HasFiniteStoppingTime n := by
  induction rem with
  | zero =>
    intro k r hk _ hchk n h1 h2 hm
    exact checkLeaf_sound fuel k r hk hchk n h1 h2 hm
  | succ rem ih =>
    intro k r hk hr hchk n hn1 hn2 hmod
    have hnk1 : 2 ^ (k + 1) ≤ n :=
      Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hn1
    exact stepChildren_sound (2 ^ (k + rem.succ + 1)) (fun m => 2 ^ (k + rem.succ) ≤ m)
      (rangeWalk fuel rem)
      (fun r' hr' h' n' hP _ hn2' hm =>
        ih (k + 1) r' (by omega) hr' h' n'
          (by simpa [Nat.add_assoc, Nat.add_comm 1 rem] using hP)
          (by simpa [Nat.add_assoc, Nat.add_comm 1 rem] using hn2') hm)
      hk r hr hchk n hn1 hnk1 hn2 hmod

/-- Top walker: `top` levels of `stepChildren`, then keep residues `lo ≤ r < hi`. -/
def rangeTop (lo hi fuel rem top : Nat) : Nat → Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Bool)
    (fun r cur p3 p2 =>
      Bool.casesOn (Nat.ble lo r) true
        (Bool.casesOn (Nat.ble (Nat.add r 1) hi) true (rangeWalk fuel rem r cur p3 p2)))
    (fun _ ih => stepChildren ih) top

/-- Soundness of `rangeTop` started at depth `k` with `k + top = t`. -/
theorem rangeTop_sound (lo hi fuel rem t : Nat) :
    ∀ top k r : Nat, 0 < k → k + top = t → r < 2 ^ k →
      rangeTop lo hi fuel rem top r (terrasIter k r)
        (3 ^ countOnes (terrasParityVec k r)) (2 ^ k) = true →
      ∀ n : Nat, 2 ^ (t + rem) ≤ n → n < 2 ^ (t + rem + 1) → n % 2 ^ k = r →
        lo ≤ n % 2 ^ t → n % 2 ^ t < hi → HasFiniteStoppingTime n := by
  intro top
  induction top with
  | zero =>
    intro k r hk hsum hr hchk n hn1 hn2 hmod hbl hbh
    have hkt : k = t := by omega
    subst hkt
    change Bool.casesOn (Nat.ble lo r) true (Bool.casesOn (Nat.ble (Nat.add r 1) hi) true
      (rangeWalk fuel rem r (terrasIter k r)
        (3 ^ countOnes (terrasParityVec k r)) (2 ^ k))) = true at hchk
    have hb1 : Nat.ble lo r = true := Nat.ble_eq.mpr (by omega)
    have hb2 : Nat.ble (Nat.add r 1) hi = true := Nat.ble_eq.mpr (by change r + 1 ≤ hi; omega)
    rw [hb1, hb2] at hchk; dsimp only at hchk
    exact rangeWalk_sound fuel rem k r hk hr hchk n hn1 hn2 hmod
  | succ top ih =>
    intro k r hk hsum hr hchk n hn1 hn2 hmod hbl hbh
    have hnk1 : 2 ^ (k + 1) ≤ n :=
      Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hn1
    exact stepChildren_sound (2 ^ (t + rem + 1))
      (fun m => 2 ^ (t + rem) ≤ m ∧ lo ≤ m % 2 ^ t ∧ m % 2 ^ t < hi)
      (rangeTop lo hi fuel rem top)
      (fun r' hr' h' n' hP _ hn2' hm =>
        ih (k + 1) r' (by omega) (by omega) hr' h' n' hP.1 hn2' hm hP.2.1 hP.2.2)
      hk r hr hchk n ⟨hn1, hbl, hbh⟩ hnk1 hn2 hmod

/-- One bucket of a shell: a successful `rangeTop` check from the root `(k = 1, r = 1)` gives
`HasFiniteStoppingTime n` for every odd `n` in `[2^(top+1+rem), 2^(top+1+rem+1))` whose residue
mod `2^(top+1)` lies in `[lo, hi)`. -/
theorem rangeShell_bucket_sound {lo hi fuel rem top : Nat}
    (hchk : rangeTop lo hi fuel rem top 1 2 3 2 = true) {n : Nat} (hodd : n % 2 = 1)
    (hlo : 2 ^ (top + 1 + rem) ≤ n) (hhi : n < 2 ^ (top + 1 + rem + 1))
    (hbl : lo ≤ n % 2 ^ (top + 1)) (hbh : n % 2 ^ (top + 1) < hi) :
    HasFiniteStoppingTime n :=
  rangeTop_sound lo hi fuel rem (top + 1) top 1 1 (by decide) (by omega) (by decide)
    (by simpa [terrasIter, terrasStep, terrasParityVec, countOnes] using hchk)
    n hlo hhi (by simpa using hodd) hbl hbh

/-- Even `n ≥ 2` drop on the first step. -/
theorem even_finiteStoppingTime {n : Nat} (hn : 2 ≤ n) (hev : n % 2 = 0) :
    HasFiniteStoppingTime n := by
  have h1 : terrasIter 1 n = n / 2 := by simp [terrasIter, terrasStep, hev]
  exact hasFiniteStoppingTime_of_terras_lt (k := 1) (by decide) (by rw [h1]; omega)

/-- Every odd `n` in the shell `[2^s, 2^(s+1))` with `lo ≤ n % 2^t < hi` has finite stopping
time. Generated shell files prove this per bucket and merge buckets with `shellCovers_merge`. -/
def ShellCovers (s t lo hi : Nat) : Prop :=
  ∀ n : Nat, n % 2 = 1 → 2 ^ s ≤ n → n < 2 ^ (s + 1) → lo ≤ n % 2 ^ t → n % 2 ^ t < hi →
    HasFiniteStoppingTime n

/-- A successful bucket check covers its bucket. -/
theorem shellCovers_of_check {lo hi fuel rem top : Nat}
    (h : rangeTop lo hi fuel rem top 1 2 3 2 = true) :
    ShellCovers (top + 1 + rem) (top + 1) lo hi :=
  fun _ hodd hlo hhi hbl hbh => rangeShell_bucket_sound h hodd hlo hhi hbl hbh

/-- Adjacent buckets merge. -/
theorem shellCovers_merge {s t a b c : Nat} (h1 : ShellCovers s t a b)
    (h2 : ShellCovers s t b c) : ShellCovers s t a c := by
  intro n hodd hlo hhi hbl hbh
  by_cases hb : n % 2 ^ t < b
  · exact h1 n hodd hlo hhi hbl hb
  · exact h2 n hodd hlo hhi (by omega) hbh

/-- A shell whose buckets cover every residue mod `2^t` is verified, even `n` included. -/
theorem shell_of_covers {s t : Nat} (hs : 1 ≤ s) (h : ShellCovers s t 0 (2 ^ t)) :
    ∀ n : Nat, 2 ^ s ≤ n → n < 2 ^ (s + 1) → HasFiniteStoppingTime n := by
  intro n hlo hhi
  have h2 : 2 ≤ n := Nat.le_trans (by simpa using Nat.pow_le_pow_right (by decide) hs) hlo
  rcases Nat.mod_two_eq_zero_or_one n with hev | hodd
  · exact even_finiteStoppingTime h2 hev
  · exact h n hodd hlo hhi (Nat.zero_le _) (Nat.mod_lt n (Nat.two_pow_pos t))

/-- Extending a verified range by one shell. -/
theorem finiteStoppingTime_extend {s : Nat}
    (hlow : ∀ n, 2 ≤ n → n < 2 ^ s → HasFiniteStoppingTime n)
    (hshell : ∀ n, 2 ^ s ≤ n → n < 2 ^ (s + 1) → HasFiniteStoppingTime n) :
    ∀ n, 2 ≤ n → n < 2 ^ (s + 1) → HasFiniteStoppingTime n := by
  intro n hn2 hn
  by_cases h : n < 2 ^ s
  · exact hlow n hn2 h
  · exact hshell n (by omega) hn

/-- The range already checked in `EliahouLifted22`, stated with a power of two. -/
theorem finiteStoppingTime_lt_two_pow_22 :
    ∀ n, 2 ≤ n → n < 2 ^ 22 → HasFiniteStoppingTime n :=
  fun _ hn2 hn => small_lt_4194304_finiteStoppingTime hn2 (by simpa using hn)

end SolveCollatz
