# The Five Collatz Barriers (Mandatory Filter for Track A `Prove/`)

Every proposed proof strategy or intermediate conjecture on Track A (`Collatz/Prove/`) **must explain why it breaks on each of these five barrier regimes**. Four of the five are already known to admit counterexamples (the first three are **formally proved in `Collatz/Core/GeneralMaps.lean`**).

| # | Barrier Regime | Concrete Counterexample / Fact | What It Kills |
|---|---|---|---|
| **1** | **`3n - 1` on `ℕ⁺`** | `5 → 14 → 7 → 20 → 10 → 5` (`three_n_minus_one_cycle_5`), plus `17 → … → 17` | Any parity/drift-only argument that ignores the sign of `+1` vs `-1`. |
| **2** | **`5n + 1` on `ℕ⁺`** | `13 → 66 → 33 → 166 → 83 → 416 → 208 → 104 → 52 → 26 → 13` (`five_n_plus_one_cycle_13`) | Any purely algebraic/modular argument that does not use the negative average log-drift `log₂(3/4) < 0` (since `log₂(5/4) > 0`). |
| **3** | **`3n + 1` on `ℤ_{<0}`** | `-5 → -14 → -7 → -20 → -10 → -5` (`neg_int_cycle_neg5`), plus `-1` and `-17` | Any argument using only the ring arithmetic of `ℤ` without positivity (`0 < n`). |
| **4** | **`3n + 1` on `ℤ₂` ($2$-adic integers)** | Every finite parity vector `v` gives a unique rational `2`-adic periodic point `x = C(v) / (2^S - 3^k) ∈ ℤ₂` | Any purely `2`-adic / local congruence / finite-automaton argument: locally in `ℤ₂`, cycles are dense! Any proof MUST use the global integrality + archimedean positivity of `ℕ⁺`. |
| **5** | **Conway (1972) Undecidability** | Generalized piecewise-affine maps `T(n) = a_i n + b_i` (`n ≡ i mod P`) simulate arbitrary Minsky machines, so halting is undecidable | Any generic local syntactic / induction schema that works uniformly for arbitrary periodic piecewise-affine maps. |

## How Swarms Must Use This File
1. Before opening a Track A conjecture or proof PR, run `python3 search/barrier_redteam.py` on your proposed invariant/predicate.
2. In your PR's `Quality pass: Q4`, explicitly state which of the 5 barriers your lemma distinguishes and why it fails on the excluded regimes.
