# Negative Knowledge Base (`REFUTED` & `BARRIER_BLOCKED` Conjectures)

This file is as important as `Collatz/` itself. In an open-problem swarm, **recording disproved conjectures and dead-end invariants with exact counterexamples prevents hundreds of agents from rediscovering and retrying the same failure.**

## Entry Format
Every entry must include:
- **ID:** `REF-NNN`
- **Claim:** Exact statement (mathematical + Lean syntax if applicable)
- **Status:** `REFUTED` (concrete counterexample on `3n+1`, `ℕ⁺`) or `BARRIER_BLOCKED` (holds equally on `3n-1`, `5n+1`, `ℤ_{<0}`, or `ℤ₂`)
- **Witness / Reproducer:** Exact integer, parity vector, or command (`python3 search/barrier_redteam.py ...`)

---

## Seed Entries (Classic Swarm Traps)

### `REF-001` — Naive Lyapunov function `Φ(n) = log(n)` decreases on every odd-to-odd Syracuse step
- **Status:** `REFUTED`
- **Witness:** `n = 3 → 10 → 5` (`5 > 3`), and arbitrarily long rising sequences exist for `n = 2^k - 1` (`2^k - 1 → 3·2^{k-1} - 1 → … → 3^k - 1`).
- **Takeaway:** Descent can only hold *on average* (drift `log₂(3/4) < 0` over random parity vectors) or after unbounded stopping times, never pointwise per step.

### `REF-002` — Pure modular covering system (`∃ M, ∀ r mod M, ...`) forces finite stopping time for all `n`
- **Status:** `BARRIER_BLOCKED` (Barrier 4: `ℤ₂`)
- **Witness:** For every modulus `2^k`, the residue class `n ≡ -1 (mod 2^k)` takes `k` consecutive odd steps without decreasing (`2^k - 1 → 3^k - 1`). More generally, every finite parity vector determines a periodic point in `ℤ₂`, so no finite modulus `2^k` can force contraction on all classes.
- **Takeaway:** Residue-class sieves can cover density `1 - ε` (Terras/Krasikov–Lagarias) or prune search trees, never `100%` of `ℕ⁺` without global archimedean/Diophantine input.

### `REF-003` — Pure arithmetic identity on `(2^S - 3^k) n = C(v)` without archimedean positivity rules out cycles
- **Status:** `BARRIER_BLOCKED` (Barrier 1 & 3: `3n - 1` and `ℤ_{<0}`)
- **Witness:** `Collatz/Core/GeneralMaps.lean` (`three_n_minus_one_cycle_5`: `5` is a 5-step cycle for `3n-1`; `neg_int_cycle_neg5`: `-5` is a 5-step cycle for `3n+1` in `ℤ_{<0}`).
- **Takeaway:** Any cycle-elimination proof must explicitly exploit positivity (`0 < n`) together with the `+1` sign (e.g. Steiner/Baker lower bounds on `|2^S - 3^k|`).
