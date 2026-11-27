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

### `REF-004` — Structured 1-circuit (`k ≤ 5000`), exhaustive 2-circuit (`k ≤ 40`), 3-circuit (`k ≤ 24`), and `log₂(3)` CF convergent 1-circuit (`k ≤ 100000`) positive non-trivial cycles
- **Claim:** There exists a positive integer `n > 1` satisfying `(2^S - 3^k) n = C(v)` for a parity vector `v` in any of:
  1. 1-circuits `(1^{k-1}, S - k + 1)` with `1 ≤ k ≤ 5000` and `S_min(k) ≤ S < S_min(k) + 4` (`20,000` candidates),
  2. Exact continued-fraction upper convergents, upper semiconvergents, and `p_even + 1` lifts of `log₂(3)` with `1 ≤ k ≤ 100000` (`41` danger-zone `(S, k)` pairs across all `12` convergents up to `(125743, 79335)`),
  3. Canonical 2-circuits `((1^{k₁-1}, ℓ₁), (1^{k₂-1}, ℓ₂))` with `2 ≤ k ≤ 40` and `S_min(k) ≤ S ≤ ⌊k log₂(10/3)⌋` (`31,341` candidates),
  4. Canonical 3-circuits with `3 ≤ k ≤ 24` and `S_min(k) ≤ S ≤ ⌊k log₂(10/3)⌋` (`131,178` candidates).
- **Status:** `REFUTED` (exhaustively verified empty: `0` non-trivial positive cycles across `182,560` candidates; `deterministic_sha256 = c3b133363ebf08686dc5943faffe77780b9862b005f1295eee0421f3260a00a4`).
- **Witness / Reproducer:**
  ```bash
  python3 search/cycle_hunter.py --self-test --max-k 5000 --max-2circuit-k 40 --max-3circuit-k 24 --cf-max-k 100000 --log-json /tmp/disprove002_sweep.json
  ```
- **Takeaway:** Closest `2`-adic rational near-misses found in the bounded search were `x = 211/13` (`k=5, S=8`, 1-circuit, distance `3/13`), `(k=33, S=54)` (`2`-circuit, distance `≈ 2.47e-5`), and `(k=24, S=40)` (`3`-circuit, distance `≈ 5.98e-6`); Track B cycle hunting must push beyond `3`-circuits (e.g., LLL/lattice reduction or GPU/SIMD higher-`m` circuits beyond `k=40`).
