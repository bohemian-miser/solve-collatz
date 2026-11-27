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

### `REF-005` — Divergent orbit, cycle, or infinite stopping-time anomaly in `1 ≤ n ≤ 10⁸` or structured high-glide families `2^k·{1,3,27} - 1` (`k ≤ 120`)
- **Claim:** There exists a positive integer `1 ≤ n ≤ 10⁸` or a structured seed `n ∈ {2^k - 1, 3·2^k - 1, 27·2^k - 1}` (`1 ≤ k ≤ 120`) that fails to drop strictly below `n` (or diverges / enters a non-trivial cycle).
- **Status:** `REFUTED` (exhaustively verified empty: `0` counterexamples across `10⁸` integers + `360` structured seeds, `0` silent `__uint128_t` overflows; `deterministic_sha256 = 94c184c1d5f4766a82ebed4ee824541183a4618f88d0d33e59c04c62223b2fe9`).
- **Witness / Reproducer:**
  ```bash
  python3 search/glide_hunter/run_glide_hunter.py --range-end 100000000 --mersenne-max 120 --log-json /tmp/disprove003_1e8.json
  ```
  - **Sieve & Arithmetic Audit:** mod-$2^{16}$ affine drop table covers `63,422 / 65,536` residues (`96.77%`, `96,710,868` fast-skips in `1..10⁸`, max pre-drop threshold `24`, max pre-drop ratio `115.332`); `overflow_count = 0`; `u128_bigint_fallbacks = 124` (arbitrary-precision `bigint_t` verified up to `196`-bit peaks); throughput `299,362,169 seeds/s` (`0.334s` Mode 1, `0.004s` Mode 2, 16 threads).
  - **Verified Record Summary (`1 ≤ n ≤ 10⁸`):**
    | Record Type | Peak Seed `n` | Stopping Time `σ(n)` | Total Steps `τ(n)` | Peak Value | Peak Ratio `peak/n` |
    |---|---:|---:|---:|---:|---:|
    | Classic Anchor | `27` | `96` | `111` | `9,232` | `341.93×` |
    | Classic Anchor | `703` | `132` | `170` | `250,504` | `356.34×` |
    | Classic Glide Anchor | `9,663` | `88` | `184` | `27,114,424` | `2,806.00×` |
    | Max Stopping Time & Total Steps (`≤ 10⁸`) | `63,728,127` | `613` | `949` | `966,616,035,460` | `15,167.81×` |
    | Max Peak Ratio (`≤ 10⁸`) | `80,049,391` | `396` | `572` | `2,185,143,829,170,100` | `27,297,444.76×` |
  - **Structured High-Glide Stress Families (`1 ≤ k ≤ 120`, `360` seeds):** All `2^k - 1`, `3·2^k - 1`, and `27·2^k - 1` converge to `1` (max `σ = 810` at `2^{113}-1`, max `τ = 1649` at `2^{116}-1`, max glide `5.203×10^{21}×` at `2^{117}-1`, max `196`-bit peak).
- **Takeaway:** Any candidate Track A stopping-time bound `σ(n) ≤ f(n)` or peak bound can be red-teamed directly against the `63,728,127` / `80,049,391` / `2^{117}-1` stress seeds (`python3 search/barrier_redteam.py --check-stopping-bound ...`); Track B searches must look above `10⁸` or target structured Diophantine cycle families (`DISPROVE-002`).

### `REF-006` — Expanded Track B Phase 2 divergence, cycle, or infinite stopping-time anomaly in `1 ≤ n ≤ 5·10⁸` or Mersenne stress families `2^k·{1,3,27} - 1` (`k ≤ 500`)
- **Claim:** There exists a positive integer `1 ≤ n ≤ 5·10⁸` or a structured seed `n ∈ {2^k - 1, 3·2^k - 1, 27·2^k - 1}` (`1 ≤ k ≤ 500`) that fails to drop strictly below `n` (or diverges / enters a non-trivial cycle).
- **Status:** `REFUTED` (exhaustively verified empty: `0` counterexamples across `5·10⁸` integers + `1,500` structured seeds up to `k = 500`, with CI `--self-test` additionally verifying Mersenne families up to `k = 700` under strict RFC-8259 JSON serialization; `0` silent `__uint128_t` overflows; `overflow_count = 0`; `u128_bigint_fallbacks = 1,264`; `deterministic_sha256 = edf01115c8117f6dabf6726f4bfa78b815c2c278bb6ff51d70cbfcbdcef9b078`).
- **Witness / Reproducer:**
  ```bash
  python3 search/glide_hunter/run_glide_hunter.py --range-end 500000000 --mersenne-max 500 --threads 16 --log-json /tmp/disprove003_p2_5e8.json
  ```
- **Sieve & Arithmetic Audit:** mod-$2^{16}$ affine drop table covers `63,422 / 65,536` residues (`96.77%`, `483,808,039` fast-skips in `1..5·10⁸`, max pre-drop threshold `24`, max pre-drop ratio `115.332`); throughput `~775M–850M seeds/s` (`~0.64s` Mode 1, `~0.11s` Mode 2, 16 threads).
- **Verified Record Summary (`1 ≤ n ≤ 5·10⁸`):**
  | Record Type | Peak Seed `n` | Stopping Time `σ(n)` | Total Steps `τ(n)` | Peak Value | Peak Ratio `peak/n` |
  |---|---:|---:|---:|---:|---:|
  | Max Stopping Time (`≤ 5·10⁸`) | `217,740,015` | `644` | `793` | `2,516,021,527,120` | `11,555.16×` |
  | Max Total Steps (`≤ 5·10⁸`) | `226,588,897` | `3` | `956` | `966,616,035,460` | `4,265.95×` |
  | Max Peak Ratio (`≤ 5·10⁸`) | `319,804,831` | `427` | `592` | `1,414,236,446,719,942,480` | `4,422,186,001.06×` |
- **Structured High-Glide Stress Families (`1 ≤ k ≤ 500`, `1,500` seeds):** All `2^k - 1`, `3·2^k - 1`, and `27·2^k - 1` converge to `1` (max `σ = 3,185` at `2^{485}-1`, max `τ = 6,748` at `2^{500}-1`, max glide ratio at `2^{493}-1` with `log2_glide_ratio = 294.255688` [`788`-bit peak]; global `max_peak_bits = 799` attained at `27·2^{500}-1`).
- **Takeaway:** Phase 2 search confirms zero anomalies up to `5·10⁸` and `k = 500`, validating finite stopping times and strict numerical overflow safety (`[S2]` fixed via exact `log2_glide_ratio` and `peak_bits`).

### `REF-007` — Expanded Track B Phase 2 canonical `2`-circuit (`K ≤ 80`), `3`-circuit (`K ≤ 79`), and `4`-circuit (`K ≤ 58`) positive non-trivial cycles
- **Claim:** There exists a non-trivial positive integer cycle `n > 1` (`n_j ≥ 3` at every block entry) satisfying `(2^S - 3^K) n_0 = C(v)` across any canonical `m`-circuit in the exact Simons–de Weger positive band `S_min(K) ≤ S < K log₂(3) + m log₂(4/3)` (`2^S · 3^m < 4^m · 3^K`) for:
  1. Canonical `2`-circuits with `2 ≤ K ≤ 80` (`40,758` candidates),
  2. Canonical `3`-circuits with `3 ≤ K ≤ 79` (`19,921,732` candidates),
  3. Canonical `4`-circuits with `4 ≤ K ≤ 58` (`621,087,319` candidates).
- **Status:** `REFUTED` (exhaustively verified empty: `0` non-trivial positive cycles across `641,049,809` canonical `m`-circuits, `overflow_guard_skips = 0`; `deterministic_sha256 = 5d25f25ac908098fa2384f758a3e043776b802b7d8d4bfb65dac45b816d765bd`).
- **Witness / Reproducer:**
  ```bash
  python3 search/mcircuit_hunter/run_mcircuit_hunter.py --k2-max 80 --k3-max 79 --k4-max 58 --bound simons --threads 8 --json-out /tmp/disprove002_p2_sweep.json
  ```
- **Arithmetic & Cross-Verification Audit:** C11 engine (`-O3 -Wall -Wextra -Werror -std=c11 -pthread`, `elapsed_seconds = 2.934143` on 8 threads) with overflow-free `add_mod128`/`mul_mod128`, strict `K ≤ 80` and `S ≤ 127` guards, exact agreement with `search/cycle_hunter.py` on Eliahou-band `2`-circuits (`K ≤ 18`, `1,271` candidates) and `3`-circuits (`K ≤ 12`, `1,404` candidates), and zero ASan/UBSan findings.
- **Closest 2-Adic Rational Near-Misses:**
  - `2`-circuit (`K = 62, S = 99`): `k_vec = [14, 48]`, `l_vec = [31, 8]`, `dist_approx = 2.479911063979e-05`
  - `3`-circuit (`K = 54, S = 86`): `k_vec = [12, 25, 17]`, `l_vec = [10, 8, 17]`, `dist_approx = 4.758234805174e-09`
  - `4`-circuit (`K = 52, S = 83`): `k_vec = [10, 14, 13, 15]`, `l_vec = [16, 6, 3, 10]`, `dist_approx = 1.973063951232e-09`
- **Takeaway:** Extends `REF-004` (`2`-circuit `K ≤ 40`, `3`-circuit `K ≤ 24`) to `K ≤ 80` (`2`-circuit), `K ≤ 79` (`3`-circuit), and adds exhaustive `4`-circuit elimination up to `K ≤ 58` (`>3,500×` candidate volume). Pushing beyond `K = 80` or `m ≥ 5` requires multi-limb (`256`-bit+) modular arithmetic or lattice/LLL reduction in `DISPROVE-002` Phase 3.

### `REF-008` — Billion-scale Track B Phase 3 divergence, cycle, or infinite stopping-time anomaly in `1 ≤ n ≤ 10⁹`, Mersenne lifts `2^k·{1,3,27} - 1`, and Terras/Roosendaal high-glide lifts `2^k·{703,9663,77671,319804831} - 1` (`k ≤ 1000`)
- **Claim:** There exists a positive integer `1 ≤ n ≤ 10⁹` or a structured seed in the `7` high-glide families `2^k·{1,3,27} - 1` (Mersenne lifts) and `2^k·{703,9663,77671,319804831} - 1` (Terras/Roosendaal record-glide lifts) for `1 ≤ k ≤ 1000` that fails to drop strictly below `n` (or diverges / enters a non-trivial cycle).
- **Status:** `REFUTED` (exhaustively verified empty: `0` counterexamples across `10⁹` integers + `7,000` structured seeds up to `k = 1000`, `0` silent `__uint128_t` overflows; `overflow_count = 0`; `u128_bigint_fallbacks = 6,489`; `deterministic_sha256 = 6e85b0e9bf1a27785243d94b9b11716778fe593528101521c34e96a26fc50510`).
- **Witness / Reproducer:**
  ```bash
  taskset -c 8-15 python3 search/glide_hunter/run_glide_hunter.py --range-end 1000000000 --mersenne-max 1000 --sieve-bits 18 --threads 8 --log-json /tmp/disprove003_p3_1e9.json
  ```
- **Sieve & Arithmetic Audit:**
  - Upgraded mod-$2^{18}$ (`262,144`) affine drop table covers `254,649 / 262,144` residues (`97.1409%`, `971,154,212` fast-skips in `1..10⁹`, max pre-drop steps `29`, max threshold `n_min = 24`, max pre-drop ratio `< 173`) paired with a `32 KiB` L1-resident fast-skip bitset for `n ≥ 2.5·10⁸` (`1.259s` Mode 1 / `793,980,270 seeds/s`, `0.995s` Mode 2 on 8 pinned cores; vs `1.363s` / `733,497,386 seeds/s` under `--sieve-bits 16` with `63,422 / 65,536 = 96.7743%` coverage and `967,679,498` fast-skips).
  - Cross-verified `--sieve-bits 0` (brute force) ≡ `--sieve-bits 16` ≡ `--sieve-bits 18` bit-for-bit on `1..2,000,000`, `threads=1` ≡ `threads=8` ≡ ASan+UBSan `deterministic_sha256` on `1..5,000,000 + k ≤ 1000`, zero ASan/UBSan findings, strict RFC-8259 JSON (`allow_nan=False`), explicit `--max-steps` budget diagnostic check, and pure-Python `int` verification of every reported record seed.
- **Verified Record Summary (`1 ≤ n ≤ 10⁹`):**
  | Record Type | Peak Seed `n` | Stopping Time `σ(n)` | Total Steps `τ(n)` | Peak Value | Peak Ratio `peak/n` |
  |---|---:|---:|---:|---:|---:|
  | Max Stopping Time (`1 ≤ n ≤ 10⁹`) | `217,740,015` | `644` | `793` | `2,516,021,527,120` | `11,555.16×` |
  | Max Peak Ratio (`1 ≤ n ≤ 10⁹`) | `319,804,831` | `427` | `592` | `1,414,236,446,719,942,480` | `4,422,186,001.06×` |
  | Max Total Steps (`n ≤ 249,999,999` [`tau_exact_up_to`]) | `226,588,897` | `3` | `956` | `966,616,035,460` | `4,265.95×` |
  | Literature Total-Steps Stress Anchor (`> tau_exact_up_to`, Python-verified) | `670,617,279` | `29` | `986` | `966,616,035,460` | `1,441.38×` |
- **Structured High-Glide Stress Families (`1 ≤ k ≤ 1000`, `7,000` seeds across 7 families):** All `2^k·{1,3,27,703,9663,77671,319804831} - 1` converge to `1` (`max σ = 6,786` at `2^{997}-1`, `max τ = 14,241` at `2^{998}-1`, `max log2_glide_ratio = 592.436188` at `2^{997}-1` [`1,590`-bit peak], global `max_peak_bits = 1,617` attained at `319,804,831·2^{1000}-1`).
- **Takeaway:** Extends exhaustive Collatz stopping-time & peak-glide verification to `10⁹` and structured `k ≤ 1000` (`1,617`-bit peaks) with `794M seeds/s` on 8 cores; `search/barrier_redteam.py` now includes all `≤ 10⁹` record stress seeds (including `217,740,015`, `319,804,831`, and `670,617,279`).

### `REF-009` — Track B Phase 3 `256`-bit multi-limb `m`-circuit elimination (`m = 2` `K ≤ 160`, `m = 3` `K ≤ 100`, `m = 4` `K ≤ 60`, `m = 5` `K ≤ 38`)
- **Claim:** There exists a non-trivial positive integer cycle `n > 1` (`n_j ≥ 3` at every block entry) satisfying `(2^S - 3^K) n_0 = C(v)` across any canonical `m`-circuit in the exact Simons–de Weger positive band `S_min(K) ≤ S < K log₂(3) + m log₂(4/3)` (`2^S · 3^m < 4^m · 3^K`) for:
  1. Canonical `2`-circuits with `2 ≤ K ≤ 160` (`325,481` candidates; `S ≤ 254`),
  2. Canonical `3`-circuits with `3 ≤ K ≤ 100` (`68,007,503` candidates; `S ≤ 160`),
  3. Canonical `4`-circuits with `4 ≤ K ≤ 60` (`770,929,000` candidates),
  4. Canonical `5`-circuits with `5 ≤ K ≤ 38` (`929,830,342` candidates; exact `243 · 2^S < 1024 · 3^K` band).
- **Status:** `REFUTED` (exhaustively verified empty: `0` non-trivial positive cycles across `1,769,092,326` canonical `m`-circuits, `overflow_guard_skips = 0`; `deterministic_sha256 = 3f981c8c64ef82de10aa347559078ffc4e9c876e267d587912ababc6dd32f550`).
- **Witness / Reproducer:**
  ```bash
  taskset -c 12-15 python3 search/mcircuit_hunter/run_mcircuit_hunter.py --k2-max 160 --k3-max 100 --k4-max 60 --k5-max 38 --bound simons --threads 4 --json-out /tmp/disprove002_p3_sweep.json
  ```
- **Arithmetic & Cross-Verification Audit:**
  - C11 engine (`-O3 -Wall -Wextra -Werror -std=c11 -pthread`, `elapsed_seconds = 7.754753` on 4 pinned cores) combining `u128` (`K ≤ 80, S ≤ 127`) with overflow-free multi-limb `u256_t` (`K ≤ 160, S ≤ 255`) and exact `u640_t` precomputation/hit recovery.
  - Bit-for-bit `deterministic_sha256` equivalence verified between `u256` (`--force-u256`) and `u128` on `m = 2 (K ≤ 80)`, `m = 3 (K ≤ 40)`, `m = 4 (K ≤ 20)` (`sha256 = cd408a958a3a7427...`), exact `m = 5 (K ≤ 12, 9,875 candidates)` cross-verification against independent pure-Python Simons enumeration, exact `REF-007` count match (`641,049,809` on `m = 2..4`), and bit-for-bit identical `deterministic_sha256` across `threads = 1`, `threads = 4`, and `ASan+UBSan` (`9,819,716`-candidate subset, `sha256 = 309c457c586c53ab...`, `0` sanitizer findings).
- **Closest 2-Adic Rational Near-Misses:**
  - `2`-circuit (`K = 126, S = 200`): `k_vec = [24, 102]`, `l_vec = [16, 60]`, `dist_approx = 2.766715634313e-06`
  - `3`-circuit (`K = 54, S = 86`): `k_vec = [12, 25, 17]`, `l_vec = [10, 8, 17]`, `dist_approx = 4.758234805174e-09` (best `u256` shell `K = 99, S = 157`: `k_vec = [9, 21, 69]`, `l_vec = [5, 46, 10]`, `dist_approx = 1.446920717900e-08`)
  - `4`-circuit (`K = 52, S = 83`): `k_vec = [10, 14, 13, 15]`, `l_vec = [16, 6, 3, 10]`, `dist_approx = 1.973063951232e-09`
  - `5`-circuit (`K = 38, S = 62`): `k_vec = [2, 24, 2, 6, 4]`, `l_vec = [2, 10, 4, 8, 5]`, `dist_approx = 6.098330324666e-10`
- **Takeaway:** Breaks the `K = 80 / S = 127` `u128` ceiling via `u256_t` (`K ≤ 160 / S ≤ 255`), doubles `2`-circuit elimination to `K ≤ 160`, pushes `3`-circuits to `K ≤ 100`, pushes `4`-circuits to `K ≤ 60`, and exhaustively refutes canonical `5`-circuits up to `K ≤ 38` (`1.769B` total candidates, `0` skips, `0` hits); any hit automatically emits a kernel-ready `SolveCollatz.Disprove.NontrivialCycleCert`. Further reach (`m ≥ 6` or `K > 160`) requires LLL/lattice reduction or `u512` modular arithmetic.

### `REF-010` — Five-billion-scale Track B Phase 4 divergence, cycle, or infinite stopping-time anomaly in `1 ≤ n ≤ 5·10⁹`, Mersenne lifts `2^k·{1,3,27} - 1`, and Terras/Roosendaal high-glide lifts `2^k·{703,9663,77671,319804831} - 1` (`k ≤ 1500`)
- **Claim:** There exists a positive integer `1 ≤ n ≤ 5·10⁹` or a structured seed in the `7` high-glide families `2^k·{1,3,27} - 1` (Mersenne lifts) and `2^k·{703,9663,77671,319804831} - 1` (Terras/Roosendaal record-glide lifts) for `1 ≤ k ≤ 1500` that fails to drop strictly below `n` (or diverges / enters a non-trivial cycle).
- **Status:** `REFUTED` (exhaustively verified empty: `0` counterexamples across `5·10⁹` integers + `10,500` structured seeds up to `k = 1500`, `0` silent `__uint128_t` overflows; `overflow_count = 0`; `u128_bigint_fallbacks = 9,989`; `deterministic_sha256 = fd113c47838fdd6865deccf30f09871d8879d133299d09331d6611f7aaadb51e`; full log at `search/logs/glide_sweep_5e9_ref010.json`).
- **Witness / Reproducer:**
  ```bash
  taskset -c 112-119 python3 search/glide_hunter/run_glide_hunter.py --range-end 5000000000 --mersenne-max 1500 --sieve-bits 20 --threads 8 --log-json search/logs/glide_sweep_5e9_ref010.json
  ```
- **Sieve & Arithmetic Audit:**
  - Upgraded mod-$2^{20}$ (`1,048,576`) affine drop table with `u128` intermediate sieve construction covers `1,021,248 / 1,048,576` residues (`97.3938%`, `4,868,668,705` fast-skips in `1..5·10⁹`, max threshold `n_min = 24`) paired with a `128 KiB` L2-resident fast-skip bitset for `n ≥ 2.5·10⁸` (`4.071289s` Mode 1 / `1,228,112,368 seeds/s`, `2.428059s` Mode 2, `7.532s` total wall time on 8 pinned cores).
  - Cross-verified `--sieve-bits 0` (brute force) ≡ `--sieve-bits 18` ≡ `--sieve-bits 20` exact records on `1..500,000`, `1..1,000,000`, and `1..1,200,000` (crossing `2^20`), `threads=1` ≡ `threads=8` ≡ ASan+UBSan `deterministic_sha256` on `1..200,000 + k ≤ 800` (`698d0adf748fb9a6`) and `1..1,200,000 + k ≤ 800` (`489a07ffa9e8859d`) with `0` sanitizer errors, strict RFC-8259 JSON via `scripts/native_cache.py`, and pure-Python `int` verification of every reported record seed.
- **Verified Record Summary (`1 ≤ n ≤ 5·10⁹`):**
  | Record Type | Peak Seed `n` | Stopping Time `σ(n)` | Total Steps `τ(n)` | Peak Value | Peak Ratio `peak/n` |
  |---|---:|---:|---:|---:|---:|
  | Max Stopping Time (`1 ≤ n ≤ 5·10⁹`) | `2,788,008,987` | `729` | `944` | `81,887,769,175,732` | `29,371.42×` |
  | Intermediate Stopping-Time Record | `1,827,397,567` | `706` | `928` | `118,736,698,851,769,012` | `64,975,843.79×` |
  | Max Peak Ratio (`1 ≤ n ≤ 5·10⁹`) | `1,410,123,943` | `590` | `770` | `7,125,885,122,794,452,160` | `5,053,375,030.02×` |
  | Max Total Steps (`n ≤ 249,999,999` [`tau_exact_up_to`]) | `226,588,897` | `3` | `956` | `966,616,035,460` | `4,265.95×` |
- **Structured High-Glide Stress Families (`1 ≤ k ≤ 1500`, `10,500` seeds across 7 families):** All `2^k·{1,3,27,703,9663,77671,319804831} - 1` converge to `1` (`max σ = 9,901` at `9663·2^{1492}-1`, `max τ = 20,696` at `319804831·2^{1500}-1`, `max log2_glide_ratio = 880.162551` at `77671·2^{1500}-1` [`2,408`-bit peak], global `max_peak_bits = 2,408`).
- **Takeaway:** Extends exhaustive Collatz stopping-time & peak-glide verification to `5·10⁹` (`1.228B seeds/s` on 8 cores via mod-$2^{20}$ sieve + `128 KiB` L2 bitset) and structured `k ≤ 1500` (`2,408`-bit peaks, `0` overflows), with `scripts/native_cache.py` unified across both Track B C11 wrappers.

### `REF-011` — Track B Phase 4 `512`-bit multi-limb & canonical `6`-circuit elimination (`m = 2` `K ≤ 240`, `m = 3` `K ≤ 120`, `m = 4` `K ≤ 70`, `m = 5` `K ≤ 44`, `m = 6` `K ≤ 32`)
- **Claim:** There exists a non-trivial positive integer cycle `n > 1` (`n_j ≥ 3` at every block entry) satisfying `(2^S - 3^K) n_0 = C(v)` across any canonical `m`-circuit in the exact Simons–de Weger positive band `S_min(K) ≤ S < K log₂(3) + m log₂(4/3)` (`2^S · 3^m < 4^m · 3^K`) for:
  1. Canonical `2`-circuits with `2 ≤ K ≤ 240` (`1,115,241` candidates; `S ≤ 381`, breaking the `u256_t` `K = 160` barrier via `u512_t`),
  2. Canonical `3`-circuits with `3 ≤ K ≤ 120` (`165,925,492` candidates; `S ≤ 192`),
  3. Canonical `4`-circuits with `4 ≤ K ≤ 70` (`2,392,613,795` candidates),
  4. Canonical `5`-circuits with `5 ≤ K ≤ 44` (`3,846,813,721` candidates; exact `243 · 2^S < 1024 · 3^K` band),
  5. Canonical `6`-circuits with `6 ≤ K ≤ 32` (`2,819,460,829` candidates; exact `729 · 2^S < 4096 · 3^K` band).
- **Status:** `REFUTED` (exhaustively verified empty: `0` non-trivial positive cycles across `9,225,929,078` canonical `m`-circuits, `overflow_guard_skips = 0`; `deterministic_sha256 = 274ce899f21659cc7674f8071f2a9dec42d6bb1d89c389d2d1f1c548918de4ae`; full log at `search/logs/mcircuit_sweep_ref011.json`).
- **Witness / Reproducer:**
  ```bash
  taskset -c 116-119 python3 search/mcircuit_hunter/run_mcircuit_hunter.py --k2-max 240 --k3-max 120 --k4-max 70 --k5-max 44 --k6-max 32 --bound simons --threads 4 --json-out search/logs/mcircuit_sweep_ref011.json
  ```
- **Arithmetic & Cross-Verification Audit:**
  - C11 engine (`-O3 -Wall -Wextra -Werror -std=c11 -pthread`, `elapsed_seconds = 48.673685` on 4 pinned cores) with 3-tier dispatch: `u128` (`K ≤ 80, S ≤ 127`), `u256_t` (`K ≤ 160, S ≤ 255`), and `u512_t` (`K ≤ 256, S ≤ 511`), plus exact `u1024_t` precomputation and hit recovery.
  - Bit-for-bit `deterministic_sha256` equivalence verified across `u128 == u256 == u512` on `m = 2..6` (`m = 2 K ≤ 50, m = 3 K ≤ 20, m = 4 K ≤ 14, m = 5 K ≤ 12, m = 6 K ≤ 12`, `sha256 = 3887fbf7d3fda874`), exact Simons-band cross-verification against independent pure-Python exact-bigint enumeration for all `m = 2..6` (`m=2 K≤20: 583`, `m=3 K≤15: 4,227`, `m=4 K≤10: 930`, `m=5 K≤12: 9,875`, `m=6 K≤13: 34,550`), exact `cycle_hunter.py` Eliahou agreement (`m=2 K≤18: 1,271`, `m=3 K≤12: 1,404`), and bit-for-bit identical `deterministic_sha256` across `threads = 1`, `threads = 4`, and `ASan+UBSan` (`1,217,351`-candidate subset including `m = 2 K ≤ 240` and `m = 6 K ≤ 13`, `sha256 = 5d243be254041105`, `0` sanitizer errors).
- **Closest 2-Adic Rational Near-Misses:**
  - `2`-circuit (`K = 216, S = 343`): `k_vec = [13, 203]`, `l_vec = [32, 97]`, `dist_approx = 3.093742840986e-07`
  - `3`-circuit (`K = 116, S = 185`): `k_vec = [14, 75, 27]`, `l_vec = [37, 21, 14]`, `dist_approx = 3.06034097069e-09`
  - `4`-circuit (`K = 64, S = 102`): `k_vec = [4, 31, 25, 4]`, `l_vec = [4, 6, 18, 14]`, `dist_approx = 1.312691683853e-11`
  - `5`-circuit (`K = 44, S = 71`): `k_vec = [2, 7, 16, 16, 3]`, `l_vec = [10, 2, 4, 9, 7]`, `dist_approx = 5.190573340752e-12`
  - `6`-circuit (`K = 32, S = 52`): `k_vec = [2, 2, 8, 12, 3, 5]`, `l_vec = [4, 6, 5, 4, 3, 4]`, `dist_approx = 6.022192645138e-11`
- **Takeaway:** Breaks the `K = 160 / S = 255` `u256_t` ceiling via `u512_t` (`K ≤ 256, S ≤ 511`) + `u1024_t` exact verification, pushes `2`-circuits to `K ≤ 240`, `3`-circuits to `K ≤ 120`, `4`-circuits to `K ≤ 70`, `5`-circuits to `K ≤ 44`, and introduces exhaustive canonical `6`-circuit elimination up to `K ≤ 32` (`9.226B` total candidates, `5.21×` `REF-009` volume, `0` skips, `0` hits), with `SolveCollatz.Disprove.NontrivialCycleCert` schema verified across `m = 1..6`. Further reach (`m ≥ 7` or higher `K`) requires LLL/lattice reduction or GPU acceleration.

### `REF-012` — Ten-billion-scale Track B Phase 5 divergence, cycle, or infinite stopping-time anomaly in `1 ≤ n ≤ 10¹⁰` and `12` structured high-glide lift families (`k ≤ 2000`)
- **Claim:** There exists a positive integer `1 ≤ n ≤ 10¹⁰` or a structured seed in the `12` high-glide families — Mersenne lifts `2^k·{1,3,27} - 1`, extended lifts `2^k·{5,7,9} - 1`, `2^k + 1`, `2^k - 3` (`k ≥ 2`), and Terras/Roosendaal record-glide lifts `2^k·{703,9663,77671,319804831} - 1` — for `1 ≤ k ≤ 2000` (`23,999` seeds) that fails to drop strictly below `n` (or diverges / enters a non-trivial cycle).
- **Status:** `REFUTED` (exhaustively verified empty: `0` counterexamples across `10¹⁰` integers + `23,999` structured seeds up to `k = 2000`, `0` silent overflows; `overflow_count = 0`; `u128_bigint_fallbacks = 23,048`; `deterministic_sha256 = f8f8d7943805eadb5f0175bc46c12c6f91d6415c030dd4e4b2a0ca2694c1251f`; full log at `search/logs/glide_sweep_1e10_ref012.json`).
- **Witness / Reproducer:**
  ```bash
  taskset -c 116-119 python3 search/glide_hunter/run_glide_hunter.py --range-end 10000000000 --mersenne-max 2000 --sieve-bits 24 --threads 4 --log-json search/logs/glide_sweep_1e10_ref012.json
  ```
- **Sieve & Arithmetic Audit:**
  - Upgraded to `uint64_t → __uint128_t → bigint_t` 3-tier exact arithmetic (`0` silent overflows) + mod-$2^{24}$ (`16,777,216`) affine drop sieve covering `16,490,635 / 16,777,216` residues (`98.2918%`, `9,812,693,796` fast-skips in `1..10¹⁰`, max pre-drop steps `39`, max threshold `n_min = 24`, max pre-drop ratio `< 876`) with direct `g_uncovered[]` (`286,581` residues = `1.7082%`) jump traversal for `n ≥ max(tau_cap, 2^B)` (`4.547942s` Mode 1 / `2,198,796,632 seeds/s`, `0.793161s` parallel Mode 2, `6.307s` total wall time on `4` pinned cores `116–119`).
  - Cross-verified `--sieve-bits 0` (brute force) ≡ `24` bit-identically on `1..20,000,000` (crossing `2²⁴`), `--sieve-bits 0 ≡ 16 ≡ 18 ≡ 20 ≡ 22 ≡ 24` on `1..1,200,000`, Phase B (`300M > TAU_CACHE_CAP`) `1t ≡ 4t` and `--sieve-bits 20 ≡ 24`, `1t ≡ 4t ≡ ASan+UBSan` bit-identical `deterministic_sha256` on `1..2,000,000 + k ≤ 200` (`05b6af9d95d8df69`) and CI `--self-test` (`2ff777514f64dad2`, `0` sanitizer errors), strict RFC-8259 JSON via `scripts/native_cache.py`, and independent pure-Python `int` verification of all `100` unique Mode 1 record seeds, all `264` Mode 2 sample orbits, and all `3` Mode 2 global champions.
- **Verified Record Summary (`1 ≤ n ≤ 10¹⁰`):**
  | Record Type | Peak Seed `n` | Stopping Time `σ(n)` | Total Steps `τ(n)` | Peak Value | Peak Ratio `peak/n` |
  |---|---:|---:|---:|---:|---:|
  | Max Stopping Time (`1 ≤ n ≤ 10¹⁰`) | `2,788,008,987` | `729` | `944` | `81,887,769,175,732` | `29,371.42×` |
  | Intermediate Stopping-Time Record | `1,827,397,567` | `706` | `928` | `118,736,698,851,769,012` | `64,975,843.79×` |
  | Max Peak Ratio (`1 ≤ n ≤ 10¹⁰`) | `1,410,123,943` | `590` | `770` | `7,125,885,122,794,452,160` | `5,053,375,030.02×` |
  | Max Total Steps (`n ≤ 249,999,999` [`tau_exact_up_to`]) | `226,588,897` | `3` | `956` | `966,616,035,460` | `4,265.95×` |
- **Structured High-Glide Stress Families (`1 ≤ k ≤ 2000`, `23,999` seeds across 12 families):** All `2^k·{1,3,5,7,9,27,703,9663,77671,319804831} - 1`, `2^k + 1`, and `2^k - 3` (`k ≥ 2`) converge to `1` (`max σ = 13,711` at `7·2^{1900}-1`, `max τ = 28,128` at `5·2^{1994}-1`, `max log2_glide_ratio = 1175.398689` at `3·2^{2000}-1`, global `max_peak_bits = 3,201` attained at `319,804,831·2^{2000}-1`).
- **Takeaway:** Extends exhaustive Collatz stopping-time & peak-glide verification by `2×` over `REF-010` (`10×` over `REF-008`) to `10¹⁰` (`2.199B seeds/s` on 4 pinned cores via mod-$2^{24}$ uncovered-residue jump sieve + 3-tier `u64/u128/bigint_t` arithmetic) and `23,999` structured lifts up to `k ≤ 2000` (`3,201`-bit peaks, `0` overflows).
