# `search/` — High-Speed Off-Kernel Search & Barrier Red-Teaming

Lean 4's kernel is the **judge**, not the search engine. This directory hosts fast off-kernel tools (Python, and optionally Rust/C++/SAT/LLL modules) that serve two critical roles for the swarm:

1. **Automated Barrier Red-Teaming (`barrier_redteam.py`)**
   - Tests candidate Track A conjectures, potential/Lyapunov functions, and invariants against known counterexample maps (`3n - 1`, `5n + 1`, negative-integer Collatz) formalized in `Collatz/Core/GeneralMaps.lean`.
   - Catches flawed Track A ideas in **milliseconds** before an agent burns compute trying to formalize a false lemma.
   - Usage:
     ```bash
     python3 search/barrier_redteam.py --verify-barriers
     ```

2. **Structured Cycle & Invariant Hunting (`cycle_hunter.py`)**
   - Explores rational and integer cycle equations derived from parity vectors and continued-fraction / lattice approximations to $\log_2 3$, as well as testing certificate emitters against generalized maps (`3n - 1`, `5n + 1`) to verify the certificate pipeline end-to-end.
   - If a true `3n + 1` nontrivial integer cycle is ever found, it emits a Lean 4 `NontrivialCycleCert` ready for kernel verification in `Collatz/Disprove/`.
   - Usage:
     ```bash
     python3 search/cycle_hunter.py --max-k 400
     ```

## Extending `search/`

- Build and run compiled engines through `search/engine.py` (`compile_c`, `run_json_engine`, `check_thread_determinism`); `search/example_engine/` is a minimal engine to copy.
- Keep CI smoke-test modes fast (< 5 seconds) and deterministic.
- Never claim a Track B discovery from raw search output alone: a finding only counts once Lean verifies `SolveCollatz.CollatzDisproof` with standard axioms only.
- When a structured search family is exhausted or proven empty, record the exact range/family in `frontier/REFUTED.md` or formalize the ruling-out lemma in `Collatz/Known/`!
