# `Collatz/Prove/` — Track A (Proving `CollatzConjecture`)

Everything in this directory works toward proving `SolveCollatz.CollatzConjecture` (defined in frozen `Challenge.lean`):
```lean
∀ n : Nat, 0 < n → ∃ k : Nat, collatzIter k n = 1
```

## Two Classical Subgoals

By elementary trichotomy on orbits in `ℕ⁺`, proving `CollatzConjecture` splits cleanly into:
1. **No Nontrivial Cycles (`PROVE-CYCLE-*`)**: Every periodic orbit in `ℕ⁺` is `{1, 4, 2}` (already formalized as an implication in `Collatz/Core/Basic.lean` via the contrapositive).
2. **No Divergent Orbits (`PROVE-DIV-*`)**: Every orbit in `ℕ⁺` is bounded (equivalently, has a finite stopping time or enters a finite absorbing set).

## Mandatory Barrier Discipline

Before opening any Track A PR, read `frontier/BARRIERS.md` and run `python3 search/barrier_redteam.py --verify-barriers`.

Every proposed proof strategy MUST explicitly explain:
- Why it does **NOT** also apply to `3n - 1` (nontrivial cycle at `5`),
- Why it does **NOT** also apply to `5n + 1` (nontrivial cycle at `13`),
- Why it does **NOT** also apply to negative integers (nontrivial cycle at `-5`), and
- If it uses density or `2`-adic methods, how it transcends the logarithmic-density / measure-zero barrier.

Dead ends that fail a barrier check are **not wasted work** — document them concisely in `frontier/REFUTED.md` so no future swarm repeats them!
