# `Collatz/Known/` — Formalized Literature Foundation

This directory houses self-contained, reusable Lean 4 formalizations of **established Collatz theorems** that both Track A (`Prove/`) and Track B (`Disprove/`) can import.

## Target Milestones (see `frontier/FRONTIER.toml`)

- **Parity vectors & Syracuse map** (`KNOWN-01`): Odd-step accelerated Syracuse map, `2`-adic parity vectors, and explicit affine orbit formula $T^k(n) = (3^{s} n + c) / 2^k$.
- **Terras (1976) / Everett (1977)** (`KNOWN-02`): Almost all positive integers (in natural density) have finite stopping time (drop strictly below $n$).
- **Cycle equation & Steiner / Simons–de Weger circuit bounds** (`KNOWN-03`): Exact Diophantine equation for $m$-cycles, Steiner's 1977 theorem ruling out nontrivial 1-cycles via Baker's theorem / linear forms in logarithms, and Hercher / Eliahou cycle length lower bounds.
- **Tao (2022) logarithmic-density theorem** (`KNOWN-04`): Almost all Collatz orbits attain almost bounded values (`f(n)` growing arbitrarily slowly) in logarithmic density — can interface with or cleanly ingest Apache-2.0 prior art such as `gotrevor/tao-collatz` where appropriate with full attribution.

## Rules

- **Zero `sorry`s** on `main` (use well-scoped, proved intermediate lemmas or interface hypotheses clearly marked as frontier nodes).
- Every theorem must cite the exact paper, theorem number, and hypotheses in its docstring.
- Keep everything cleanly usable by **both** tracks (e.g., Eliahou/Simons–de Weger cycle bounds narrow Track B's search space AND support Track A's no-nontrivial-cycle branch!).
