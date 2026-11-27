# `Collatz/Disprove/` — Track B (Proving `CollatzDisproof := ¬ CollatzConjecture`)

Everything in this directory works toward proving `SolveCollatz.CollatzDisproof` (defined in frozen `Challenge.lean`):
```lean
¬ SolveCollatz.CollatzConjecture
```

## Two Routes to a Disproof

1. **Concrete Nontrivial Cycle Certificate (`Cert.lean`, `DISPROVE-CYCLE-*`)**
   - `Collatz/Disprove/Cert.lean` already provides `NontrivialCycleCert` and a **kernel-verified** theorem:
     ```lean
     theorem NontrivialCycleCert.disproves_collatz (cert : NontrivialCycleCert) :
         SolveCollatz.CollatzDisproof
     ```
   - Any external high-speed search engine (Python, Rust, C++, GPU, SMT/SAT, LLL/lattice reduction) in `search/` can hunt for rational/integer cycles or near-cycles without touching Lean. If it ever finds a genuine integer cycle, it emits a single tiny Lean certificate file — and Lean's kernel verifies `CollatzDisproof` automatically!
   - **Important:** Do NOT use `native_decide` or `Lean.ofReduceBool` to verify certificates. For huge cycles, provide structured step-by-step arithmetic certificates (e.g., Syracuse compressed blocks or modular/affine composition proofs) verified strictly by the Lean kernel.

2. **Certified Divergent Orbit (`DISPROVE-DIV-*`)**
   - Prove the existence of an `n > 0` whose orbit never hits `1` — e.g., via an invariant inductive set `S ⊆ ℕ⁺` with `1 ∉ S`, `n ∈ S`, and `∀ x ∈ S, collatzStep x ∈ S`, or a strictly increasing subsequence on a structured family of residues.
   - `Collatz/Core/Basic.lean` already proves `collatzDisproof_of_hasDivergentOrbit`.

## Grounding in Computational Bounds

Any serious Track B search should build on known computational lower bounds (convergence verified past $2^{71}$; nontrivial cycle length $> 10^{11}$ under Baker/Eliahou/Hercher bounds). Searches in `search/` should therefore target **structured algebraic families** (Syracuse parity patterns, continued-fraction convergents of $\log_2 3$, LLL / lattice-reduction cycle equations, inductive invariant search) rather than naive brute force from $n = 1$.
