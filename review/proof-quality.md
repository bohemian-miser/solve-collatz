# Rubric 4: Proof Quality, Decomposition & Maintainability

## Mission
Keep the codebase readable by humans and easy for future swarms to build on.

## Mandatory Checks

1. **Proof Length & Decomposition (`[S1]`)**
   - `scripts/check_source_guards.py` enforces a hard cap (default **50 lines** per declaration, **100 chars** per line, **1000 lines** per new file).
   - Even under 50 lines, flag proofs that glue unrelated steps together instead of extracting named mathematical lemmas.
2. **Conceptual Clarity Over Tactic Golf (`[S1]`)**
   - Reject unreadable compressed tactic one-liners that obscure mathematical structure.
   - Prefer structured proofs (`calc`, `have`, clean `simp only`, explicit intermediate claims) where a mathematician can read the argument from the skeleton.
3. **No Brittle Tactic Debt (`[S1]`/`[S2]`)**
   - Avoid `erw`, non-terminal `simp`, `unfold` cascades, or fragile `omega`/`decide` calls that spike heartbeats.
4. **API Design & Documentation (`[S2]`)**
   - Every `public` `def`, `structure`, and `theorem` has a concise docstring explaining *what* it states and *why* it matters for the frontier.
   - Every file has a top-of-file module docstring summarizing its role in the DAG (`Core`, `Known`, `Prove`, or `Disprove`).
5. **Search / Tooling Hygiene (`[S1]`/`[S2]`)**
   - Any script in `search/` or `scripts/` must be deterministic (seeded if randomized), fast in CI smoke-test mode, and emit machine-checkable Lean certificates when claiming any Track B candidate.
   - Compiled native Track B search tools (C/C++/Rust/CUDA) MUST use `scripts/native_cache.py` (content-hashed `/tmp` binaries via `cached_binary_path` + `atomic_compile`, zero committed binaries), emit strict RFC-8259 JSON (`allow_nan=False`), pass an `ASan+UBSan` check, and verify multi-thread `t=1 == t=N` bit-for-bit `deterministic_sha256` JSON field equivalence (computed via `canonical_sha256`).
6. **Root Barrel Import Ordering (`[S2]`)**
   - Keep `public import` entries in the root library file (`<LeanRoot>.lean`) alphabetically sorted to minimize parallel-PR merge conflicts.

## Output Format
List `[S0]`/`[S1]`/`[S2]` findings with `file:line`, plus concrete refactoring suggestions and verdict `PASS` or `REQUEST CHANGES`.
