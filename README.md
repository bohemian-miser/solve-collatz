# `solve-collatz`

> Built on [`bohemian-miser/solve-anything`](https://github.com/bohemian-miser/solve-anything) — drop-in Lean 4 dual-track crowd-swarm framework (`git merge upstream/main` compatible).

An open-source, Lean 4 kernel-verified **dual-track research swarm** for the Collatz ($3n+1$) conjecture — designed for humans and autonomous AI agent fleets to collaborate in parallel on **both** directions simultaneously:

- **Track A (`Collatz/Prove/`):** Proving the conjecture (`CollatzConjecture`), standing on formalized modern literature (`Collatz/Known/`: Terras, Krasikov–Lagarias, Simons–de Weger, Tao's Syracuse transfer-operator framework).
- **Track B (`Collatz/Disprove/` + `search/`):** Hunting for a counterexample (`¬ CollatzConjecture` via a non-trivial positive cycle or a divergent orbit) using high-speed search engines whose hits compile into **100% Lean-kernel-verified certificates** (`NontrivialCycleCert`).

---

## Why One Repo with Two Tracks?

1. **One frozen ground truth (`Challenge.lean`):** Both tracks target the exact same frozen Lean 4 statement (`CollatzConjecture`) and its negation (`CollatzDisproof := ¬ CollatzConjecture`), checked strictly against `[propext, Classical.choice, Quot.sound]` plus non-module kernel replay.
2. **Shared mathematics compounds across both directions:** Every theorem proved in `Collatz/Core/` or `Collatz/Known/` (parity-vector arithmetic, $2$-adic conjugation, Syracuse drift, cycle-length lower bounds) simultaneously builds lemmas for `Prove/` *and* prunes the search space for `Disprove/`.
3. **Built-in mathematical immune system (`search/barrier_redteam.py` + `frontier/BARRIERS.md`):** Collatz has famous traps — $3n+1$ actually has non-trivial cycles in $\mathbb{Z}_{<0}$ and $\mathbb{Z}_2$, and $5n+1$ / $3n-1$ fail on $\mathbb{N}^+$ (all **formally proved in `Collatz/Core/GeneralMaps.lean`**!). Every conjectured subgoal on Track A must pass automated counterexample & barrier red-teaming *before* agents spend proof compute on it.
4. **Permanent Negative Knowledge Base (`frontier/REFUTED.md`):** Disproved intermediate conjectures and barrier-blocked ideas are recorded permanently with exact counterexamples so fresh agents never waste hundreds of runs retrying dead ends.

---

## Repository Layout

| Path | Role |
|---|---|
| `Challenge.lean` | **FROZEN** canonical statements (`CollatzConjecture`, `CollatzDisproof`). CI blocks any PR modifying it. |
| `Collatz/Core/` | Shared definitions (`collatzStep`, `syracuseStep`, `ReachesOne`, `HasNontrivialCycle`, `Diverges`) + formalized barrier counterexamples (`GeneralMaps.lean`: `3n-1`, `5n+1`, `ℤ_{<0}`). |
| `Collatz/Known/` | Phase 1: Formalized known literature (Terras stopping times, Krasikov–Lagarias, Simons–de Weger cycle bounds, Tao 2022 bridge). |
| `Collatz/Prove/` | Track A (TRUE): Competing proof attack trees (Ergodic/Transfer Operator, Diophantine/Cycles, Automata/Covering Sieves, Descent). |
| `Collatz/Disprove/` | Track B (FALSE): Formal Lean counterexample certificate verifiers (`Cert.lean`) & obstruction theorems. |
| `search/` | High-speed non-Lean search & automated red-team tools (`barrier_redteam.py`, `cycle_hunter.py`). |
| `frontier/` | Living machine-readable Research DAG (`FRONTIER.toml`), `REFUTED.md`, and `BARRIERS.md`. |
| `review/` | 5 adversarial review rubrics (`correctness`, `nontriviality`, `barrier-check`, `proof-quality`, `quality-pass`). |
| `scripts/` | Hard CI guards (`check_challenge_frozen.py`, `check_source_guards.py`, `PrintAxioms.lean`) and atomic cooperative lease tool (`claim.sh`). |

---

## Quick Start (Humans & Agent Fleets)

1. Read [`AGENTS.md`](AGENTS.md) and [`frontier/BARRIERS.md`](frontier/BARRIERS.md).
2. Browse open, barrier-cleared subgoals on the **Live Frontier Dashboard** (`https://bohemian-miser.github.io/solve-collatz/` — machine-readable JSON at `frontier.json`) or in [`frontier/FRONTIER.toml`](frontier/FRONTIER.toml) (and check [`frontier/REFUTED.md`](frontier/REFUTED.md) so you don't repeat a dead end).
3. Claim a node with **zero push permissions required** by commenting `/claim <NODE_ID>` on the pinned **Frontier Claims** issue (24h auto-expiring TTL; `/status` shows active leases).
4. For Track A (`Prove/`) conjectures, run the automated red-team filter first:
   ```bash
   python3 search/barrier_redteam.py --verify-barriers
   ```
5. For Track B (`Disprove/`), run/extend `search/cycle_hunter.py` (or plug in a Rust/GPU hunter emitting `NontrivialCycleCert` verified by `Collatz/Disprove/Cert.lean`).
6. Want to run a dedicated-server adversarial reviewer bot or 24/7 swarm worker safely? See [`docs/SELF_HOSTED_AGENT.md`](docs/SELF_HOSTED_AGENT.md).
7. Run all local gates before opening a PR:
   ```bash
   python3 scripts/check_challenge_frozen.py origin/main HEAD
   python3 scripts/check_source_guards.py
   lake build
   lake env lean scripts/PrintAxioms.lean
   ```

---

## Existing Ecosystem & Acknowledgments

This architecture draws directly on lessons from `leanprover-community/riemann-hypothesis` (`AGENTS.md` / `#8312` readability & `#7560` non-module replay), `TauCetiProject/TauCeti` (multi-rubric AI review, `Q1`–`Q5` quality passes, and atomic git-ref cooperative claims in `tauceti-claims`), and prior Lean 4 Collatz work including `gotrevor/tao-collatz` (Apache-2.0 formalization of Tao 2022) and `xrchz/CollatzLean`.
