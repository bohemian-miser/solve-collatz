# Research map

What is known about the Collatz conjecture, what this repo has formalized, and where work can go next.
Read this before claiming a node in `frontier/FRONTIER.toml`.

Figures marked † were taken from memory during the first survey (2026-11-28) and still need checking
against the original paper. Fixing one is a good first PR: replace the † with a page or theorem number.

## 1. The shape of the problem

Every Lean result about cycles, here and in the literature, needs the same two inputs:

- **A verified range `B`:** every `n < B` reaches 1. A smallest cycle element must then be at least `B`.
- **A Diophantine bound:** a lower bound on `2^S - 3^k` when `2^S > 3^k`. Steiner, Simons and Simons–de
  Weger get this from Baker's theory of linear forms in logarithms. In this repo it appears as the
  hypothesis `hBaker`.

Continued fractions of `log2 3` turn these two inputs into cycle theorems, and the repo already has
that step (`eliahou_cf_elimination`, `mCircuit_cf_elimination_bernoulli`, the `hBaker` reductions).
What it lacks is either input at full strength:

| Input | Literature | This repo (kernel-checked) |
|---|---|---|
| Verified range | `2^71` (Barina 2025) | `2^22` (`small_lt_4194304_finiteStoppingTime`, by `decide`) |
| Diophantine bound | Baker / Rhin-type bounds, explicit constants† | hypothesis `hBaker`, not proved |

Density results (Terras, Korec, Tao) are a separate line. They show the set of exceptions is thin but
cannot rule out a single cycle or divergent orbit, which would form a density-zero set. Every proof also
has to use something specific to 3, because `5n+1` has non-trivial cycles and Conway showed that
generalized Collatz maps are undecidable.

## 2. Literature

| Result | Statement | Reference | Formalized here? | Effort to formalize |
|---|---|---|---|---|
| Terras, Everett | Density 1 of n with finite stopping time | Acta Arith. 30 (1976); Adv. Math. 25 (1977) | Yes (`terras_hasNaturalDensityOne`) | done |
| Korec | Almost all n drop below `n^c` for every `c > log_4 3` | Math. Slovaca 44 (1994)† | Yes, with a power-saving rate (`korec_general_power_saving`) | done |
| Krasikov–Lagarias | `#{n ≤ x : n reaches 1} ≥ x^0.84` | Acta Arith. 109 (2003)† | No (the README claims it; the Lean tree doesn't have it) | months; LP certificate |
| Tao | Almost all orbits (log density) get below any `f(n) → ∞` | Forum Math. Pi 10 (2022) | Statement only; the bridge assumes it | not realistic yet |
| Steiner | No non-trivial 1-cycle | Manitoba Conf. 1977† | For `k ≤ 10,781,273`; full result assumes `hBaker` | months with a Diophantine bound |
| Simons | No 2-cycle | Proc. AMS 133 (2005)† | Lower bound only (`k₁+k₂ > 64,497,106`); full result assumes `hBaker` | as above |
| Simons–de Weger | No m-cycle for `m ≤ 68` (later 75) | Acta Arith. 117 (2005)† | Lower bounds on length only | as above, plus LLL |
| Hercher | No m-cycle for `m ≤ 91` | J. Integer Seq. 26 (2023) 23.3.5, arXiv:2201.00406 | No | as above, plus `2^68` |
| Eliahou | With range `2^40`, cycle length ≥ 17,087,915 | Discrete Math. 118 (1993)† | Same method with range `2^22`: length ≥ 19,700 | elementary; limited by the range |
| Barina | Every `n < 2^71` reaches 1 | J. Supercomputing 81 (2025) | `n < 2^22` | `2^71` is not realistic in the kernel |
| Angeltveit | Faster verification algorithm (2^N to 2^(N+1) in under 2× the time) | arXiv:2602.10466 (2026) | No | algorithmic |
| Lagarias, Bernstein | Map on `ℤ_2` is conjugate to the shift; explicit inverse | Monthly 92 (1985); Proc. AMS 121 (1994)† | Rational periodic points only (`universal_twoAdic_periodicPoint`) | weeks to months; needs Mathlib `ℤ_[2]` |
| Monks | Collatz holds iff it holds on any arithmetic progression | Proc. AMS 134 (2006)† | No | weeks |
| Conway, Kurtz–Simon | Generalized Collatz maps are undecidable; the "for all n" version is Π⁰₂-complete | 1972†; TAMC 2007† | No (the "conway" barrier theorems don't mention it) | months |
| Yolcu–Aaronson–Heule | Collatz as termination of a string rewriting system; weakened variants proved by SAT | CADE-28 (2021)† | No | encoding weeks; certificates checkable |

Claimed proofs and disproofs since 2023, none valid:
- The July 2026 Lean "disproof" (xrchz/CollatzLean) exploited a Lean kernel bug (#14576), fixed in
  4.32.2.
- Several Zenodo, arXiv and fee-charging-journal "proofs" put the real content in axioms or are
  unreviewed.

Track B certificates should carry an explicit witness checked by evaluation, and should also pass an
independent checker (lean4lean or nanoda), not just the axiom audit.

## 3. Existing formalizations elsewhere

Nothing substantial: no proof assistant has Terras, Tao, Steiner, Simons–de Weger, Conway, or a checked
verification run. A few pieces are worth reusing:

| Source | What | Use |
|---|---|---|
| google-deepmind/formal-conjectures | Canonical Lean statement (no proof) | Prove ours equivalent so results line up with the benchmark |
| besimelagh/collatz-lean (MIT, Lean 4.36, no Mathlib) | Residue-class descent; `iterT j (2^j b - 1) = 3^j b - 1` | Port directly |
| shuanat/collatz-lean4 (MIT, Mathlib) | `ord_{2^t}(3) = 2^(t-2)`, mod-3 layer lemmas | Mine for statements |
| Coq Library of Undecidability Proofs (MPL-2.0) | FRACTRAN halting undecidable | Template for a Conway node |

## 4. What this repo has proved

From the 2026-11-28 audit. `Challenge.lean` states the conjecture correctly, and both disproof bridges
are sound.

Results that hold as claimed:
- the Syracuse affine and cycle equations;
- the reduction of a cycle to its minimal odd element;
- the Terras parity-vector bijection and density 1;
- Korec with a power-saving rate;
- sound residue-class descent certificates (`dropsWithin_sound`);
- a kernel-checked range of `2^22`, giving cycle length ≥ 19,700;
- the continued-fraction elimination machinery.

Weaker than their node titles:

| Node | Title says | Lean proves |
|---|---|---|
| KNOWN-002 | Steiner's theorem | The 1-cycle case for `k ≤ 10,781,273`; the full theorem assumes `hBaker` |
| KNOWN-003 | Eliahou / Simons–de Weger | Eliahou's method with range `2^22`; Simons–de Weger is not there |
| KNOWN-004 | Bridge to Tao | Tao's statement, derived from a hypothesis that restates it for Syracuse orbits |
| PROVE-B1 | m-cycle non-existence | Lower bounds on cycle length; non-existence assumes `hBaker` |
| DISPROVE-002/003 | Search frontier | Searches far below published ranges (`n ≤ 10^10` vs `2^71`; small m vs Hercher's 91) |

Also:
- The 48 `barrier*` theorems combine cycles of other maps with numeric facts. They don't show any
  argument fails on a barrier, so they shouldn't count as results.
- The "Chernoff tightness" theorem bounds this particular method, not the exceptional set.
- `NontrivialCycleCert.returns` iterates one step at a time, too slowly for a real cycle (at least
  19,700 steps).

## 5. Directions

Each direction lists its first claimable nodes, each sized as one PR.

### D1. Scale the verified range (feeds every cycle theorem)

Replace `decide` over all residues with a certificate. A sieve modulo `2^k` (most classes are covered by
`dropsWithin_sound`), plus a list of surviving residues. Each survivor gets a short descent witness,
checked by kernel `Nat` arithmetic, which uses GMP. Nothing trusts the compiler.

- D1.1 Certificate format and checker; reproduce `2^22` from a certificate, and measure kernel time per
  witness.
- D1.2 `2^28`, then `2^32`. Each range feeds straight into `syracuseCycle_min_ge_of_stopping` and the
  Eliahou bound.
- D1.3 Generic theorem: range `B` implies cycle-length bound `L(B)`, with `L` computed from the
  convergents. With `B = 2^40` this would be the first machine-checked Eliahou bound (17,087,915).
- D1.4 Test whether Angeltveit's algorithm gives smaller certificates.

### D2. Prove the Diophantine bound (makes Steiner and Simons unconditional)

Discharging `hBaker` turns the existing reductions into the first formal proofs of Steiner (no
1-cycles) and Simons (no 2-cycles). The full Baker theory is too large. Effective irrationality measures
for `log 3 / log 2` (Rhin; later Wu–Wang)† use Padé approximants and integral estimates. That is hard,
but standard analysis, and would need Mathlib.

- D2.1 Find the weakest bound of the `hBaker` shape that closes Steiner given the current range, and
  state it as a single named hypothesis.
- D2.2 Survey which published irrationality measure is easiest to formalize, and get its exact
  statement and proof outline from the paper.
- D2.3 Formalize it (multi-month; Mathlib).

### D3. Structure and reformulations (shared library, cheap to start)

- D3.1 Prove `Challenge.lean` equivalent to the formal-conjectures statement.
- D3.2 Port the besimelagh lemmas.
- D3.3 Monks: the conjecture holds iff it holds on any fixed arithmetic progression.
- D3.4 Lagarias conjugacy and Bernstein's inverse on Mathlib `ℤ_[2]`.
- D3.5 The Yolcu–Aaronson–Heule rewriting-system equivalence, then their SAT-found certificates for the
  weakened systems.

### D4. Density line

Terras and Korec are done.
- D4.1 Krasikov–Lagarias `x^0.84`: an LP certificate, large but checkable; first a lower exponent such
  as Krasikov's `3/7`†.
- D4.2 Long term: pieces of Tao's argument, such as the 3-adic equidistribution of Syracuse variables.

### D5. Track B, recast

No counterexample is in reach: none below `2^71`, no m-cycle with `m ≤ 91`. Work here is about
constraints any counterexample must satisfy, which feed D1 and D2.
- D5.1 A fast `returns` checker in `Cert.lean`, by repeated squaring of the parity-vector affine map.
- D5.2 Independent-checker CI job: lean4lean or nanoda over the Disprove tree.
- D5.3 Rerun Hercher's computation with `2^71` to see whether `m ≤ 92+` follows. This is computation, not
  Lean, but possibly a small new result.

### Cleanup to do first

- Correct the node titles in section 4.
- Remove or relabel the `barrier*` theorems.
- Drop the Krasikov–Lagarias and transfer-operator claims from the README.
- Add the † checks as `good-first-issue` nodes.
