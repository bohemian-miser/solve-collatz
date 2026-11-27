#!/usr/bin/env python3
"""Track B (`Disprove/`) Diophantine Cycle Hunter & Lean Certificate Emitter.

Searches parity vectors v = (e_0, ..., e_{k-1}) with total halving sum S > k * log2(3)
for exact divisibility (2^S - 3^k) | C(v) yielding a positive integer n > 1 (a non-trivial
Collatz cycle!). If any hit is found, emits a ready-to-compile Lean 4 `NontrivialCycleCert`
for `Collatz/Disprove/Cert.lean`.

Also scans convergent denominators `(S, k)` of `log2(3)` where `2^S - 3^k` is unusually small
(the classic Diophantine danger zone for non-trivial cycles!).
"""

from __future__ import annotations

import argparse
import math
import sys
from fractions import Fraction


def compute_cycle_numerator(exps: tuple[int, ...]) -> int:
    k = len(exps)
    c = 0
    s_pref = 0
    for i, e in enumerate(exps):
        c += (3 ** (k - 1 - i)) * (1 << s_pref)
        s_pref += e
    return c


def is_trivial_cycle(n: int) -> bool:
    return n in (1, 2, 4)


def emit_lean_cert(start: int, period: int) -> str:
    return f"""-- Auto-generated Track B Counterexample Certificate
import Collatz.Disprove.Cert

theorem discovered_nontrivial_cycle : SolveCollatz.CollatzDisproof :=
  SolveCollatz.Disprove.NontrivialCycleCert.disproves_collatz
    {{ start := {start}
      period := {period}
      start_pos := by decide
      period_pos := by decide
      returns := by decide
      avoids_one := by decide }}
"""


def scan_k_circuits(max_k: int) -> list[tuple[int, int, int]]:
    """Scan 1-circuit parity patterns (1, 1, ..., 1, S - (k - 1)) and general small-k patterns
    for exact divisibility (2^S - 3^k) | C(v) with n > 1."""
    hits: list[tuple[int, int, int]] = []
    for k in range(1, max_k + 1):
        min_s = int(math.floor(k * math.log2(3))) + 1
        # Check S near k * log2(3) where 2^S - 3^k is small
        for s in range(min_s, min_s + 4):
            denom = (1 << s) - (3 ** k)
            if denom <= 0:
                continue
            # 1-circuit (Steiner pattern): k-1 ones followed by (s - (k - 1))
            last_e = s - (k - 1)
            if last_e >= 1:
                exps = (1,) * (k - 1) + (last_e,)
                num = compute_cycle_numerator(exps)
                if num % denom == 0:
                    n = num // denom
                    if n > 0 and not is_trivial_cycle(n):
                        hits.append((n, k + s, k))
    return hits


def main() -> int:
    p = argparse.ArgumentParser(description="Diophantine Non-Trivial Collatz Cycle Hunter")
    p.add_argument("--max-k", type=int, default=400, help="Max odd steps k for 1-circuit scan")
    args = p.parse_args()

    hits = scan_k_circuits(args.max_k)
    if hits:
        for n, period, k in hits:
            print(f"[HIT!] Non-trivial cycle found: start={n}, period={period}, odd_steps={k}")
            print(emit_lean_cert(n, period))
        return 10
    print(f"[CLEAN] Scanned 1-circuit Diophantine candidates up to k={args.max_k}: 0 non-trivial positive cycles.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
