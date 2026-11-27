#!/usr/bin/env python3
"""Automated Counterexample & Barrier Red-Team Harness for Track A (`Prove/`) conjectures.

Tests a candidate Python predicate `pred(n, a, b)` (or orbit-level predicate) against:
  1. Standard `3n + 1` on `N+` (1..limit + extreme glide/record-height seeds like 27, 2^k - 1).
  2. Barrier 1: `3n - 1` on `N+` (includes known cycle 5, 17).
  3. Barrier 2: `5n + 1` on `N+` (includes known cycle 13, 17).
  4. Barrier 3: `3n + 1` on `Z_<0` (includes known cycles -1, -5, -17).
  5. Barrier 4: `2`-adic periodic rational witnesses `x = C(v) / (2^S - 3^k)`.

Usage:
  python3 search/barrier_redteam.py --verify-barriers
  python3 search/barrier_redteam.py --check-stopping-bound "lambda n, k: k <= 20 * n.bit_length()"
"""

from __future__ import annotations

import argparse
import sys
from fractions import Fraction


def gen_step(a: int, b: int, n: int) -> int:
    return n // 2 if n % 2 == 0 else a * n + b


def find_cycle_or_steps(a: int, b: int, start: int, max_steps: int = 5000) -> tuple[str, int, int]:
    """Return (status, steps_or_period, peak_abs). status in {'hits_one', 'cycle', 'timeout'}."""
    seen: dict[int, int] = {}
    cur = start
    peak = abs(cur)
    for step in range(max_steps):
        if cur == 1 and start > 0 and a == 3 and b == 1:
            return ("hits_one", step, peak)
        if cur in seen:
            return ("cycle", step - seen[cur], peak)
        seen[cur] = step
        cur = gen_step(a, b, cur)
        if abs(cur) > peak:
            peak = abs(cur)
    return ("timeout", max_steps, peak)


def rational_2adic_cycle(parity_exps: list[int]) -> Fraction:
    """For odd-step halving exponents e_0..e_{k-1}, return the unique rational periodic point
    x = C(v) / (2^S - 3^k) in Z_(2) (hence Z_2) whose Syracuse parity pattern is `parity_exps`."""
    k = len(parity_exps)
    S = sum(parity_exps)
    C = 0
    prefix_s = 0
    for i, e in enumerate(parity_exps):
        C += (3 ** (k - 1 - i)) * (2 ** prefix_s)
        prefix_s += e
    return Fraction(C, (2 ** S) - (3 ** k))


def verify_builtin_barriers() -> bool:
    """Sanity-check all four arithmetic barriers mirrored in Collatz/Core/GeneralMaps.lean."""
    checks = [
        ("Barrier 1 (3n-1 cycle at 5)", 3, -1, 5, 5),
        ("Barrier 2 (5n+1 cycle at 13)", 5, 1, 13, 10),
        ("Barrier 3 (3n+1 neg cycle at -5)", 3, 1, -5, 5),
        ("Barrier 3b (3n+1 neg cycle at -17)", 3, 1, -17, 18),
    ]
    ok = True
    for label, a, b, start, expected_period in checks:
        st, per, _ = find_cycle_or_steps(a, b, start)
        passed = st == "cycle" and per == expected_period
        print(f"[{'OK' if passed else 'FAIL'}] {label}: status={st} period={per}")
        ok = ok and passed

    # Barrier 4: 2-adic rational cycle (parity pattern [1, 2] -> x = (3 + 2)/(8 - 9) = -5;
    # parity pattern [1, 1, 2] -> x = (9 + 6 + 4)/(16 - 27) = -19/11 in Z_2!)
    x = rational_2adic_cycle([1, 1, 2])
    passed_2adic = (x == Fraction(-19, 11)) and (x.denominator % 2 == 1)
    print(f"[{'OK' if passed_2adic else 'FAIL'}] Barrier 4 (Z_2 rational periodic point [1,1,2]): x = {x}")
    return ok and passed_2adic


def check_stopping_bound(expr: str, limit: int) -> int:
    """Test a proposed stopping-time bound `f(n, steps) -> bool` on standard 3n+1 up to `limit`
    plus adversarial seeds `2^k - 1`."""
    fn = eval(expr, {"__builtins__": {"abs": abs, "min": min, "max": max, "pow": pow}})
    seeds = list(range(2, limit + 1)) + [(1 << k) - 1 for k in range(5, 45)]
    for n in seeds:
        st, steps, peak = find_cycle_or_steps(3, 1, n, max_steps=10000)
        if st != "hits_one":
            print(f"[ALERT] Non-terminating seed within 10000 steps: n={n} status={st} peak={peak}")
            return 2
        if not fn(n, steps):
            print(f"[REFUTED] Stopping bound failed at n={n} (steps={steps}, peak={peak})")
            return 1
    print(f"[SURVIVED] Tested {len(seeds)} seeds (up to {limit} + 2^k-1 stress seeds); 0 refutations.")
    return 0


def main() -> int:
    p = argparse.ArgumentParser(description="Collatz Counterexample & Barrier Red-Team Harness")
    p.add_argument("--verify-barriers", action="store_true", help="Verify built-in barrier witnesses")
    p.add_argument("--check-stopping-bound", type=str, help="Python lambda n, k: ... to red-team")
    p.add_argument("--limit", type=int, default=50000, help="Upper seed limit for stress testing")
    args = p.parse_args()

    if args.verify_barriers:
        return 0 if verify_builtin_barriers() else 1
    if args.check_stopping_bound:
        return check_stopping_bound(args.check_stopping_bound, args.limit)
    p.print_help()
    return 0


if __name__ == "__main__":
    sys.exit(main())
