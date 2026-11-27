#!/usr/bin/env python3
"""Track B (`Disprove/`) Diophantine Cycle Hunter & Rational/2-Adic Near-Cycle Analyzer.

Pure-stdlib, deterministic off-kernel search engine targeting exact cycle divisibility:
    (2^S - 3^k) | C(v)   yielding a positive integer n > 1 (non-trivial Collatz cycle).

Capabilities:
  1. Exact integer continued-fraction convergent & upper-semiconvergent generator for log_2(3)
     via exact `2^p` vs `3^q` comparisons (zero floating-point drift).
  2. Convergent-anchored 1-circuit Diophantine danger-zone scan up to high `k` (e.g. `100000`).
  3. Exhaustive 1-circuit, canonical 2-circuit, and canonical 3-circuit divisibility scanners
     within the rigorous non-trivial positive cycle band `3^k < 2^S <= (10/3)^k`.
  4. Rational / 2-adic near-cycle analyzer computing `x(v) = C(v) / (2^S - 3^k) in Z_(2)`
     and tracking closest fractional near-misses `||x(v)||`.
  5. End-to-end `--self-test` verifying generalized maps (`3n - 1` at 5, `5n + 1` at 13),
     CF convergents, 2-adic barrier points, and verbatim alignment with `Collatz/Disprove/Cert.lean`.
  6. Reproducible JSON sweep logging (`--log-json <path>`) with SHA-256 digests.
"""

from __future__ import annotations

import argparse
import dataclasses
import hashlib
import heapq
import json
import math
import pathlib
import re
import sys
import time
from fractions import Fraction
from typing import Any


@dataclasses.dataclass(frozen=True)
class CycleHit:
    family: str
    a: int
    b: int
    start: int
    period: int
    k: int
    s: int
    pattern: str


@dataclasses.dataclass(frozen=True)
class Convergent:
    index: int
    partial_quotient: int
    s: int
    k: int
    sign: int  # +1 if 2^s > 3^k (upper convergent), -1 if 2^s < 3^k (lower convergent)
    delta_bits: int
    delta_preview: str


@dataclasses.dataclass
class ScanSummary:
    family: str
    k_min: int
    k_max: int
    s_rule: str
    candidates_tested: int
    hits: list[CycleHit]
    near_misses: list[dict[str, Any]]


def compute_cycle_numerator(exps: tuple[int, ...], a: int = 3) -> int:
    """Compute C_a(v) = sum_{i=0}^{k-1} a^{k-1-i} * 2^{prefix_s_i}."""
    k = len(exps)
    c = 0
    s_pref = 0
    for i, e in enumerate(exps):
        c += (a ** (k - 1 - i)) * (1 << s_pref)
        s_pref += e
    return c


def is_trivial_cycle(n: int) -> bool:
    return n in (1, 2, 4)


def gen_step(a: int, b: int, n: int) -> int:
    return n // 2 if n % 2 == 0 else a * n + b


def verify_orbit_cycle(a: int, b: int, start: int, period: int) -> bool:
    """Directly simulate T_{a, b} for `period` steps and verify return to `start` avoiding `1`."""
    if start <= 0 or period <= 0:
        return False
    cur = start
    for _ in range(period):
        if cur == 1:
            return False
        cur = gen_step(a, b, cur)
    return cur == start


def rational_2adic_cycle(exps: tuple[int, ...], a: int = 3, b: int = 1) -> Fraction:
    """Return the unique periodic point x(v) = b * C_a(v) / (2^S - a^k) in Z_(2)."""
    k = len(exps)
    s = sum(exps)
    c = compute_cycle_numerator(exps, a=a)
    return Fraction(b * c, (1 << s) - (a ** k))


def analyze_2adic_near_cycle(exps: tuple[int, ...], a: int = 3, b: int = 1) -> dict[str, Any]:
    """Analyze the rational 2-adic periodic point for parity pattern `exps`."""
    k = len(exps)
    s = sum(exps)
    x = rational_2adic_cycle(exps, a=a, b=b)
    denom = x.denominator
    rem = abs(x.numerator) % denom
    dist_num = min(rem, denom - rem)
    return {
        "k": k,
        "s": s,
        "exps": list(exps),
        "x_fraction": str(x),
        "in_Z_2": (denom % 2 == 1),
        "is_integer": (denom == 1),
        "dist_to_int_fraction": f"{dist_num}/{denom}",
        "dist_to_int_approx": float(Fraction(dist_num, denom)),
    }


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


def validate_lean_cert_against_source(cert_text: str, cert_lean_path: pathlib.Path) -> list[str]:
    """Confirm emitted `NontrivialCycleCert` syntax matches `Collatz/Disprove/Cert.lean` verbatim
    and satisfies repository Lean source hygiene rules."""
    errors: list[str] = []
    if not cert_lean_path.exists():
        return [f"Missing Lean certificate definition: {cert_lean_path}"]

    src = cert_lean_path.read_text(encoding="utf-8")
    if "namespace SolveCollatz.Disprove" not in src:
        errors.append("Cert.lean missing `namespace SolveCollatz.Disprove`")

    m_struct = re.search(
        r"structure\s+NontrivialCycleCert\s+where\b(.*?)\n\s*\n",
        src,
        flags=re.DOTALL,
    )
    if not m_struct:
        errors.append("Cert.lean missing `structure NontrivialCycleCert where`")
        return errors

    expected_fields = re.findall(r"^\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*:", m_struct.group(1), flags=re.M)
    if not expected_fields:
        errors.append("Failed to parse NontrivialCycleCert fields from Cert.lean")
        return errors

    if "theorem NontrivialCycleCert.disproves_collatz (c : NontrivialCycleCert) : CollatzDisproof" not in src:
        errors.append("Cert.lean missing `NontrivialCycleCert.disproves_collatz` theorem signature")

    if "import Collatz.Disprove.Cert" not in cert_text:
        errors.append("Emitted cert missing `import Collatz.Disprove.Cert`")
    if "SolveCollatz.Disprove.NontrivialCycleCert.disproves_collatz" not in cert_text:
        errors.append("Emitted cert missing `SolveCollatz.Disprove.NontrivialCycleCert.disproves_collatz`")
    if ": SolveCollatz.CollatzDisproof :=" not in cert_text:
        errors.append("Emitted cert missing `: SolveCollatz.CollatzDisproof :=`")

    m_lit = re.search(r"\{(.*)\}", cert_text, flags=re.DOTALL)
    if not m_lit:
        errors.append("Emitted cert missing `{ ... }` NontrivialCycleCert literal")
        return errors

    emitted_fields = re.findall(r"\b([a-zA-Z_][a-zA-Z0-9_]*)\s*:=", m_lit.group(1))
    if emitted_fields != expected_fields:
        errors.append(
            f"Emitted struct fields {emitted_fields} != Cert.lean fields {expected_fields}"
        )

    for idx, line in enumerate(cert_text.splitlines(), 1):
        if len(line) > 100:
            errors.append(f"Emitted cert line {idx} exceeds 100 chars")
        for forbidden in ("sorry", "admit", "native_decide", "set_option", "erw"):
            if re.search(rf"\b{forbidden}\b", line):
                errors.append(f"Emitted cert line {idx} contains forbidden `{forbidden}`")
        if line.strip().startswith("--") and '"' in line:
            errors.append(f"Emitted cert line {idx} contains double quote in comment")

    return errors


def _format_int_preview(val: int, max_digits: int = 36) -> str:
    bits = abs(val).bit_length()
    if bits > 12000:
        sign = "-" if val < 0 else ""
        nbytes = (bits + 7) // 8 + 1
        digest = hashlib.sha256(abs(val).to_bytes(nbytes, "big")).hexdigest()[:12]
        return f"{sign}<{bits}-bit int, sha256:{digest}>"
    s = str(val)
    if len(s) <= max_digits:
        return s
    half = (max_digits - 5) // 2
    return f"{s[:half]}...{s[-half:]} ({len(s)} digits)"


def log2_3_convergents(max_k: int) -> tuple[list[Convergent], list[tuple[int, int, str]]]:
    """Generate exact continued-fraction convergents and upper semiconvergents for log_2(3)
    with denominator k <= max_k using exact integer `2^p` vs `3^q` arithmetic (no float drift)."""
    convergents: list[Convergent] = []
    upper_candidates: list[tuple[int, int, str]] = []
    seen_sk: set[tuple[int, int]] = set()

    p_prev2, q_prev2 = 0, 1
    p_prev1, q_prev1 = 1, 0
    n = 0

    while True:
        is_even = (n % 2 == 0)

        def _within_side(t: int) -> bool:
            p = t * p_prev1 + p_prev2
            q = t * q_prev1 + q_prev2
            lhs = 1 << p
            rhs = 3 ** q
            return lhs < rhs if is_even else lhs > rhs

        lo = 1 if n >= 1 else 0
        hi = lo
        while _within_side(hi):
            lo = hi
            hi = 1 if hi == 0 else hi * 2
        while lo + 1 < hi:
            mid = (lo + hi) // 2
            if _within_side(mid):
                lo = mid
            else:
                hi = mid

        a_n = lo
        p_n = a_n * p_prev1 + p_prev2
        q_n = a_n * q_prev1 + q_prev2
        if q_n > max_k:
            # Still collect any upper semiconvergents before q_n exceeds max_k
            if not is_even and q_prev1 > 0:
                max_t = (max_k - q_prev2) // q_prev1
                for t in range(1, min(a_n, max_t) + 1):
                    pt = t * p_prev1 + p_prev2
                    qt = t * q_prev1 + q_prev2
                    if 0 < qt <= max_k and (pt, qt) not in seen_sk:
                        seen_sk.add((pt, qt))
                        upper_candidates.append((pt, qt, f"semiconvergent_n{n}_t{t}"))
            break

        if not is_even:
            for t in range(1, a_n + 1):
                pt = t * p_prev1 + p_prev2
                qt = t * q_prev1 + q_prev2
                tag = f"convergent_n{n}" if t == a_n else f"semiconvergent_n{n}_t{t}"
                if (pt, qt) not in seen_sk:
                    seen_sk.add((pt, qt))
                    upper_candidates.append((pt, qt, tag))
        else:
            # Even convergent has 2^p_n < 3^q_n; p_n + 1 is minimal S with 2^S > 3^q_n.
            if (p_n + 1, q_n) not in seen_sk:
                seen_sk.add((p_n + 1, q_n))
                upper_candidates.append((p_n + 1, q_n, f"even_convergent_plus1_n{n}"))

        delta = (1 << p_n) - (3 ** q_n)
        sign = 1 if delta > 0 else -1
        abs_delta = abs(delta)
        convergents.append(
            Convergent(
                index=n,
                partial_quotient=a_n,
                s=p_n,
                k=q_n,
                sign=sign,
                delta_bits=abs_delta.bit_length(),
                delta_preview=_format_int_preview(delta),
            )
        )

        p_prev2, q_prev2 = p_prev1, q_prev1
        p_prev1, q_prev1 = p_n, q_n
        n += 1

    upper_candidates.sort(key=lambda item: (item[1], item[0]))
    return convergents, upper_candidates


def _push_near_miss(
    heap: list[tuple[float, tuple[int, ...], int, int, int, int]],
    limit: int,
    dist_approx: float,
    exps: tuple[int, ...],
    k: int,
    s: int,
    rem: int,
    denom: int,
) -> None:
    if rem == 0:
        return
    dist_num = min(rem, denom - rem)
    entry = (-dist_approx, exps, k, s, dist_num, denom)
    if len(heap) < limit:
        heapq.heappush(heap, entry)
    elif entry > heap[0]:
        heapq.heapreplace(heap, entry)


def _finalize_near_misses(
    heap: list[tuple[float, tuple[int, ...], int, int, int, int]],
) -> list[dict[str, Any]]:
    items = sorted(heap, key=lambda e: -e[0])
    out: list[dict[str, Any]] = []
    for neg_dist, exps, k, s, dist_num, denom in items:
        out.append(
            {
                "k": k,
                "s": s,
                "exps": list(exps),
                "dist_num": str(dist_num) if dist_num.bit_length() <= 128 else _format_int_preview(dist_num),
                "denom": str(denom) if denom.bit_length() <= 128 else _format_int_preview(denom),
                "dist_approx": -neg_dist,
            }
        )
    return out


def scan_1_circuits(max_k: int, s_band: int = 4, track_near_k: int = 200) -> ScanSummary:
    """Scan all 1-circuits (1,...,1, S-(k-1)) for 1 <= k <= max_k using exact integer bounds.
    Uses exact closed form C(v) = 3^k - 2^k and min_s = (3^k).bit_length()."""
    hits: list[CycleHit] = []
    near_heap: list[tuple[float, tuple[int, ...], int, int, int, int]] = []
    tested = 0
    pow3 = 1
    pow2 = 1

    for k in range(1, max_k + 1):
        pow3 *= 3
        pow2 <<= 1
        min_s = pow3.bit_length()
        c = pow3 - pow2
        for s in range(min_s, min_s + s_band):
            denom = (1 << s) - pow3
            tested += 1
            rem = c % denom
            if rem == 0:
                n = c // denom
                if n > 0 and not is_trivial_cycle(n):
                    exps = (1,) * (k - 1) + (s - k + 1,)
                    if verify_orbit_cycle(3, 1, n, k + s):
                        hits.append(CycleHit("1-circuit", 3, 1, n, k + s, k, s, f"1^{k-1},{s-k+1}"))
            elif k <= track_near_k and s == min_s and denom > 1:
                dist_num = min(rem, denom - rem)
                dist_approx = math.exp(math.log(dist_num) - math.log(denom)) if denom.bit_length() > 900 else dist_num / denom
                exps = (1,) * (k - 1) + (s - k + 1,)
                _push_near_miss(near_heap, 5, dist_approx, exps, k, s, rem, denom)

    return ScanSummary(
        family="1-circuit",
        k_min=1 if max_k >= 1 else 0,
        k_max=max_k,
        s_rule=f"min_s(k) <= S < min_s(k) + {s_band}",
        candidates_tested=tested,
        hits=hits,
        near_misses=_finalize_near_misses(near_heap),
    )


def scan_convergent_1_circuits(cf_max_k: int) -> tuple[list[Convergent], ScanSummary]:
    """Scan all exact continued-fraction upper convergents & upper semiconvergents of log_2(3)
    up to k <= cf_max_k for 1-circuit divisibility via (2^S - 3^k) | (2^{S-k} - 1)."""
    convergents, upper_candidates = log2_3_convergents(cf_max_k)
    hits: list[CycleHit] = []
    tested = 0

    for s, k, tag in upper_candidates:
        pow3 = 3 ** k
        denom = (1 << s) - pow3
        if denom <= 0:
            continue
        tested += 1
        # Equivalence: (3^k - 2^k) + (2^S - 3^k) = 2^k * (2^{S-k} - 1) with gcd(2^k, denom) = 1.
        if (pow(2, s - k, denom) - 1) % denom == 0:
            c = pow3 - (1 << k)
            n = c // denom
            if n > 0 and not is_trivial_cycle(n):
                if verify_orbit_cycle(3, 1, n, k + s):
                    hits.append(CycleHit(f"cf-{tag}", 3, 1, n, k + s, k, s, f"1^{k-1},{s-k+1}"))

    summary = ScanSummary(
        family="cf-convergent-1-circuit",
        k_min=upper_candidates[0][1] if upper_candidates else 0,
        k_max=cf_max_k,
        s_rule="exact CF upper convergents, semiconvergents, and even_p+1 of log_2(3)",
        candidates_tested=tested,
        hits=hits,
        near_misses=[],
    )
    return convergents, summary


def scan_2_circuits(max_k: int) -> ScanSummary:
    """Exhaustively scan all canonical 2-circuits ((1^{k1-1}, l1), (1^{k2-1}, l2)) for 2 <= k <= max_k
    across the full positive non-trivial band min_s(k) <= S <= floor(k * log_2(10/3))."""
    hits: list[CycleHit] = []
    near_heap: list[tuple[float, tuple[int, ...], int, int, int, int]] = []
    tested = 0
    if max_k < 2:
        return ScanSummary("2-circuit", 0, 0, "empty", 0, [], [])

    max_s_global = 2 * max_k + 2
    pow3 = [1] * (max_k + 1)
    pow10 = [1] * (max_k + 1)
    pow2 = [1] * (max_s_global + 1)
    for i in range(1, max_k + 1):
        pow3[i] = pow3[i - 1] * 3
        pow10[i] = pow10[i - 1] * 10
    for i in range(1, max_s_global + 1):
        pow2[i] = pow2[i - 1] << 1

    for k in range(2, max_k + 1):
        p3k = pow3[k]
        p10k = pow10[k]
        min_s = p3k.bit_length()
        s = min_s
        while s == min_s or p3k * pow2[s] <= p10k:
            denom = pow2[s] - p3k
            rem_l = s - k + 2  # l1 + l2 = rem_l, each >= 2
            if rem_l >= 4:
                for k1 in range(1, k // 2 + 1):
                    k2 = k - k1
                    base = pow3[k2] * (pow3[k1] - pow2[k1])
                    c2 = pow3[k2] - pow2[k2]
                    l1_max = rem_l - 2
                    if k1 == k2:
                        l1_max = min(l1_max, rem_l // 2)
                    for l1 in range(2, l1_max + 1):
                        l2 = rem_l - l1
                        c = base + pow2[k1 - 1 + l1] * c2
                        tested += 1
                        rem = c % denom
                        if rem == 0:
                            n = c // denom
                            if n > 0 and not is_trivial_cycle(n):
                                if verify_orbit_cycle(3, 1, n, k + s):
                                    hits.append(
                                        CycleHit(
                                            "2-circuit",
                                            3,
                                            1,
                                            n,
                                            k + s,
                                            k,
                                            s,
                                            f"(1^{k1-1},{l1};1^{k2-1},{l2})",
                                        )
                                    )
                        elif denom > 1:
                            dist_num = min(rem, denom - rem)
                            dist_approx = dist_num / denom
                            if len(near_heap) < 5 or -dist_approx > near_heap[0][0]:
                                exps = (1,) * (k1 - 1) + (l1,) + (1,) * (k2 - 1) + (l2,)
                                _push_near_miss(near_heap, 5, dist_approx, exps, k, s, rem, denom)
            s += 1

    return ScanSummary(
        family="2-circuit",
        k_min=2,
        k_max=max_k,
        s_rule="min_s(k) <= S <= floor(k * log_2(10/3)) via exact 3^k * 2^S <= 10^k",
        candidates_tested=tested,
        hits=hits,
        near_misses=_finalize_near_misses(near_heap),
    )


def scan_3_circuits(max_k: int) -> ScanSummary:
    """Exhaustively scan all canonical 3-circuits for 3 <= k <= max_k across the full positive
    non-trivial band min_s(k) <= S <= floor(k * log_2(10/3))."""
    hits: list[CycleHit] = []
    near_heap: list[tuple[float, tuple[int, ...], int, int, int, int]] = []
    tested = 0
    if max_k < 3:
        return ScanSummary("3-circuit", 0, 0, "empty", 0, [], [])

    max_s_global = 2 * max_k + 2
    pow3 = [1] * (max_k + 1)
    pow10 = [1] * (max_k + 1)
    pow2 = [1] * (max_s_global + 1)
    for i in range(1, max_k + 1):
        pow3[i] = pow3[i - 1] * 3
        pow10[i] = pow10[i - 1] * 10
    for i in range(1, max_s_global + 1):
        pow2[i] = pow2[i - 1] << 1

    for k in range(3, max_k + 1):
        p3k = pow3[k]
        p10k = pow10[k]
        min_s = p3k.bit_length()
        s = min_s
        while s == min_s or p3k * pow2[s] <= p10k:
            denom = pow2[s] - p3k
            rem_l = s - k + 3  # l1 + l2 + l3 = rem_l, each >= 2
            if rem_l >= 6:
                for k1 in range(1, k // 3 + 1):
                    c1 = pow3[k1] - pow2[k1]
                    for k2 in range(k1, k - 2 * k1 + 1):
                        k3 = k - k1 - k2
                        if k3 < k1:
                            continue
                        c2 = pow3[k2] - pow2[k2]
                        c3 = pow3[k3] - pow2[k3]
                        base1 = pow3[k2 + k3] * c1
                        for l1 in range(2, rem_l - 3):
                            s1 = k1 - 1 + l1
                            base2 = base1 + pow3[k3] * pow2[s1] * c2
                            for l2 in range(2, rem_l - l1 - 1):
                                l3 = rem_l - l1 - l2
                                b1, b2, b3 = (k1, l1), (k2, l2), (k3, l3)
                                rot0 = (b1, b2, b3)
                                if rot0 > (b2, b3, b1) or rot0 > (b3, b1, b2):
                                    continue
                                s12 = s1 + k2 - 1 + l2
                                c = base2 + pow2[s12] * c3
                                tested += 1
                                rem = c % denom
                                if rem == 0:
                                    n = c // denom
                                    if n > 0 and not is_trivial_cycle(n):
                                        if verify_orbit_cycle(3, 1, n, k + s):
                                            hits.append(
                                                CycleHit(
                                                    "3-circuit",
                                                    3,
                                                    1,
                                                    n,
                                                    k + s,
                                                    k,
                                                    s,
                                                    f"(1^{k1-1},{l1};1^{k2-1},{l2};1^{k3-1},{l3})",
                                                )
                                            )
                                elif denom > 1:
                                    dist_num = min(rem, denom - rem)
                                    dist_approx = dist_num / denom
                                    if len(near_heap) < 5 or -dist_approx > near_heap[0][0]:
                                        exps = (
                                            (1,) * (k1 - 1) + (l1,)
                                            + (1,) * (k2 - 1) + (l2,)
                                            + (1,) * (k3 - 1) + (l3,)
                                        )
                                        _push_near_miss(near_heap, 5, dist_approx, exps, k, s, rem, denom)
            s += 1

    return ScanSummary(
        family="3-circuit",
        k_min=3,
        k_max=max_k,
        s_rule="min_s(k) <= S <= floor(k * log_2(10/3)) via exact 3^k * 2^S <= 10^k",
        candidates_tested=tested,
        hits=hits,
        near_misses=_finalize_near_misses(near_heap),
    )


def scan_generalized_1_circuits(a: int, b: int, max_k: int) -> list[CycleHit]:
    """Scan 1-circuits on generalized map T_{a, b} (e.g. `3n - 1` or `5n + 1`) for positive cycles."""
    hits: list[CycleHit] = []
    if a <= 2 or (a - 2) % 2 == 0:
        return hits

    for k in range(1, max_k + 1):
        ak = a ** k
        c = (ak - (1 << k)) // (a - 2)
        if b > 0:
            s_start = ak.bit_length()
            s_range = range(s_start, s_start + 5)
        else:
            # For b < 0 (e.g. 3n - 1), positive cycle requires 2^S - a^k < 0.
            s_max = ak.bit_length() - 1
            s_range = range(k + 1, s_max + 1)

        for s in s_range:
            denom = (1 << s) - ak
            if denom == 0:
                continue
            num = b * c
            if num % denom == 0:
                n = num // denom
                if n > 1 and verify_orbit_cycle(a, b, n, k + s):
                    hits.append(
                        CycleHit(
                            f"gen-1-circuit({a}n{b:+d})",
                            a,
                            b,
                            n,
                            k + s,
                            k,
                            s,
                            f"1^{k-1},{s-k+1}",
                        )
                    )
    return hits


def run_self_test(repo_root: pathlib.Path) -> tuple[bool, dict[str, Any]]:
    """Verify the entire cycle-hunting & Lean certificate pipeline end-to-end."""
    checks: list[dict[str, Any]] = []
    all_ok = True

    # 1. Generalized 3n - 1 (start=5, period=5)
    hits_3m1 = scan_generalized_1_circuits(3, -1, max_k=10)
    found_5 = any(h.start == 5 and h.period == 5 for h in hits_3m1)
    checks.append({"name": "3n-1_cycle_5", "passed": found_5, "hits": [dataclasses.asdict(h) for h in hits_3m1]})
    all_ok = all_ok and found_5

    # 2. Generalized 5n + 1 (start=13, period=10)
    hits_5p1 = scan_generalized_1_circuits(5, 1, max_k=10)
    found_13 = any(h.start == 13 and h.period == 10 for h in hits_5p1)
    checks.append({"name": "5n+1_cycle_13", "passed": found_13, "hits": [dataclasses.asdict(h) for h in hits_5p1]})
    all_ok = all_ok and found_13

    # 3. Exact Lean NontrivialCycleCert syntax match against Collatz/Disprove/Cert.lean
    cert_path = repo_root / "Collatz" / "Disprove" / "Cert.lean"
    sample_cert = emit_lean_cert(start=5, period=5)
    schema_errs = validate_lean_cert_against_source(sample_cert, cert_path)
    schema_ok = len(schema_errs) == 0
    checks.append({"name": "lean_cert_verbatim_schema", "passed": schema_ok, "errors": schema_errs})
    all_ok = all_ok and schema_ok

    # 4. Exact CF convergents of log_2(3)
    expected_pairs = [
        (1, 1),
        (2, 1),
        (3, 2),
        (8, 5),
        (19, 12),
        (65, 41),
        (84, 53),
        (485, 306),
        (1054, 665),
        (24727, 15601),
    ]
    convs, _ = log2_3_convergents(16000)
    got_pairs = [(c.s, c.k) for c in convs[: len(expected_pairs)]]
    cf_ok = got_pairs == expected_pairs
    checks.append({"name": "cf_convergents_log2_3", "passed": cf_ok, "got_prefix": got_pairs})
    all_ok = all_ok and cf_ok

    # 5. Rational / 2-adic near-cycle analyzer (Barrier 4 witnesses)
    a1 = analyze_2adic_near_cycle((1, 2))
    a2 = analyze_2adic_near_cycle((1, 1, 2))
    a3 = analyze_2adic_near_cycle((1, 1, 1, 1, 4))
    z2_ok = (
        a1["x_fraction"] == "-5"
        and a2["x_fraction"] == "-19/11"
        and a2["in_Z_2"] is True
        and a3["x_fraction"] == "211/13"
        and a3["dist_to_int_fraction"] == "3/13"
    )
    checks.append({"name": "2adic_rational_analyzer", "passed": z2_ok, "samples": [a1, a2, a3]})
    all_ok = all_ok and z2_ok

    return all_ok, {"passed": all_ok, "checks": checks}


def _canonical_sha256(obj: Any) -> str:
    encoded = json.dumps(obj, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def main() -> int:
    p = argparse.ArgumentParser(
        description="Diophantine Non-Trivial Collatz Cycle Hunter & 2-Adic Near-Cycle Analyzer"
    )
    p.add_argument("--max-k", type=int, default=2000, help="Max odd steps k for 1-circuit scan")
    p.add_argument("--max-2circuit-k", type=int, default=40, help="Max odd steps k for exhaustive 2-circuit scan")
    p.add_argument("--max-3circuit-k", type=int, default=20, help="Max odd steps k for exhaustive 3-circuit scan")
    p.add_argument("--cf-max-k", type=int, default=100000, help="Max denominator k for log_2(3) CF convergents")
    p.add_argument("--s-band", type=int, default=4, help="Band [min_s, min_s + s_band) for 1-circuit scan")
    p.add_argument("--self-test", action="store_true", help="Run end-to-end generalized map & Lean cert self-test")
    p.add_argument("--log-json", type=str, help="Write deterministic JSON sweep log to path")
    args = p.parse_args()

    t0 = time.perf_counter()
    repo_root = pathlib.Path(__file__).resolve().parent.parent

    self_test_report: dict[str, Any] | None = None
    if args.self_test:
        st_ok, self_test_report = run_self_test(repo_root)
        for chk in self_test_report["checks"]:
            status = "OK" if chk["passed"] else "FAIL"
            print(f"[{status}] self-test: {chk['name']}")
            if not chk["passed"] and "errors" in chk:
                for err in chk["errors"]:
                    print(f"       error: {err}", file=sys.stderr)
        if not st_ok:
            print("[FAIL] Self-test failed!", file=sys.stderr)
            return 1

    k2_limit = min(args.max_2circuit_k, args.max_k) if args.max_k > 0 else 0
    k3_limit = min(args.max_3circuit_k, args.max_k) if args.max_k > 0 else 0

    convergents, cf_summary = scan_convergent_1_circuits(args.cf_max_k)
    s1_summary = scan_1_circuits(args.max_k, s_band=args.s_band)
    s2_summary = scan_2_circuits(k2_limit)
    s3_summary = scan_3_circuits(k3_limit)

    summaries = [cf_summary, s1_summary, s2_summary, s3_summary]
    all_hits = [h for sm in summaries for h in sm.hits]
    elapsed = time.perf_counter() - t0

    deterministic_core: dict[str, Any] = {
        "schema": "solve-collatz-cycle-hunter/v1",
        "parameters": {
            "max_k": args.max_k,
            "max_2circuit_k": k2_limit,
            "max_3circuit_k": k3_limit,
            "cf_max_k": args.cf_max_k,
            "s_band": args.s_band,
            "self_test": bool(args.self_test),
        },
        "convergents_log2_3": [dataclasses.asdict(c) for c in convergents],
        "scanned_families": [
            {
                "family": sm.family,
                "k_min": sm.k_min,
                "k_max": sm.k_max,
                "s_rule": sm.s_rule,
                "candidates_tested": sm.candidates_tested,
                "hits_found": len(sm.hits),
                "near_misses": sm.near_misses,
            }
            for sm in summaries
        ],
        "hits": [dataclasses.asdict(h) for h in all_hits],
    }
    if self_test_report is not None:
        deterministic_core["self_test"] = self_test_report

    det_sha256 = _canonical_sha256(deterministic_core)
    log_payload: dict[str, Any] = {
        **deterministic_core,
        "deterministic_sha256": det_sha256,
        "runtime_seconds": round(elapsed, 6),
    }
    log_payload["payload_sha256"] = _canonical_sha256(log_payload)

    if args.log_json:
        out_path = pathlib.Path(args.log_json)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json.dumps(log_payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    if all_hits:
        for h in all_hits:
            print(
                f"[HIT!] {h.family}: start={h.start}, period={h.period}, "
                f"odd_steps={h.k}, S={h.s}, pattern={h.pattern}"
            )
            print(emit_lean_cert(h.start, h.period))
        return 10

    total_tested = sum(sm.candidates_tested for sm in summaries)
    print(
        f"[CLEAN] Tested {total_tested} candidates in {elapsed:.3f}s "
        f"(1-circuit k<={args.max_k}, 2-circuit k<={k2_limit}, 3-circuit k<={k3_limit}, "
        f"CF log2(3) k<={args.cf_max_k} [{len(convergents)} convergents]): "
        f"0 non-trivial positive cycles. sha256={det_sha256[:16]}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
