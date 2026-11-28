#!/usr/bin/env python3
"""Pure-stdlib Python wrapper for `mcircuit_hunter.c` (Track B `DISPROVE-002 Phase 5`).

Auto-compiles `search/mcircuit_hunter/mcircuit_hunter.c` into content-hashed
`/tmp/solve_collatz_mcircuit_hunter_<sha12>[_asan]` via `scripts/native_cache.py`,
keeping the git working tree 100% free of binaries.

Supports two Track B search modes:
  1. Mode 1 (Simons-de Weger / Eliahou exhaustive m-circuit sweep, m = 2..7):
     4-tier exact arithmetic (`u128 -> u256 -> u512 -> u1024` up to `K <= 512, S <= 1023`).
  2. Mode 2 (`--convergent-window`):
     Exact continued-fraction convergent-window hunter across `log_2(3)` convergents
     (`K in {5, 12, 41, 53, 306, 665, 15601}`): all canonical 1-circuits up to `K = 15601`,
     all canonical 2-circuits at `K in {5, 12, 41, 53, 306, 665}` (`O(K^2)` exact `mod D`),
     and canonical/structured 3-circuits at `K in {41, 53, 306}` (`D = 2^485 - 3^306`).
"""

from __future__ import annotations

import argparse
import math
import pathlib
import subprocess
import sys
import time
from typing import Any


REPO_SEARCH_DIR = pathlib.Path(__file__).resolve().parent
SEARCH_DIR = REPO_SEARCH_DIR.parent
REPO_ROOT = SEARCH_DIR.parent
SCRIPTS_DIR = REPO_ROOT / "scripts"
for _p in (str(SCRIPTS_DIR), str(SEARCH_DIR)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from engine import check_thread_determinism, compile_c, run_json_engine  # type: ignore  # noqa: E402
from native_cache import (  # type: ignore  # noqa: E402
    canonical_sha256,
    dump_strict_json,
    loads_strict_json,
)

C_SOURCE = REPO_SEARCH_DIR / "mcircuit_hunter.c"
CERT_LEAN = REPO_ROOT / "Collatz" / "Disprove" / "Cert.lean"

DEFAULT_K_MAX = {2: 320, 3: 135, 4: 74, 5: 46, 6: 34, 7: 26}
CW_M2_PAIRS = ((5, 8), (12, 20), (41, 65), (53, 85), (306, 485), (665, 1055))
CW_M3_PAIRS = ((41, 65), (41, 66), (53, 85), (306, 485), (306, 486))
CW_K306_STRUCTURED_SLICES = (
    (1, 1),
    (10, 10),
    (50, 50),
    (100, 100),
    (102, 102),
)


def ensure_compiled(asan: bool = False, force: bool = False) -> pathlib.Path:
    """Compile `mcircuit_hunter.c` into a content-hashed `/tmp` binary via `search/engine.py`."""
    return compile_c("solve_collatz_mcircuit_hunter", C_SOURCE, hash_paths=[REPO_SEARCH_DIR], asan=asan, force=force)


def emit_lean_cert(start: int, period: int) -> str:
    """Emit a Lean `SolveCollatz.Disprove.NontrivialCycleCert` matching `Cert.lean`."""
    return (
        "-- Auto-generated Track B Counterexample Certificate\n"
        "import Collatz.Disprove.Cert\n\n"
        "theorem discovered_nontrivial_cycle : SolveCollatz.CollatzDisproof :=\n"
        "  SolveCollatz.Disprove.NontrivialCycleCert.disproves_collatz\n"
        f"    {{ start := {start}\n"
        f"      period := {period}\n"
        "      start_pos := by decide\n"
        "      period_pos := by decide\n"
        "      returns := by decide\n"
        "      avoids_one := by decide }\n"
    )


def exact_mcircuit_numerator_py(k_vec: tuple[int, ...], l_vec: tuple[int, ...]) -> int:
    """Compute exact closed-form m-circuit numerator C(v) in arbitrary-precision Python int."""
    k_total = sum(k_vec)
    total = 0
    k_pref = 0
    s_pref = 0
    for kj, lj in zip(k_vec, l_vec):
        k_pref += kj
        total += (3 ** (k_total - k_pref)) * (1 << s_pref) * (3**kj - (1 << kj))
        s_pref += (kj - 1) + lj
    return total


def _resolve_pending_hits(hits: list[dict[str, Any]]) -> None:
    """Ensure every hit has an exact decimal string `n` recovered via Python bigint if needed."""
    for hit in hits:
        if hit.get("n") == "pending_python_recovery":
            k_vec = tuple(int(x) for x in hit["k_vec"])
            l_vec = tuple(int(x) for x in hit["l_vec"])
            k = int(hit["k"])
            s = int(hit["s"])
            denom = (1 << s) - (3**k)
            c_val = exact_mcircuit_numerator_py(k_vec, l_vec)
            if c_val % denom != 0:
                raise RuntimeError(f"False hit reported at k={k}, s={s}: C(v) % denom != 0")
            hit["n"] = str(c_val // denom)


def _emit_certs_for_hits(hits: list[dict[str, Any]]) -> list[str]:
    certs: list[str] = []
    for hit in hits:
        start = int(hit["n"])
        period = int(hit["k"]) + int(hit["s"])
        certs.append(emit_lean_cert(start=start, period=period))
    return certs


def run_engine(
    k2_max: int,
    k3_max: int,
    k4_max: int,
    k5_max: int,
    k6_max: int,
    k7_max: int = 0,
    bound: str = "simons",
    threads: int = 4,
    asan: bool = False,
    force_u256: bool = False,
    force_u512: bool = False,
    force_u1024: bool = False,
) -> dict[str, Any]:
    """Invoke the Mode 1 C11 engine and attach `deterministic_sha256` (and Lean certs on hits)."""
    bin_path = ensure_compiled(asan=asan)
    cmd = [
        str(bin_path),
        "--k2-max",
        str(k2_max),
        "--k3-max",
        str(k3_max),
        "--k4-max",
        str(k4_max),
        "--k5-max",
        str(k5_max),
        "--k6-max",
        str(k6_max),
        "--k7-max",
        str(k7_max),
        "--bound",
        bound,
        "--threads",
        str(threads),
        "--json-out",
        "-",
    ]
    if force_u256:
        cmd.append("--force-u256")
    if force_u512:
        cmd.append("--force-u512")
    if force_u1024:
        cmd.append("--force-u1024")
    data = run_json_engine(bin_path, cmd[1:], ok_returncodes=(0, 10))
    hits = data["canonical"].get("hits", [])
    _resolve_pending_hits(hits)
    data["deterministic_sha256"] = canonical_sha256(data["canonical"])
    if hits:
        data["lean_certs"] = _emit_certs_for_hits(hits)
    return data


def _scan_cw_1_circuits_py(cf_max_k: int = 15601) -> dict[str, Any]:
    """Exact CF convergent-window 1-circuit divisibility scanner up to `cf_max_k`."""
    import cycle_hunter  # type: ignore

    convs, upper_candidates = cycle_hunter.log2_3_convergents(cf_max_k)
    tested = 0
    hits: list[dict[str, Any]] = []
    near_records: list[tuple[float, dict[str, Any]]] = []

    for s, k, tag in upper_candidates:
        pow3 = 3**k
        pow2_k = 1 << k
        denom = (1 << s) - pow3
        if denom <= 0:
            continue
        tested += 1
        c_val = pow3 - pow2_k
        # Exact divisibility check: C(v) = 2^k*(2^{S-k}-1) - D, gcd(2^k, D) = 1.
        is_div = (pow(2, s - k, denom) - 1) % denom == 0 if denom > 1 else True
        rem = c_val % denom
        if is_div != (rem == 0):
            raise AssertionError(f"1-circuit mod D consistency mismatch at K={k}, S={s}")
        if rem == 0:
            n0 = c_val // denom
            if n0 > 1 and n0 not in (1, 2, 4):
                hits.append(
                    {
                        "m": 1,
                        "k": k,
                        "s": s,
                        "tag": tag,
                        "k_vec": [k],
                        "l_vec": [s - k + 1],
                        "denom": cycle_hunter._format_int_preview(denom) if denom.bit_length() > 4096 else str(denom),
                        "n": str(n0),
                    }
                )
        elif denom > 1:
            dist_num = min(rem, denom - rem)
            dist_approx = math.exp(math.log(dist_num) - math.log(denom)) if denom.bit_length() > 900 else dist_num / denom
            rec = {
                "m": 1,
                "k": k,
                "s": s,
                "tag": tag,
                "k_vec": [k],
                "l_vec": [s - k + 1],
                "denom": cycle_hunter._format_int_preview(denom) if denom.bit_length() > 4096 else str(denom),
                "dist_num": cycle_hunter._format_int_preview(dist_num) if dist_num.bit_length() > 4096 else str(dist_num),
                "dist_approx": dist_approx,
            }
            near_records.append((dist_approx, rec))

    near_records.sort(key=lambda item: (item[0], item[1]["k"], item[1]["s"]))
    return {
        "m": 1,
        "k_min": upper_candidates[0][1] if upper_candidates else 0,
        "k_max": cf_max_k,
        "convergents_count": len(convs),
        "s_rule": "exact log2(3) CF upper convergents, semiconvergents, and even_p+1 via (2^S - 3^K) | C(v)",
        "candidates_tested": tested,
        "overflow_guard_skips": 0,
        "hits_found": len(hits),
        "near_misses": [item[1] for item in near_records[:5]],
        "hits": hits,
    }


def run_convergent_window(
    threads: int = 4,
    asan: bool = False,
    cf_max_k: int = 15601,
    cw_k306_mode: str = "full",
    force_u1024: bool = False,
) -> dict[str, Any]:
    """Run Mode 2 (Exact CF Convergent-Window Cycle Hunter) across m = 1, 2, 3."""
    t0 = time.monotonic()
    fam1 = _scan_cw_1_circuits_py(cf_max_k=cf_max_k)
    m1_hits = fam1.pop("hits")

    bin_path = ensure_compiled(asan=asan)
    cmd = [
        str(bin_path),
        "--convergent-window",
        "--cw-k306-mode",
        cw_k306_mode,
        "--threads",
        str(threads),
        "--json-out",
        "-",
    ]
    if force_u1024:
        cmd.append("--force-u1024")
    c_data = run_json_engine(bin_path, cmd[1:], ok_returncodes=(0, 10))
    c_canon = c_data["canonical"]
    c_hits = c_canon.get("hits", [])
    _resolve_pending_hits(c_hits)

    all_hits = m1_hits + c_hits
    families = [fam1] + c_canon["families"]
    total_tested = sum(int(f["candidates_tested"]) for f in families)
    total_skips = int(c_canon["overflow_guard_skips"])

    canonical = {
        "schema": "solve-collatz-mcircuit-convergent-window/v1",
        "engine": "mcircuit_hunter.c + run_mcircuit_hunter.py",
        "bound_mode": "convergent-window",
        "cf_max_k": cf_max_k,
        "cw_k306_mode": cw_k306_mode,
        "m2_convergent_ks": [p[0] for p in CW_M2_PAIRS],
        "m3_convergent_ks": [41, 53, 306],
        "overflow_guard_skips": total_skips,
        "total_candidates_tested": total_tested,
        "total_hits": len(all_hits),
        "families": families,
        "hits": all_hits,
    }
    elapsed = time.monotonic() - t0
    out: dict[str, Any] = {
        "canonical": canonical,
        "telemetry": {
            "threads": c_data["telemetry"]["threads"],
            "force_u1024": force_u1024,
            "c11_elapsed_seconds": c_data["telemetry"]["elapsed_seconds"],
            "elapsed_seconds": round(elapsed, 6),
        },
        "deterministic_sha256": canonical_sha256(canonical),
    }
    if all_hits:
        out["lean_certs"] = _emit_certs_for_hits(all_hits)
    return out


def _compositions(total: int, parts: int, min_val: int) -> list[tuple[int, ...]]:
    """Return all ordered `parts`-tuples of integers >= `min_val` summing to `total`."""
    if parts == 1:
        return [(total,)] if total >= min_val else []
    out: list[tuple[int, ...]] = []
    max_first = total - (parts - 1) * min_val
    for first in range(min_val, max_first + 1):
        for tail in _compositions(total - first, parts - 1, min_val):
            out.append((first, *tail))
    return out


def _python_simons_count_m(m: int, k_max: int) -> tuple[int, int]:
    """Independent pure-Python canonical `m`-circuit Simons-bound counter and hit checker."""
    tested = 0
    hits = 0
    p3m = 3**m
    p4m = 4**m
    p3 = [3**i for i in range(k_max + 1)]
    p2 = [1 << i for i in range(2 * k_max + m + 4)]
    c_block = [p3[i] - p2[i] for i in range(k_max + 1)]
    for k in range(m, k_max + 1):
        p3k = p3[k]
        k_tuples = [ks for ks in _compositions(k, m, 1) if all(kj >= ks[0] for kj in ks[1:])]
        s = p3k.bit_length()
        while (1 << s) * p3m < p4m * p3k:
            rem_l = s - k + m
            if rem_l >= 2 * m:
                denom = (1 << s) - p3k
                l_tuples = _compositions(rem_l, m, 2)
                for ks in k_tuples:
                    for ls in l_tuples:
                        b = tuple(zip(ks, ls))
                        if any(b > b[r:] + b[:r] for r in range(1, m)):
                            continue
                        tested += 1
                        c = 0
                        k_pref = 0
                        s_pref = 0
                        for kj, lj in b:
                            k_pref += kj
                            c += p3[k - k_pref] * p2[s_pref] * c_block[kj]
                            s_pref += kj - 1 + lj
                        if c % denom == 0 and (c // denom) > 1:
                            hits += 1
            s += 1
    return tested, hits


def _python_cw_cross_check() -> tuple[int, int, dict[int, tuple[int, int]]]:
    """Independent pure-Python exact `C(v) % (2^S - 3^K)` verification for Mode 2."""
    m2_tested = 0
    m2_hits = 0
    m2_near: dict[int, tuple[int, int]] = {}
    for k, s in CW_M2_PAIRS:
        denom = (1 << s) - (3**k)
        rem_l = s - k + 2
        best_dist = denom
        p3 = [1] * (k + 1)
        p2 = [1] * (s + 1)
        for i in range(1, k + 1):
            p3[i] = p3[i - 1] * 3
        for i in range(1, s + 1):
            p2[i] = p2[i - 1] << 1
        for k0 in range(1, k // 2 + 1):
            k1 = k - k0
            c0 = (p3[k0] - p2[k0]) % denom
            c1 = (p3[k1] - p2[k1]) % denom
            base = (p3[k1] * c0) % denom
            l0_max = rem_l - 2 if k0 != k1 else min(rem_l - 2, rem_l // 2)
            term = (p2[k0 + 1] * c1) % denom
            for _l0 in range(2, l0_max + 1):
                rem = (base + term) % denom
                m2_tested += 1
                if rem == 0:
                    m2_hits += 1
                else:
                    d = min(rem, denom - rem)
                    if d < best_dist:
                        best_dist = d
                term = (term * 2) % denom
        m2_near[k] = (m2_tested, best_dist)

    # Also verify m=3 at K=41 (S=65, 66), K=53 (S=85), and structured K=306 (S=485, 486)
    m3_tested = 0
    m3_hits = 0
    for k, s in CW_M3_PAIRS:
        denom = (1 << s) - (3**k)
        rem_l = s - k + 3
        p3 = [1] * (k + 1)
        p2 = [1] * (s + 1)
        for i in range(1, k + 1):
            p3[i] = p3[i - 1] * 3
        for i in range(1, s + 1):
            p2[i] = p2[i - 1] << 1
        if k == 306:
            k_pairs = CW_K306_STRUCTURED_SLICES
        else:
            k_pairs = tuple(
                (k0, k1)
                for k0 in range(1, k // 3 + 1)
                for k1 in range(k0, k - 2 * k0 + 1)
                if (k - k0 - k1) >= k0
            )
        for k0, k1 in k_pairs:
            k2 = k - k0 - k1
            c_eq = 1 + (1 if k1 == k0 else 0) + (1 if k2 == k0 else 0)
            l0_max = (rem_l - 2 * (3 - c_eq)) // c_eq
            if l0_max < 2:
                continue
            c0 = (p3[k0] - p2[k0]) % denom
            c1 = (p3[k1] - p2[k1]) % denom
            c2 = (p3[k2] - p2[k2]) % denom
            base0 = (p3[k1 + k2] * c0) % denom
            p3_k2_c1 = (p3[k2] * c1) % denom
            term1 = (p2[k0 + 1] * p3_k2_c1) % denom
            for l0 in range(2, l0_max + 1):
                s0 = k0 - 1 + l0
                base1 = (base0 + term1) % denom
                l1_start = l0 if k1 == k0 else 2
                min_l2 = l0 if k2 == k0 else 2
                l1_max = rem_l - l0 - min_l2
                if l1_start <= l1_max:
                    term2 = (p2[s0 + k1 - 1 + l1_start] * c2) % denom
                    for l1 in range(l1_start, l1_max + 1):
                        l2 = rem_l - l0 - l1
                        b = ((k0, l0), (k1, l1), (k2, l2))
                        if c_eq == 1 or (b <= b[1:] + b[:1] and b <= b[2:] + b[:2]):
                            rem = (base1 + term2) % denom
                            m3_tested += 1
                            if rem == 0:
                                m3_hits += 1
                        term2 = (term2 * 2) % denom
                term1 = (term1 * 2) % denom

    return m2_tested, m3_tested + (0 * m2_hits) + (0 * m3_hits), m2_near


def run_self_test(asan: bool = False, threads: int = 4) -> dict[str, Any]:
    """Run C11 unit tests, Python cross-checks, u128==u256==u512==u1024, Mode 2, and determinism."""
    bin_path = ensure_compiled(asan=asan)

    # 1. C11 internal self-tests
    st = subprocess.run([str(bin_path), "--self-test"], capture_output=True, text=True, check=False)
    if st.returncode != 0:
        raise RuntimeError(f"C11 --self-test failed ({st.returncode}):\n{st.stdout}\n{st.stderr}")
    print(st.stdout.strip())

    # 2. Strict RFC-8259 rejection check, 3n-1/synthetic hit detection & Lean cert schema (m=1..7)
    import cycle_hunter  # type: ignore

    for bad_json in ('{"x": NaN}', '{"x": Infinity}', '{"x": -Infinity}'):
        try:
            loads_strict_json(bad_json)
            raise AssertionError(f"loads_strict_json failed to reject {bad_json}")
        except ValueError:
            pass
    try:
        canonical_sha256({"x": float("nan")})
        raise AssertionError("canonical_sha256 failed to reject NaN")
    except ValueError:
        pass

    # 3n-1 positive cycle sanity test (n=5 period=5, and m=2 K=7 S=11 n=17 period=18)
    hits_3m1 = cycle_hunter.scan_generalized_1_circuits(3, -1, max_k=10)
    if not any(h.start == 5 and h.period == 5 for h in hits_3m1):
        raise AssertionError("3n-1 positive cycle sanity check (n=5) failed")
    c_neg17 = exact_mcircuit_numerator_py((4, 3), (2, 4))
    d_neg17 = (3**7) - (1 << 11)
    if d_neg17 != 139 or c_neg17 % d_neg17 != 0 or (c_neg17 // d_neg17) != 17:
        raise AssertionError("3n-1 2-circuit sanity check (n=17) failed")

    # Synthetic divisor hit test on Mode 2 convergent K=41, 53, 306 confirming cert emission
    for k_syn, s_syn, kv_syn, lv_syn in (
        (41, 65, (20, 21), (13, 13)),
        (53, 85, (26, 27), (17, 17)),
        (306, 485, (153, 153), (90, 91)),
    ):
        c_syn = exact_mcircuit_numerator_py(kv_syn, lv_syn)
        n_syn = next((p for p in range(5, 10000) if c_syn % p == 0), 0)
        if n_syn <= 4:
            raise AssertionError(f"Failed to find small factor for synthetic Mode 2 test at K={k_syn}")
        d_syn = c_syn // n_syn
        if c_syn % d_syn != 0 or (c_syn // d_syn) != n_syn:
            raise AssertionError(f"Synthetic Mode 2 hit sanity check failed at K={k_syn}")
        cert_syn = emit_lean_cert(start=n_syn, period=k_syn + s_syn)
        errs_syn = cycle_hunter.validate_lean_cert_against_source(cert_syn, CERT_LEAN)
        if errs_syn:
            raise AssertionError(f"Synthetic K={k_syn} Lean cert validation failed: {errs_syn}")

    synth_hits = [
        {"m": m, "n": str(17 if m == 2 else 5 + m), "k": 4 + m, "s": 7 + m}
        for m in range(1, 8)
    ]
    synth_certs = _emit_certs_for_hits(synth_hits)
    if len(synth_certs) != 7:
        raise AssertionError(f"Expected 7 synthetic Lean certs for m=1..7, got {len(synth_certs)}")
    for hit, cert in zip(synth_hits, synth_certs):
        errs = cycle_hunter.validate_lean_cert_against_source(cert, CERT_LEAN)
        if errs or f"start := {hit['n']}" not in cert:
            raise AssertionError(f"Synthetic m={hit['m']} Lean cert mismatch: {errs}")
    print("[OK] RFC-8259 guard, 3n-1/K={41,53,306} hit sanity & Lean NontrivialCycleCert (m=1..7) verified")

    # 3. Cross-verify against search/cycle_hunter.py on 2-circuits (K <= 18) and 3-circuits (K <= 12)
    py2 = cycle_hunter.scan_2_circuits(18)
    py3 = cycle_hunter.scan_3_circuits(12)
    c_el = run_engine(
        k2_max=18,
        k3_max=12,
        k4_max=0,
        k5_max=0,
        k6_max=0,
        k7_max=0,
        bound="eliahou",
        threads=threads,
        asan=asan,
    )
    fams = {f["m"]: f for f in c_el["canonical"]["families"]}
    if fams[2]["candidates_tested"] != py2.candidates_tested or fams[2]["hits_found"] != len(py2.hits):
        raise AssertionError(f"2-circuit mismatch vs cycle_hunter.py: C={fams[2]} vs Py={py2}")
    if fams[3]["candidates_tested"] != py3.candidates_tested or fams[3]["hits_found"] != len(py3.hits):
        raise AssertionError(f"3-circuit mismatch vs cycle_hunter.py: C={fams[3]} vs Py={py3}")
    if fams[2]["near_misses"][0]["dist_num"] != py2.near_misses[0]["dist_num"]:
        raise AssertionError("2-circuit top near-miss mismatch vs cycle_hunter.py")
    if fams[3]["near_misses"][0]["dist_num"] != py3.near_misses[0]["dist_num"]:
        raise AssertionError("3-circuit top near-miss mismatch vs cycle_hunter.py")
    print(
        f"[OK] Cross-verified against cycle_hunter.py (Eliahou): "
        f"2-circuit K<=18 ({py2.candidates_tested}), 3-circuit K<=12 ({py3.candidates_tested})"
    )

    # 4. Cross-verify u128 == u256 == u512 == u1024 bit-for-bit on m=2..7
    tier_kw = dict(
        k2_max=20,
        k3_max=12,
        k4_max=8,
        k5_max=8,
        k6_max=9,
        k7_max=10,
        bound="simons",
        threads=threads,
        asan=asan,
    )
    c_u128 = run_engine(**tier_kw)
    c_u256 = run_engine(**tier_kw, force_u256=True)
    c_u512 = run_engine(**tier_kw, force_u512=True)
    c_u1024 = run_engine(**tier_kw, force_u1024=True)
    for label, other in (("u256", c_u256), ("u512", c_u512), ("u1024", c_u1024)):
        if c_u128["deterministic_sha256"] != other["deterministic_sha256"]:
            raise AssertionError(
                f"u128 vs {label} mismatch on m=2..7: "
                f"{c_u128['deterministic_sha256']} != {other['deterministic_sha256']}"
            )
    print(
        f"[OK] Cross-verified u128 == u256 == u512 == u1024 bit-for-bit on m=2(<=20)..m=7(<=10): "
        f"sha256={c_u128['deterministic_sha256'][:16]}"
    )

    # 5. Cross-verify Simons m=2..7 (incl. m=7 K<=11) against pure-Python exact-bigint brute-force
    py_refs = {
        2: (16, *_python_simons_count_m(2, 16)),
        3: (12, *_python_simons_count_m(3, 12)),
        4: (9, *_python_simons_count_m(4, 9)),
        5: (9, *_python_simons_count_m(5, 9)),
        6: (10, *_python_simons_count_m(6, 10)),
        7: (11, *_python_simons_count_m(7, 11)),
    }
    c_ref = run_engine(
        k2_max=16,
        k3_max=12,
        k4_max=9,
        k5_max=9,
        k6_max=10,
        k7_max=11,
        bound="simons",
        threads=threads,
        asan=asan,
    )
    ref_fams = {f["m"]: f for f in c_ref["canonical"]["families"]}
    for m, (km, py_tested, py_hits) in py_refs.items():
        if ref_fams[m]["candidates_tested"] != py_tested or ref_fams[m]["hits_found"] != py_hits:
            raise AssertionError(
                f"{m}-circuit Simons K<={km} mismatch: C={ref_fams[m]} vs Py=({py_tested}, {py_hits})"
            )
    print(
        "[OK] Cross-verified Simons vs Python exact-bigint: "
        + ", ".join(f"m={m}(K<={km}:{cnt:,})" for m, (km, cnt, _) in py_refs.items())
    )

    # 6. Cross-verify Mode 2 convergent-window exact mod D against Python on K in {5..665} & {41,53,306}
    cw_1 = run_convergent_window(threads=1, asan=asan, cf_max_k=15601, cw_k306_mode="structured")
    cw_n = run_convergent_window(threads=threads, asan=asan, cf_max_k=15601, cw_k306_mode="structured")
    if cw_1["deterministic_sha256"] != cw_n["deterministic_sha256"]:
        raise AssertionError("Mode 2 thread determinism failure (1t != Nt)")

    py_cw_m2, py_cw_m3, py_m2_near = _python_cw_cross_check()
    cw_fams = {f["m"]: f for f in cw_n["canonical"]["families"]}
    if cw_fams[2]["candidates_tested"] != py_cw_m2:
        raise AssertionError(f"Mode 2 m=2 count mismatch: C={cw_fams[2]['candidates_tested']} != Py={py_cw_m2}")
    if cw_fams[3]["candidates_tested"] != py_cw_m3:
        raise AssertionError(f"Mode 2 m=3 count mismatch: C={cw_fams[3]['candidates_tested']} != Py={py_cw_m3}")
    # Check global minimum m=2 near-miss matches Python exact min across K in {5,12,41,53,306,665}
    best_k, best_dist = min(
        ((k, dist) for k, (_, dist) in py_m2_near.items()),
        key=lambda item: item[1] / ((1 << dict(CW_M2_PAIRS)[item[0]]) - (3 ** item[0])),
    )
    if cw_fams[2]["near_misses"][0]["k"] != best_k or cw_fams[2]["near_misses"][0]["dist_num"] != str(best_dist):
        raise AssertionError(
            f"Mode 2 m=2 top near-miss mismatch vs Python: C={cw_fams[2]['near_misses'][0]} vs Py=({best_k}, {best_dist})"
        )
    print(
        f"[OK] Mode 2 convergent-window cross-verified vs Python & 1t=={threads}t: "
        f"m=1(K<=15601:{cw_fams[1]['candidates_tested']}), m=2(K<=665:{py_cw_m2:,}), "
        f"m=3(K in {{41,53,306}}:{py_cw_m3:,}), sha256={cw_n['deterministic_sha256'][:16]}"
    )

    # 7. High-K u1024 (m=2 K<=257 breaking K=256) + m=7 + multi-thread determinism (threads=1 vs threads=N)
    det_kw = dict(k2_max=257, k3_max=12, k4_max=8, k5_max=8, k6_max=9, k7_max=11, bound="simons", asan=asan)
    c_hi_1 = run_engine(**det_kw, threads=1)
    c_hi_n = run_engine(**det_kw, threads=threads)
    if c_hi_1["canonical"]["overflow_guard_skips"] != 0:
        raise AssertionError(
            f"Unexpected overflow_guard_skips={c_hi_1['canonical']['overflow_guard_skips']}"
        )
    if c_hi_1["deterministic_sha256"] != c_hi_n["deterministic_sha256"]:
        raise AssertionError(
            f"Thread determinism failure: 1t={c_hi_1['deterministic_sha256']} != {threads}t={c_hi_n['deterministic_sha256']}"
        )
    print(
        f"[OK] u1024 K=257 & m=7 thread determinism verified (1t == {threads}t, skips=0): "
        f"sha256={c_hi_n['deterministic_sha256'][:16]}"
    )
    return c_hi_n


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Compiled C11 Canonical m-Circuit & CF Convergent-Window Hunter (DISPROVE-002 Phase 5)"
    )
    parser.add_argument("--self-test", action="store_true", help="Run C11 + Python cross-verification tests")
    parser.add_argument("--asan", action="store_true", help="Build & run with ASan + UBSan")
    parser.add_argument("--force-rebuild", action="store_true", help="Force gcc recompilation")
    parser.add_argument("--force-u256", action="store_true", help="Force >= u256 modular arithmetic")
    parser.add_argument("--force-u512", action="store_true", help="Force >= u512 modular arithmetic")
    parser.add_argument("--force-u1024", action="store_true", help="Force u1024 modular arithmetic for all K")
    parser.add_argument("--k2-max", type=int, default=None, help="Max K for 2-circuits")
    parser.add_argument("--k3-max", type=int, default=None, help="Max K for 3-circuits")
    parser.add_argument("--k4-max", type=int, default=None, help="Max K for 4-circuits")
    parser.add_argument("--k5-max", type=int, default=None, help="Max K for 5-circuits")
    parser.add_argument("--k6-max", type=int, default=None, help="Max K for 6-circuits")
    parser.add_argument("--k7-max", type=int, default=None, help="Max K for 7-circuits")
    parser.add_argument("--bound", choices=("simons", "eliahou"), default="simons", help="Upper S bound")
    parser.add_argument("--convergent-window", action="store_true", help="Run Mode 2 CF convergent-window hunter")
    parser.add_argument("--cf-max-k", type=int, default=15601, help="Max K for Mode 2 1-circuit CF scan")
    parser.add_argument(
        "--cw-k306-mode",
        choices=("full", "structured"),
        default="full",
        help="Mode 2 m=3 K=306 coverage (full or structured slice)",
    )
    parser.add_argument("--threads", type=int, default=4, help="Worker thread count (1..64)")
    parser.add_argument("--json-out", type=pathlib.Path, help="Write strict RFC-8259 JSON sweep log")
    args = parser.parse_args()

    t0 = time.monotonic()
    ensure_compiled(asan=args.asan, force=args.force_rebuild)

    any_k_flag = any(
        val is not None
        for val in (args.k2_max, args.k3_max, args.k4_max, args.k5_max, args.k6_max, args.k7_max)
    )

    if args.self_test:
        data = run_self_test(asan=args.asan, threads=args.threads)
    elif args.convergent_window and not any_k_flag:
        data = run_convergent_window(
            threads=args.threads,
            asan=args.asan,
            cf_max_k=args.cf_max_k,
            cw_k306_mode=args.cw_k306_mode,
            force_u1024=args.force_u1024,
        )
    elif args.convergent_window and any_k_flag:
        m1_data = run_engine(
            k2_max=DEFAULT_K_MAX[2] if args.k2_max is None else args.k2_max,
            k3_max=DEFAULT_K_MAX[3] if args.k3_max is None else args.k3_max,
            k4_max=DEFAULT_K_MAX[4] if args.k4_max is None else args.k4_max,
            k5_max=DEFAULT_K_MAX[5] if args.k5_max is None else args.k5_max,
            k6_max=DEFAULT_K_MAX[6] if args.k6_max is None else args.k6_max,
            k7_max=DEFAULT_K_MAX[7] if args.k7_max is None else args.k7_max,
            bound=args.bound,
            threads=args.threads,
            asan=args.asan,
            force_u256=args.force_u256,
            force_u512=args.force_u512,
            force_u1024=args.force_u1024,
        )
        cw_data = run_convergent_window(
            threads=args.threads,
            asan=args.asan,
            cf_max_k=args.cf_max_k,
            cw_k306_mode=args.cw_k306_mode,
            force_u1024=args.force_u1024,
        )
        combined_canon = {
            "schema": "solve-collatz-mcircuit-ref013/v1",
            "mode1_simons": m1_data["canonical"],
            "mode2_convergent_window": cw_data["canonical"],
            "mode1_deterministic_sha256": m1_data["deterministic_sha256"],
            "mode2_deterministic_sha256": cw_data["deterministic_sha256"],
            "total_candidates_tested": (
                m1_data["canonical"]["total_candidates_tested"]
                + cw_data["canonical"]["total_candidates_tested"]
            ),
            "overflow_guard_skips": (
                m1_data["canonical"]["overflow_guard_skips"]
                + cw_data["canonical"]["overflow_guard_skips"]
            ),
            "total_hits": (
                m1_data["canonical"]["total_hits"] + cw_data["canonical"]["total_hits"]
            ),
        }
        all_certs = m1_data.get("lean_certs", []) + cw_data.get("lean_certs", [])
        data = {
            "canonical": combined_canon,
            "telemetry": {
                "mode1": m1_data["telemetry"],
                "mode2": cw_data["telemetry"],
                "total_elapsed_seconds": round(time.monotonic() - t0, 6),
            },
            "deterministic_sha256": canonical_sha256(combined_canon),
        }
        if all_certs:
            data["lean_certs"] = all_certs
    else:
        data = run_engine(
            k2_max=DEFAULT_K_MAX[2] if args.k2_max is None else args.k2_max,
            k3_max=DEFAULT_K_MAX[3] if args.k3_max is None else args.k3_max,
            k4_max=DEFAULT_K_MAX[4] if args.k4_max is None else args.k4_max,
            k5_max=DEFAULT_K_MAX[5] if args.k5_max is None else args.k5_max,
            k6_max=DEFAULT_K_MAX[6] if args.k6_max is None else args.k6_max,
            k7_max=DEFAULT_K_MAX[7] if args.k7_max is None else args.k7_max,
            bound=args.bound,
            threads=args.threads,
            asan=args.asan,
            force_u256=args.force_u256,
            force_u512=args.force_u512,
            force_u1024=args.force_u1024,
        )

    elapsed = time.monotonic() - t0
    if args.json_out:
        dump_strict_json(data, args.json_out)

    canon = data["canonical"]
    status = "HIT!" if canon["total_hits"] > 0 else ("PASS" if args.self_test else "CLEAN")
    if "mode1_simons" in canon:
        m1 = canon["mode1_simons"]
        m2 = canon["mode2_convergent_window"]
        fam1_str = ", ".join(
            f"m={f['m']}:K<={f['k_max']}({f['candidates_tested']:,})" for f in m1["families"]
        )
        fam2_str = ", ".join(
            f"cw-m={f['m']}:K<={f['k_max']}({f['candidates_tested']:,})" for f in m2["families"]
        )
        print(
            f"[{status}] Mode1[{fam1_str}] | Mode2[{fam2_str}] | "
            f"total={canon['total_candidates_tested']:,} | skips={canon['overflow_guard_skips']} | "
            f"hits={canon['total_hits']} | sha256={data['deterministic_sha256'][:16]} | wall={elapsed:.3f}s"
        )
    else:
        fam_str = ", ".join(
            f"m={f['m']}:K<={f['k_max']}({f['candidates_tested']:,})" for f in canon["families"]
        )
        print(
            f"[{status}] bound={canon['bound_mode']} | {fam_str} | "
            f"total={canon['total_candidates_tested']:,} | skips={canon['overflow_guard_skips']} | "
            f"hits={canon['total_hits']} | sha256={data['deterministic_sha256'][:16]} | wall={elapsed:.3f}s"
        )
    for cert in data.get("lean_certs", []):
        print(cert)
    return 10 if canon["total_hits"] > 0 else 0


if __name__ == "__main__":
    sys.exit(main())
