#!/usr/bin/env python3
"""Pure-stdlib Python wrapper for `mcircuit_hunter.c` (Track B `DISPROVE-002 Phase 4`).

Auto-compiles `search/mcircuit_hunter/mcircuit_hunter.c` into content-hashed
`/tmp/solve_collatz_mcircuit_hunter_<sha12>[_asan]` via `scripts/native_cache.py`,
keeping the git working tree 100% free of binaries. Validates exact agreement against
`search/cycle_hunter.py`, cross-verifies `u128 == u256 == u512` bit-for-bit on `m=2..6`,
cross-verifies `m=2..6` Simons-de Weger circuits against an independent pure-Python
exact-bigint reference, verifies multi-thread determinism, emits Lean
`NontrivialCycleCert` on any hit, and enforces strict RFC-8259 JSON serialization.
"""

from __future__ import annotations

import argparse
import pathlib
import subprocess
import sys
import time
from typing import Any


REPO_SEARCH_DIR = pathlib.Path(__file__).resolve().parent
SEARCH_DIR = REPO_SEARCH_DIR.parent
REPO_ROOT = SEARCH_DIR.parent
SCRIPTS_DIR = REPO_ROOT / "scripts"
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))

from native_cache import (  # type: ignore  # noqa: E402
    atomic_compile,
    cached_binary_path,
    canonical_sha256,
    dump_strict_json,
    loads_strict_json,
)

C_SOURCE = REPO_SEARCH_DIR / "mcircuit_hunter.c"
CERT_LEAN = REPO_ROOT / "Collatz" / "Disprove" / "Cert.lean"


def ensure_compiled(asan: bool = False, force: bool = False) -> pathlib.Path:
    """Compile `mcircuit_hunter.c` into `/tmp/` via `scripts/native_cache.py`."""
    if not C_SOURCE.exists():
        raise FileNotFoundError(f"Missing C source: {C_SOURCE}")
    suffix = "_asan" if asan else ""
    target = cached_binary_path("solve_collatz_mcircuit_hunter", [REPO_SEARCH_DIR], suffix=suffix)
    cmd = [
        "gcc",
        "-O2" if asan else "-O3",
        "-Wall",
        "-Wextra",
        "-Werror",
        "-std=c11",
        "-pthread",
    ]
    if asan:
        cmd.extend(["-g", "-fsanitize=address,undefined", "-fno-omit-frame-pointer"])
    cmd.extend([str(C_SOURCE), "-lm", "-o", "{out}"])
    return atomic_compile(cmd, target, force=force)


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
    bound: str,
    threads: int,
    asan: bool = False,
    force_u256: bool = False,
    force_u512: bool = False,
) -> dict[str, Any]:
    """Invoke the compiled C binary and attach `deterministic_sha256` (and Lean certs on hits)."""
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
    res = subprocess.run(cmd, capture_output=True, text=True, check=False)
    if res.returncode not in (0, 10):
        raise RuntimeError(f"mcircuit_hunter exited with {res.returncode}:\n{res.stderr}")
    data = loads_strict_json(res.stdout)
    data["deterministic_sha256"] = canonical_sha256(data["canonical"])
    hits = data["canonical"].get("hits", [])
    if hits:
        data["lean_certs"] = _emit_certs_for_hits(hits)
    return data


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
    for k in range(m, k_max + 1):
        p3k = 3**k
        k_tuples = _compositions(k, m, 1)
        s = p3k.bit_length()
        while (1 << s) * p3m < p4m * p3k:
            rem_l = s - k + m
            if rem_l >= 2 * m:
                denom = (1 << s) - p3k
                l_tuples = _compositions(rem_l, m, 2)
                for ks in k_tuples:
                    k0 = ks[0]
                    if any(kj < k0 for kj in ks[1:]):
                        continue
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
                            c += (3 ** (k - k_pref)) * (1 << s_pref) * (3**kj - (1 << kj))
                            s_pref += kj - 1 + lj
                        if c % denom == 0 and (c // denom) > 1:
                            hits += 1
            s += 1
    return tested, hits


def run_self_test(asan: bool = False, threads: int = 4) -> dict[str, Any]:
    """Run C11 unit tests, Python cross-checks, u128==u256==u512 equivalence, and determinism."""
    bin_path = ensure_compiled(asan=asan)

    # 1. C11 internal self-tests
    st = subprocess.run([str(bin_path), "--self-test"], capture_output=True, text=True, check=False)
    if st.returncode != 0:
        raise RuntimeError(f"C11 --self-test failed ({st.returncode}):\n{st.stdout}\n{st.stderr}")
    print(st.stdout.strip())

    # 2. Strict RFC-8259 rejection check & Lean NontrivialCycleCert schema check (m=1..6)
    sys.path.insert(0, str(SEARCH_DIR))
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

    for start, period in ((1, 3), (5, 5)):
        cert = emit_lean_cert(start=start, period=period)
        errs = cycle_hunter.validate_lean_cert_against_source(cert, CERT_LEAN)
        if errs:
            raise AssertionError(f"Lean cert validation failed for ({start}, {period}): {errs}")
    synth_hits = [
        {"m": m, "n": str(17 if m == 2 else 5 + m), "k": 4 + m, "s": 7 + m}
        for m in range(1, 7)
    ]
    synth_certs = _emit_certs_for_hits(synth_hits)
    if len(synth_certs) != 6:
        raise AssertionError(f"Expected 6 synthetic Lean certs for m=1..6, got {len(synth_certs)}")
    for hit, cert in zip(synth_hits, synth_certs):
        errs = cycle_hunter.validate_lean_cert_against_source(cert, CERT_LEAN)
        if errs or f"start := {hit['n']}" not in cert:
            raise AssertionError(f"Synthetic m={hit['m']} Lean cert mismatch: {errs}")
    print("[OK] RFC-8259 strict JSON guard & Lean NontrivialCycleCert schema (m=1..6) verified")

    # 3. Cross-verify against search/cycle_hunter.py on 2-circuits (K <= 18) and 3-circuits (K <= 12)
    py2 = cycle_hunter.scan_2_circuits(18)
    py3 = cycle_hunter.scan_3_circuits(12)
    c_el = run_engine(
        k2_max=18,
        k3_max=12,
        k4_max=0,
        k5_max=0,
        k6_max=0,
        bound="eliahou",
        threads=threads,
        asan=asan,
    )
    fams = {f["m"]: f for f in c_el["canonical"]["families"]}

    if fams[2]["candidates_tested"] != py2.candidates_tested or fams[2]["hits_found"] != len(py2.hits):
        raise AssertionError(
            f"2-circuit mismatch vs cycle_hunter.py: C={fams[2]} vs Py=({py2.candidates_tested}, {len(py2.hits)})"
        )
    if fams[3]["candidates_tested"] != py3.candidates_tested or fams[3]["hits_found"] != len(py3.hits):
        raise AssertionError(
            f"3-circuit mismatch vs cycle_hunter.py: C={fams[3]} vs Py=({py3.candidates_tested}, {len(py3.hits)})"
        )
    if fams[2]["near_misses"][0]["dist_num"] != py2.near_misses[0]["dist_num"]:
        raise AssertionError(
            f"2-circuit top near-miss mismatch: C={fams[2]['near_misses'][0]} vs Py={py2.near_misses[0]}"
        )
    if fams[3]["near_misses"][0]["dist_num"] != py3.near_misses[0]["dist_num"]:
        raise AssertionError(
            f"3-circuit top near-miss mismatch: C={fams[3]['near_misses'][0]} vs Py={py3.near_misses[0]}"
        )
    print(
        f"[OK] Cross-verified against cycle_hunter.py (Eliahou): "
        f"2-circuit K<=18 ({py2.candidates_tested}), 3-circuit K<=12 ({py3.candidates_tested})"
    )

    # 4. Cross-verify u128 == u256 == u512 bit-for-bit on m=2..6
    tier_kw = dict(k2_max=50, k3_max=20, k4_max=14, k5_max=12, k6_max=12, bound="simons", threads=threads, asan=asan)
    c_u128 = run_engine(**tier_kw)
    c_u256 = run_engine(**tier_kw, force_u256=True)
    c_u512 = run_engine(**tier_kw, force_u512=True)
    if c_u128["deterministic_sha256"] != c_u256["deterministic_sha256"]:
        raise AssertionError(
            f"u128 vs u256 mismatch on m=2..6: "
            f"{c_u128['deterministic_sha256']} != {c_u256['deterministic_sha256']}"
        )
    if c_u128["deterministic_sha256"] != c_u512["deterministic_sha256"]:
        raise AssertionError(
            f"u128 vs u512 mismatch on m=2..6: "
            f"{c_u128['deterministic_sha256']} != {c_u512['deterministic_sha256']}"
        )
    print(
        f"[OK] Cross-verified u128 == u256 == u512 bit-for-bit on m=2(<=50)..m=6(<=12): "
        f"sha256={c_u128['deterministic_sha256'][:16]}"
    )

    # 5. Cross-verify Simons m=2..6 against independent pure-Python exact-bigint references
    py_refs = {
        2: (20, *_python_simons_count_m(2, 20)),
        3: (15, *_python_simons_count_m(3, 15)),
        4: (10, *_python_simons_count_m(4, 10)),
        5: (12, *_python_simons_count_m(5, 12)),
        6: (13, *_python_simons_count_m(6, 13)),
    }
    c_ref = run_engine(
        k2_max=20, k3_max=15, k4_max=10, k5_max=12, k6_max=13, bound="simons", threads=threads, asan=asan
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

    # 6. High-K u512 (m=2 K<=240) + m=6 + multi-thread determinism check (threads=1 vs threads=N)
    det_kw = dict(k2_max=240, k3_max=24, k4_max=14, k5_max=12, k6_max=13, bound="simons", asan=asan)
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
        f"[OK] u512 K=240 & m=6 thread determinism verified (1t == {threads}t, skips=0): "
        f"sha256={c_hi_n['deterministic_sha256'][:16]}"
    )
    return c_hi_n


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Compiled C11 Canonical m-Circuit Diophantine Hunter (DISPROVE-002 Phase 4)"
    )
    parser.add_argument("--self-test", action="store_true", help="Run C11 + Python cross-verification tests")
    parser.add_argument("--asan", action="store_true", help="Build & run with ASan + UBSan")
    parser.add_argument("--force-rebuild", action="store_true", help="Force gcc recompilation")
    parser.add_argument("--force-u256", action="store_true", help="Force >= u256 modular arithmetic")
    parser.add_argument("--force-u512", action="store_true", help="Force u512 modular arithmetic for all K")
    parser.add_argument("--k2-max", type=int, default=240, help="Max K for 2-circuits")
    parser.add_argument("--k3-max", type=int, default=120, help="Max K for 3-circuits")
    parser.add_argument("--k4-max", type=int, default=70, help="Max K for 4-circuits")
    parser.add_argument("--k5-max", type=int, default=44, help="Max K for 5-circuits")
    parser.add_argument("--k6-max", type=int, default=32, help="Max K for 6-circuits")
    parser.add_argument("--bound", choices=("simons", "eliahou"), default="simons", help="Upper S bound")
    parser.add_argument("--threads", type=int, default=4, help="Worker thread count (1..64)")
    parser.add_argument("--json-out", type=pathlib.Path, help="Write strict RFC-8259 JSON sweep log")
    args = parser.parse_args()

    t0 = time.monotonic()
    ensure_compiled(asan=args.asan, force=args.force_rebuild)

    if args.self_test:
        data = run_self_test(asan=args.asan, threads=args.threads)
    else:
        data = run_engine(
            k2_max=args.k2_max,
            k3_max=args.k3_max,
            k4_max=args.k4_max,
            k5_max=args.k5_max,
            k6_max=args.k6_max,
            bound=args.bound,
            threads=args.threads,
            asan=args.asan,
            force_u256=args.force_u256,
            force_u512=args.force_u512,
        )

    elapsed = time.monotonic() - t0
    if args.json_out:
        dump_strict_json(data, args.json_out)

    canon = data["canonical"]
    status = "HIT!" if canon["total_hits"] > 0 else ("PASS" if args.self_test else "CLEAN")
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
