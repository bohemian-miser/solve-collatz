#!/usr/bin/env python3
"""Pure-stdlib Python wrapper for `mcircuit_hunter.c` (Track B `DISPROVE-002 Phase 3`).

Auto-compiles `search/mcircuit_hunter/mcircuit_hunter.c` into content-hashed
`/tmp/solve_collatz_mcircuit_hunter_<sha12>[_asan]` (never colliding across worktrees),
keeping the git working tree 100% free of binaries. Validates exact agreement against
`search/cycle_hunter.py`, cross-verifies `u256` vs `u128` on `m=2..4`, cross-verifies
`m=5` Simons-de Weger circuits against an independent Python reference, verifies
multi-thread determinism, emits Lean `NontrivialCycleCert` on any hit, and enforces
strict RFC-8259 JSON serialization.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import pathlib
import subprocess
import sys
import time
from typing import Any


REPO_SEARCH_DIR = pathlib.Path(__file__).resolve().parent
SEARCH_DIR = REPO_SEARCH_DIR.parent
REPO_ROOT = SEARCH_DIR.parent
C_SOURCE = REPO_SEARCH_DIR / "mcircuit_hunter.c"
CERT_LEAN = REPO_ROOT / "Collatz" / "Disprove" / "Cert.lean"


def _cached_bin_path(asan: bool) -> pathlib.Path:
    """Return a content-hashed `/tmp/` binary path so worktrees/branches never collide."""
    h = hashlib.sha256()
    for path in sorted(REPO_SEARCH_DIR.glob("*.[ch]")):
        h.update(path.name.encode("utf-8"))
        h.update(b"\0")
        h.update(path.read_bytes())
    digest = h.hexdigest()[:12]
    suffix = "_asan" if asan else ""
    return pathlib.Path(f"/tmp/solve_collatz_mcircuit_hunter_{digest}{suffix}")


def ensure_compiled(asan: bool = False, force: bool = False) -> pathlib.Path:
    """Compile `mcircuit_hunter.c` into `/tmp/` keyed by source SHA-256."""
    if not C_SOURCE.exists():
        raise FileNotFoundError(f"Missing C source: {C_SOURCE}")
    target = _cached_bin_path(asan=asan)
    if not force and target.exists():
        return target

    tmp_bin = pathlib.Path(f"{target}.{os.getpid()}")
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
    cmd.extend([str(C_SOURCE), "-lm", "-o", str(tmp_bin)])

    res = subprocess.run(cmd, capture_output=True, text=True, check=False)
    if res.returncode != 0:
        if tmp_bin.exists():
            tmp_bin.unlink()
        raise RuntimeError(f"gcc failed ({res.returncode}):\n{res.stderr}")
    os.replace(tmp_bin, target)
    return target


def _reject_non_rfc8259(val: str) -> None:
    raise ValueError(f"Non-RFC-8259 JSON constant: {val}")


def parse_strict_json(raw: str) -> dict[str, Any]:
    """Parse JSON strictly rejecting NaN, Infinity, and -Infinity."""
    data = json.loads(raw, parse_constant=_reject_non_rfc8259)
    json.dumps(data, allow_nan=False)
    return data


def canonical_sha256(canonical_obj: dict[str, Any]) -> str:
    """Compute reproducible SHA-256 digest over the timing-free canonical payload."""
    encoded = json.dumps(
        canonical_obj, sort_keys=True, separators=(",", ":"), allow_nan=False
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


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
    bound: str,
    threads: int,
    asan: bool = False,
    force_u256: bool = False,
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
        "--bound",
        bound,
        "--threads",
        str(threads),
        "--json-out",
        "-",
    ]
    if force_u256:
        cmd.append("--force-u256")
    res = subprocess.run(cmd, capture_output=True, text=True, check=False)
    if res.returncode not in (0, 10):
        raise RuntimeError(f"mcircuit_hunter exited with {res.returncode}:\n{res.stderr}")
    data = parse_strict_json(res.stdout)
    data["deterministic_sha256"] = canonical_sha256(data["canonical"])
    hits = data["canonical"].get("hits", [])
    if hits:
        data["lean_certs"] = _emit_certs_for_hits(hits)
    return data


def _python_simons_count_m4(k_max: int) -> tuple[int, int]:
    """Independent pure-Python canonical 4-circuit Simons-bound counter and hit checker."""
    tested = 0
    hits = 0
    for k in range(4, k_max + 1):
        p3k = 3**k
        s = p3k.bit_length()
        while (1 << s) * (3**4) < (4**4) * p3k:
            rem_l = s - k + 4
            if rem_l >= 8:
                denom = (1 << s) - p3k
                for k0 in range(1, k // 4 + 1):
                    for k1 in range(k0, k - 3 * k0 + 1):
                        for k2 in range(k0, k - 2 * k0 - k1 + 1):
                            k3 = k - k0 - k1 - k2
                            if k3 < k0:
                                continue
                            for l0 in range(2, rem_l - 5):
                                for l1 in range(2, rem_l - l0 - 3):
                                    for l2 in range(2, rem_l - l0 - l1 - 1):
                                        l3 = rem_l - l0 - l1 - l2
                                        if l3 < 2:
                                            continue
                                        b = ((k0, l0), (k1, l1), (k2, l2), (k3, l3))
                                        if (
                                            b > (b[1], b[2], b[3], b[0])
                                            or b > (b[2], b[3], b[0], b[1])
                                            or b > (b[3], b[0], b[1], b[2])
                                        ):
                                            continue
                                        tested += 1
                                        s0 = k0 - 1 + l0
                                        s01 = s0 + k1 - 1 + l1
                                        s012 = s01 + k2 - 1 + l2
                                        c = (
                                            (3 ** (k1 + k2 + k3)) * (3**k0 - (1 << k0))
                                            + (3 ** (k2 + k3)) * (1 << s0) * (3**k1 - (1 << k1))
                                            + (3**k3) * (1 << s01) * (3**k2 - (1 << k2))
                                            + (1 << s012) * (3**k3 - (1 << k3))
                                        )
                                        if c % denom == 0 and (c // denom) > 1:
                                            hits += 1
            s += 1
    return tested, hits


def _python_simons_count_m5(k_max: int) -> tuple[int, int]:
    """Independent pure-Python canonical 5-circuit Simons-bound counter and hit checker."""
    tested = 0
    hits = 0
    for k in range(5, k_max + 1):
        p3k = 3**k
        s = p3k.bit_length()
        while (1 << s) * (3**5) < (4**5) * p3k:
            rem_l = s - k + 5
            if rem_l >= 10:
                denom = (1 << s) - p3k
                for k0 in range(1, k // 5 + 1):
                    for k1 in range(k0, k - 4 * k0 + 1):
                        for k2 in range(k0, k - 3 * k0 - k1 + 1):
                            for k3 in range(k0, k - 2 * k0 - k1 - k2 + 1):
                                k4 = k - k0 - k1 - k2 - k3
                                if k4 < k0:
                                    continue
                                for l0 in range(2, rem_l - 7):
                                    for l1 in range(2, rem_l - l0 - 5):
                                        for l2 in range(2, rem_l - l0 - l1 - 3):
                                            for l3 in range(2, rem_l - l0 - l1 - l2 - 1):
                                                l4 = rem_l - l0 - l1 - l2 - l3
                                                if l4 < 2:
                                                    continue
                                                b = (
                                                    (k0, l0),
                                                    (k1, l1),
                                                    (k2, l2),
                                                    (k3, l3),
                                                    (k4, l4),
                                                )
                                                if any(b > b[r:] + b[:r] for r in range(1, 5)):
                                                    continue
                                                tested += 1
                                                s0 = k0 - 1 + l0
                                                s01 = s0 + k1 - 1 + l1
                                                s012 = s01 + k2 - 1 + l2
                                                s0123 = s012 + k3 - 1 + l3
                                                c = (
                                                    (3 ** (k1 + k2 + k3 + k4)) * (3**k0 - (1 << k0))
                                                    + (3 ** (k2 + k3 + k4))
                                                    * (1 << s0)
                                                    * (3**k1 - (1 << k1))
                                                    + (3 ** (k3 + k4))
                                                    * (1 << s01)
                                                    * (3**k2 - (1 << k2))
                                                    + (3**k4) * (1 << s012) * (3**k3 - (1 << k3))
                                                    + (1 << s0123) * (3**k4 - (1 << k4))
                                                )
                                                if c % denom == 0 and (c // denom) > 1:
                                                    hits += 1
            s += 1
    return tested, hits


def run_self_test(asan: bool = False, threads: int = 4) -> dict[str, Any]:
    """Run C11 unit tests, Python cross-checks, u128==u256 equivalence, and determinism."""
    bin_path = ensure_compiled(asan=asan)

    # 1. C11 internal self-tests
    st = subprocess.run([str(bin_path), "--self-test"], capture_output=True, text=True, check=False)
    if st.returncode != 0:
        raise RuntimeError(f"C11 --self-test failed ({st.returncode}):\n{st.stdout}\n{st.stderr}")
    print(st.stdout.strip())

    # 2. Strict RFC-8259 rejection check & Lean NontrivialCycleCert schema check
    sys.path.insert(0, str(SEARCH_DIR))
    import cycle_hunter  # type: ignore

    for bad_json in ('{"x": NaN}', '{"x": Infinity}', '{"x": -Infinity}'):
        try:
            parse_strict_json(bad_json)
            raise AssertionError(f"parse_strict_json failed to reject {bad_json}")
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
    synth_certs = _emit_certs_for_hits([{"n": "5", "k": 2, "s": 3}])
    if len(synth_certs) != 1 or "start := 5" not in synth_certs[0] or "period := 5" not in synth_certs[0]:
        raise AssertionError(f"Synthetic hit cert emission mismatch: {synth_certs}")
    print("[OK] RFC-8259 strict JSON guard & Lean NontrivialCycleCert schema verified")

    # 3. Cross-verify against search/cycle_hunter.py on 2-circuits (K <= 18) and 3-circuits (K <= 12)
    py2 = cycle_hunter.scan_2_circuits(18)
    py3 = cycle_hunter.scan_3_circuits(12)
    c_el = run_engine(
        k2_max=18, k3_max=12, k4_max=0, k5_max=0, bound="eliahou", threads=threads, asan=asan
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

    # 4. Cross-verify u256 engine vs u128 path on m=2 (K<=80), m=3 (K<=40), m=4 (K<=20)
    c_u128 = run_engine(
        k2_max=80, k3_max=40, k4_max=20, k5_max=0, bound="simons", threads=threads, asan=asan, force_u256=False
    )
    c_u256 = run_engine(
        k2_max=80, k3_max=40, k4_max=20, k5_max=0, bound="simons", threads=threads, asan=asan, force_u256=True
    )
    if c_u128["deterministic_sha256"] != c_u256["deterministic_sha256"]:
        raise AssertionError(
            f"u128 vs u256 mismatch on m=2(<=80),3(<=40),4(<=20): "
            f"{c_u128['deterministic_sha256']} != {c_u256['deterministic_sha256']}"
        )
    print(
        f"[OK] Cross-verified u256 == u128 bit-for-bit on m=2(K<=80), m=3(K<=40), m=4(K<=20): "
        f"sha256={c_u128['deterministic_sha256'][:16]}"
    )

    # 5. Cross-verify Simons m=4 (K<=10) & m=5 (K<=12) against independent pure-Python references
    py4_tested, py4_hits = _python_simons_count_m4(10)
    py5_tested, py5_hits = _python_simons_count_m5(12)
    c_m5_ref = run_engine(
        k2_max=18, k3_max=12, k4_max=10, k5_max=12, bound="simons", threads=threads, asan=asan
    )
    m5_fams = {f["m"]: f for f in c_m5_ref["canonical"]["families"]}
    if m5_fams[4]["candidates_tested"] != py4_tested or m5_fams[4]["hits_found"] != py4_hits:
        raise AssertionError(
            f"4-circuit Simons mismatch: C={m5_fams[4]} vs Py=({py4_tested}, {py4_hits})"
        )
    if m5_fams[5]["candidates_tested"] != py5_tested or m5_fams[5]["hits_found"] != py5_hits:
        raise AssertionError(
            f"5-circuit Simons mismatch: C={m5_fams[5]} vs Py=({py5_tested}, {py5_hits})"
        )
    print(
        f"[OK] Cross-verified Simons m=4 K<=10 ({py4_tested:,}) & m=5 K<=12 ({py5_tested:,}) vs Python"
    )

    # 6. High-K u256 (K=100) + multi-thread determinism check (threads=1 vs threads=N)
    c_hi_1 = run_engine(
        k2_max=100, k3_max=40, k4_max=20, k5_max=16, bound="simons", threads=1, asan=asan
    )
    c_hi_n = run_engine(
        k2_max=100, k3_max=40, k4_max=20, k5_max=16, bound="simons", threads=threads, asan=asan
    )
    if c_hi_1["canonical"]["overflow_guard_skips"] != 0:
        raise AssertionError(
            f"Unexpected overflow_guard_skips={c_hi_1['canonical']['overflow_guard_skips']}"
        )
    if c_hi_1["deterministic_sha256"] != c_hi_n["deterministic_sha256"]:
        raise AssertionError(
            f"Thread determinism failure: 1t={c_hi_1['deterministic_sha256']} != {threads}t={c_hi_n['deterministic_sha256']}"
        )
    print(
        f"[OK] u256 K=100 & thread determinism verified (1t == {threads}t, skips=0): "
        f"sha256={c_hi_n['deterministic_sha256'][:16]}"
    )
    return c_hi_n


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Compiled C11 Canonical m-Circuit Diophantine Hunter (DISPROVE-002 Phase 3)"
    )
    parser.add_argument("--self-test", action="store_true", help="Run C11 + Python cross-verification tests")
    parser.add_argument("--asan", action="store_true", help="Build & run with ASan + UBSan")
    parser.add_argument("--force-rebuild", action="store_true", help="Force gcc recompilation")
    parser.add_argument("--force-u256", action="store_true", help="Force u256 modular arithmetic for all K")
    parser.add_argument("--k2-max", type=int, default=160, help="Max K for 2-circuits")
    parser.add_argument("--k3-max", type=int, default=100, help="Max K for 3-circuits")
    parser.add_argument("--k4-max", type=int, default=60, help="Max K for 4-circuits")
    parser.add_argument("--k5-max", type=int, default=38, help="Max K for 5-circuits")
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
            bound=args.bound,
            threads=args.threads,
            asan=args.asan,
            force_u256=args.force_u256,
        )

    elapsed = time.monotonic() - t0
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(
            json.dumps(data, indent=2, allow_nan=False) + "\n", encoding="utf-8"
        )

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
