#!/usr/bin/env python3
"""Pure-stdlib Python wrapper for `mcircuit_hunter.c` (Track B `DISPROVE-002 Phase 2`).

Auto-compiles `search/mcircuit_hunter/mcircuit_hunter.c` into `/tmp/solve_collatz_mcircuit_hunter`
(or `/tmp/..._asan` under `--asan`), keeping the git working tree 100% free of binaries.
Validates exact agreement against `search/cycle_hunter.py` on canonical 2- and 3-circuits,
cross-checks Simons-de Weger 4-circuits against an independent Python reference, verifies
multi-thread determinism, and enforces strict RFC-8259 JSON serialization.
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
C_SOURCE = REPO_SEARCH_DIR / "mcircuit_hunter.c"
BIN_PATH = pathlib.Path("/tmp/solve_collatz_mcircuit_hunter")
BIN_ASAN_PATH = pathlib.Path("/tmp/solve_collatz_mcircuit_hunter_asan")


def ensure_compiled(asan: bool = False, force: bool = False) -> pathlib.Path:
    """Compile `mcircuit_hunter.c` into `/tmp/` if missing or stale."""
    if not C_SOURCE.exists():
        raise FileNotFoundError(f"Missing C source: {C_SOURCE}")
    target = BIN_ASAN_PATH if asan else BIN_PATH
    src_mtime = C_SOURCE.stat().st_mtime
    if not force and target.exists() and target.stat().st_mtime >= src_mtime:
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
    # Also verify strict re-serialization with allow_nan=False succeeds.
    json.dumps(data, allow_nan=False)
    return data


def canonical_sha256(canonical_obj: dict[str, Any]) -> str:
    """Compute reproducible SHA-256 digest over the timing-free canonical payload."""
    encoded = json.dumps(
        canonical_obj, sort_keys=True, separators=(",", ":"), allow_nan=False
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def run_engine(
    k2_max: int,
    k3_max: int,
    k4_max: int,
    bound: str,
    threads: int,
    asan: bool = False,
) -> dict[str, Any]:
    """Invoke the compiled C binary and attach `deterministic_sha256`."""
    bin_path = ensure_compiled(asan=asan)
    cmd = [
        str(bin_path),
        "--k2-max",
        str(k2_max),
        "--k3-max",
        str(k3_max),
        "--k4-max",
        str(k4_max),
        "--bound",
        bound,
        "--threads",
        str(threads),
        "--json-out",
        "-",
    ]
    res = subprocess.run(cmd, capture_output=True, text=True, check=False)
    if res.returncode not in (0, 10):
        raise RuntimeError(f"mcircuit_hunter exited with {res.returncode}:\n{res.stderr}")
    data = parse_strict_json(res.stdout)
    data["deterministic_sha256"] = canonical_sha256(data["canonical"])
    return data


def _python_simons_count_m4(k_max: int) -> tuple[int, int]:
    """Independent pure-Python canonical 4-circuit Simons-bound counter and hit checker."""
    tested = 0
    hits = 0
    for k in range(4, k_max + 1):
        p3k = 3**k
        s_min = p3k.bit_length()
        s = s_min
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


def run_self_test(asan: bool = False, threads: int = 4) -> dict[str, Any]:
    """Run C11 unit tests, Python cycle_hunter cross-verification, and determinism check."""
    bin_path = ensure_compiled(asan=asan)

    # 1. C11 internal self-tests
    st = subprocess.run([str(bin_path), "--self-test"], capture_output=True, text=True, check=False)
    if st.returncode != 0:
        raise RuntimeError(f"C11 --self-test failed ({st.returncode}):\n{st.stdout}\n{st.stderr}")
    print(st.stdout.strip())

    # 2. Cross-verify against search/cycle_hunter.py on 2-circuits (K <= 18) and 3-circuits (K <= 12)
    sys.path.insert(0, str(SEARCH_DIR))
    import cycle_hunter  # type: ignore

    py2 = cycle_hunter.scan_2_circuits(18)
    py3 = cycle_hunter.scan_3_circuits(12)
    c_el = run_engine(k2_max=18, k3_max=12, k4_max=0, bound="eliahou", threads=threads, asan=asan)
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

    # 3. Cross-verify Simons 4-circuit counter & hits against independent Python reference (K <= 10)
    py4_tested, py4_hits = _python_simons_count_m4(10)
    c_sim_1 = run_engine(k2_max=18, k3_max=12, k4_max=10, bound="simons", threads=1, asan=asan)
    c_sim_n = run_engine(k2_max=18, k3_max=12, k4_max=10, bound="simons", threads=threads, asan=asan)
    sim_fams = {f["m"]: f for f in c_sim_1["canonical"]["families"]}
    if sim_fams[4]["candidates_tested"] != py4_tested or sim_fams[4]["hits_found"] != py4_hits:
        raise AssertionError(
            f"4-circuit Simons mismatch: C={sim_fams[4]} vs Py=({py4_tested}, {py4_hits})"
        )
    print(f"[OK] Cross-verified 4-circuit Simons K<=10 ({py4_tested} candidates)")

    # 4. Multi-thread determinism check (threads=1 vs threads=N)
    if c_sim_1["deterministic_sha256"] != c_sim_n["deterministic_sha256"]:
        raise AssertionError(
            f"Thread determinism failure: 1t={c_sim_1['deterministic_sha256']} != {threads}t={c_sim_n['deterministic_sha256']}"
        )
    print(f"[OK] Determinism verified (threads=1 vs threads={threads}): sha256={c_sim_1['deterministic_sha256'][:16]}")
    return c_sim_n


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Compiled C11 Canonical m-Circuit Diophantine Hunter (DISPROVE-002 Phase 2)"
    )
    parser.add_argument("--self-test", action="store_true", help="Run C11 + Python cross-verification tests")
    parser.add_argument("--asan", action="store_true", help="Build & run with ASan + UBSan")
    parser.add_argument("--force-rebuild", action="store_true", help="Force gcc recompilation")
    parser.add_argument("--k2-max", type=int, default=80, help="Max K for 2-circuits")
    parser.add_argument("--k3-max", type=int, default=79, help="Max K for 3-circuits")
    parser.add_argument("--k4-max", type=int, default=58, help="Max K for 4-circuits")
    parser.add_argument("--bound", choices=("simons", "eliahou"), default="simons", help="Upper S bound")
    parser.add_argument("--threads", type=int, default=8, help="Worker thread count (1..64)")
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
            bound=args.bound,
            threads=args.threads,
            asan=args.asan,
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
    return 10 if canon["total_hits"] > 0 else 0


if __name__ == "__main__":
    sys.exit(main())
