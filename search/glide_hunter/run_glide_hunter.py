#!/usr/bin/env python3
"""Pure-stdlib Python wrapper for `glide_hunter.c` (Track B `DISPROVE-003`).

Auto-compiles `search/glide_hunter/glide_hunter.c` into `/tmp/solve_collatz_glide_hunter`
(keeping the git working tree 100% free of build artifacts), validates classic Collatz
stopping-time & glide records in `--self-test` mode, and emits deterministic SHA-256-hashed
JSON sweep summaries.
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
C_SOURCE = REPO_SEARCH_DIR / "glide_hunter.c"
BIN_PATH = pathlib.Path("/tmp/solve_collatz_glide_hunter")


def ensure_compiled(force: bool = False) -> pathlib.Path:
    """Compile `glide_hunter.c` into `/tmp/` if missing or stale."""
    if not C_SOURCE.exists():
        raise FileNotFoundError(f"Missing C source: {C_SOURCE}")
    src_mtime = C_SOURCE.stat().st_mtime
    if not force and BIN_PATH.exists() and BIN_PATH.stat().st_mtime >= src_mtime:
        return BIN_PATH

    tmp_bin = pathlib.Path(f"/tmp/solve_collatz_glide_hunter.{os.getpid()}")
    cmd = [
        "gcc",
        "-O3",
        "-Wall",
        "-Wextra",
        "-Werror",
        "-std=c11",
        "-pthread",
        str(C_SOURCE),
        "-lm",
        "-o",
        str(tmp_bin),
    ]
    res = subprocess.run(cmd, capture_output=True, text=True, check=False)
    if res.returncode != 0:
        if tmp_bin.exists():
            tmp_bin.unlink()
        raise RuntimeError(f"gcc failed ({res.returncode}):\n{res.stderr}")
    os.replace(tmp_bin, BIN_PATH)
    return BIN_PATH


def canonical_sha256(canonical_obj: dict[str, Any]) -> str:
    """Compute reproducible SHA-256 digest over the timing-free canonical payload."""
    encoded = json.dumps(canonical_obj, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def run_engine(
    range_end: int | None,
    mersenne_max: int | None,
    threads: int | None = None,
) -> dict[str, Any]:
    """Invoke the compiled C binary and attach `deterministic_sha256`."""
    bin_path = ensure_compiled()
    cmd = [str(bin_path)]
    if range_end is not None and range_end > 0:
        cmd.extend(["--range-end", str(range_end)])
    if mersenne_max is not None and mersenne_max > 0:
        cmd.extend(["--mersenne-max", str(mersenne_max)])
    if threads is not None:
        cmd.extend(["--threads", str(threads)])

    res = subprocess.run(cmd, capture_output=True, text=True, check=False)
    if res.returncode != 0:
        raise RuntimeError(f"glide_hunter exited with {res.returncode}:\n{res.stderr}")
    data = json.loads(res.stdout)
    data["deterministic_sha256"] = canonical_sha256(data["canonical"])
    return data


def python_orbit_stats(n: int) -> tuple[int, int, int]:
    """Independent pure-Python reference `(stopping_time, total_steps, peak)`."""
    if n == 1:
        return (0, 0, 1)
    cur = n
    steps = 0
    stop = None
    peak = n
    while cur != 1:
        cur = cur // 2 if cur % 2 == 0 else 3 * cur + 1
        steps += 1
        if cur > peak:
            peak = cur
        if stop is None and cur < n:
            stop = steps
    assert stop is not None
    return (stop, steps, peak)


def run_self_test(range_end: int) -> dict[str, Any]:
    """Verify classic Collatz records, Mersenne big-int fallback, and determinism."""
    test_range = max(range_end, 100_000)
    data = run_engine(range_end=test_range, mersenne_max=700)
    canon = data["canonical"]
    if canon["overflow_count"] != 0:
        raise AssertionError(f"Unexpected overflow_count={canon['overflow_count']}")

    m1 = canon["mode1_range"]
    if not m1["all_converged"] or m1["verified_count"] != test_range:
        raise AssertionError("Mode 1 failed full convergence verification")

    by_total = {r["n"]: r for r in m1["total_stopping_time_records"]}
    by_stop = {r["n"]: r for r in m1["stopping_time_records"]}
    by_peak = {r["n"]: r for r in m1["peak_ratio_records"]}

    # Classic literature & user-specified anchor checks
    expected_total = {
        27: (96, 111, "9232"),
        703: (132, 170, "250504"),
        77031: (145, 350, "21933016"),
    }
    for n, (exp_stop, exp_tot, exp_peak) in expected_total.items():
        if n not in by_total:
            raise AssertionError(f"Missing total stopping time record n={n}")
        rec = by_total[n]
        if (rec["stopping_time"], rec["total_steps"], rec["peak"]) != (exp_stop, exp_tot, exp_peak):
            raise AssertionError(f"Mismatch at n={n}: got {rec}")

    if 35655 not in by_stop or by_stop[35655]["stopping_time"] != 220:
        raise AssertionError("Missing or mismatched stopping-time record n=35655 -> 220")

    expected_peak = {
        27: (96, 111, "9232"),
        703: (132, 170, "250504"),
        9663: (88, 184, "27114424"),
        77671: (171, 231, "1570824736"),
    }
    for n, (exp_stop, exp_tot, exp_peak) in expected_peak.items():
        if n not in by_peak:
            raise AssertionError(f"Missing peak-ratio record n={n}")
        rec = by_peak[n]
        if (rec["stopping_time"], rec["total_steps"], rec["peak"]) != (exp_stop, exp_tot, exp_peak):
            raise AssertionError(f"Peak record mismatch at n={n}: got {rec}")

    # Cross-check against pure Python orbit simulator
    for n in (27, 703, 9663, 35655, 77031, 77671):
        py_stop, py_tot, py_peak = python_orbit_stats(n)
        rec = by_peak.get(n) or by_total.get(n) or by_stop.get(n)
        assert rec is not None
        if (rec["stopping_time"], rec["total_steps"], int(rec["peak"])) != (py_stop, py_tot, py_peak):
            raise AssertionError(f"Python cross-check failed for n={n}")

    # Mode 2 Mersenne & structured high-glide checks (including __uint128_t -> bigint fallback & k=700 overflow test)
    m2 = canon["mode2_mersenne"]
    if not m2["all_converged"] or m2["tested_count"] != 2100:  # 700 * 3 families
        raise AssertionError(f"Mode 2 check failed: {m2}")
    if canon["u128_bigint_fallbacks"] == 0:
        raise AssertionError("Expected u128->bigint fallback to exercise at k <= 700")

    # Validate strict RFC-8259 JSON serialization and parsing (reject NaN/Infinity)
    raw_json_str = json.dumps(data, allow_nan=False)

    def _reject_constant(val: str) -> None:
        raise ValueError(f"Non-standard JSON constant: {val}")

    json.loads(raw_json_str, parse_constant=_reject_constant)

    # Determinism check on 10k slice
    d1 = run_engine(range_end=10_000, mersenne_max=60)["deterministic_sha256"]
    d2 = run_engine(range_end=10_000, mersenne_max=60)["deterministic_sha256"]
    if d1 != d2:
        raise AssertionError(f"Non-deterministic canonical digest: {d1} != {d2}")

    return data


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Compiled C11 Collatz Stopping-Time & Extreme-Glide Hunter"
    )
    parser.add_argument("--self-test", action="store_true", help="Run record & determinism checks")
    parser.add_argument("--range-end", type=int, default=100_000, help="Mode 1 upper seed bound N")
    parser.add_argument(
        "--mersenne-max",
        type=int,
        default=100,
        help="Mode 2 max exponent K for 2^k-1, 3*2^k-1, 27*2^k-1",
    )
    parser.add_argument("--threads", type=int, default=None, help="Worker thread count (1..64)")
    parser.add_argument("--log-json", type=pathlib.Path, help="Write full JSON sweep log to path")
    parser.add_argument("--force-rebuild", action="store_true", help="Force gcc recompilation")
    args = parser.parse_args()

    t0 = time.monotonic()
    ensure_compiled(force=args.force_rebuild)

    if args.self_test:
        data = run_self_test(args.range_end)
    else:
        data = run_engine(
            range_end=args.range_end if args.range_end > 0 else None,
            mersenne_max=args.mersenne_max if args.mersenne_max > 0 else None,
            threads=args.threads,
        )

    elapsed = time.monotonic() - t0
    if args.log_json:
        args.log_json.parent.mkdir(parents=True, exist_ok=True)
        args.log_json.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")

    canon = data["canonical"]
    telem = data.get("telemetry", {})
    parts = [f"overflows={canon['overflow_count']}"]
    if "mode1_range" in canon:
        m1 = canon["mode1_range"]
        rate = telem.get("mode1_seeds_per_sec", 0.0)
        top_stop = m1["stopping_time_records"][-1]
        top_tot = m1["total_stopping_time_records"][-1]
        top_peak = m1["peak_ratio_records"][-1]
        parts.append(
            f"range=1..{m1['range_end']:,} ({rate:,.0f} seeds/s, "
            f"max_stop={top_stop['stopping_time']}@{top_stop['n']}, "
            f"max_total={top_tot['total_steps']}@{top_tot['n']}, "
            f"max_glide={top_peak['peak_ratio']:.2f}x@{top_peak['n']})"
        )
    if "mode2_mersenne" in canon:
        m2 = canon["mode2_mersenne"]
        parts.append(
            f"mersenne=1..{m2['mersenne_max_k']} ({m2['tested_count']} seeds, "
            f"bigint_fallbacks={canon['u128_bigint_fallbacks']})"
        )
    parts.append(f"sha256={data['deterministic_sha256'][:16]}")
    parts.append(f"wall={elapsed:.3f}s")
    print(f"[{'PASS' if args.self_test else 'CLEAN'}] " + " | ".join(parts))
    return 0


if __name__ == "__main__":
    sys.exit(main())
