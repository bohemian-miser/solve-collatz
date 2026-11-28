#!/usr/bin/env python3
"""Pure-stdlib Python wrapper for `glide_hunter.c` (Track B `DISPROVE-003` Phase 4).

Auto-compiles `search/glide_hunter/glide_hunter.c` into content-hashed
`/tmp/solve_collatz_glide_hunter_<sha12>[_asan]` via `scripts/native_cache.py`,
keeping the git working tree 100% free of build artifacts. Enforces strict RFC-8259
JSON serialization, independently cross-verifies every reported Mode 1 record seed
and Mode 2 sample in pure Python `int` arithmetic, validates sieve equivalence across
`--sieve-bits 0|16|18|20`, and emits deterministic SHA-256-hashed JSON sweep summaries.
"""

from __future__ import annotations

import argparse
import pathlib
import re
import subprocess
import sys
import time
from typing import Any


REPO_SEARCH_DIR = pathlib.Path(__file__).resolve().parent
REPO_ROOT = REPO_SEARCH_DIR.parent.parent
SCRIPTS_DIR = REPO_ROOT / "scripts"
for _p in (str(SCRIPTS_DIR), str(REPO_SEARCH_DIR.parent)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from engine import check_thread_determinism, compile_c, run_json_engine  # type: ignore  # noqa: E402
from native_cache import (  # type: ignore  # noqa: E402
    canonical_sha256,
    dump_strict_json,
    loads_strict_json,
)

C_SOURCE = REPO_SEARCH_DIR / "glide_hunter.c"


def ensure_compiled(asan: bool = False, force: bool = False) -> pathlib.Path:
    """Compile `glide_hunter.c` into a content-hashed `/tmp` binary via `search/engine.py`."""
    return compile_c("solve_collatz_glide_hunter", C_SOURCE, asan=asan, force=force)


def python_orbit_stats(n: int) -> tuple[int, int, int]:
    """Independent pure-Python reference `(stopping_time, total_steps, peak)`."""
    if n == 1:
        return (0, 0, 1)
    cur = n
    steps = 0
    stop = None
    peak = n
    while cur != 1:
        if (cur & 1) == 0:
            tz = (cur & -cur).bit_length() - 1
            nxt = cur >> tz
            if stop is None and nxt < n:
                j = 1
                tmp = cur >> 1
                while j < tz and tmp >= n:
                    tmp >>= 1
                    j += 1
                stop = steps + j
            cur = nxt
            steps += tz
        else:
            nxt = 3 * cur + 1
            if nxt > peak:
                peak = nxt
            tz = (nxt & -nxt).bit_length() - 1
            reduced = nxt >> tz
            if stop is None and reduced < n:
                j = 1
                tmp = nxt >> 1
                while j < tz and tmp >= n:
                    tmp >>= 1
                    j += 1
                stop = steps + 1 + j
            cur = reduced
            steps += 1 + tz
    assert stop is not None
    return (stop, steps, peak)


def verify_mode1_records_python(m1: dict[str, Any]) -> int:
    """Independently cross-check EVERY Mode 1 record seed in pure Python `int` arithmetic."""
    checked_seeds: dict[int, tuple[int, int, int]] = {}
    lists = (
        ("stopping_time_records", "stopping_time"),
        ("total_stopping_time_records", "total_steps"),
        ("peak_ratio_records", "peak_ratio"),
    )
    for key, metric in lists:
        recs = m1[key]
        prev_val: int | None = None
        prev_peak: tuple[int, int] | None = None
        for rec in recs:
            n = int(rec["n"])
            if n not in checked_seeds:
                checked_seeds[n] = python_orbit_stats(n)
            py_stop, py_tot, py_peak = checked_seeds[n]
            if (int(rec["stopping_time"]), int(rec["total_steps"]), int(rec["peak"])) != (
                py_stop,
                py_tot,
                py_peak,
            ):
                raise AssertionError(
                    f"Python cross-check mismatch in {key} at n={n}: "
                    f"C={(rec['stopping_time'], rec['total_steps'], rec['peak'])} vs "
                    f"Py={(py_stop, py_tot, py_peak)}"
                )
            if metric == "stopping_time":
                if prev_val is not None and py_stop <= prev_val:
                    raise AssertionError(f"Non-monotonic stopping_time at n={n}")
                prev_val = py_stop
            elif metric == "total_steps":
                if prev_val is not None and py_tot <= prev_val:
                    raise AssertionError(f"Non-monotonic total_steps at n={n}")
                prev_val = py_tot
            else:
                if prev_peak is not None and py_peak * prev_peak[1] <= prev_peak[0] * n:
                    raise AssertionError(f"Non-monotonic peak_ratio at n={n}")
                prev_peak = (py_peak, n)
    return len(checked_seeds)


def _seed_from_family(family: str, k: int) -> int:
    m = re.fullmatch(r"(?:(\d+)\*)?2\^k([+-]\d+)", family)
    if not m:
        raise ValueError(f"Unsupported Mode 2 family string: {family}")
    mult = int(m.group(1)) if m.group(1) else 1
    offset = int(m.group(2))
    return (mult << k) + offset


def verify_mode2_samples_python(m2: dict[str, Any]) -> int:
    """Independently verify Mode 2 sample orbits in pure Python `int` arithmetic."""
    samples = m2.get("samples", [])
    for s in samples:
        seed = _seed_from_family(s["family"], int(s["k"]))
        py_stop, py_tot, py_peak = python_orbit_stats(seed)
        if (
            seed.bit_length() != int(s["seed_bits"])
            or py_stop != int(s["stopping_time"])
            or py_tot != int(s["total_steps"])
            or py_peak.bit_length() != int(s["peak_bits"])
        ):
            raise AssertionError(
                f"Mode 2 Python cross-check failed for {s['family']} k={s['k']}: "
                f"C={(s['seed_bits'], s['stopping_time'], s['total_steps'], s['peak_bits'])} vs "
                f"Py={(seed.bit_length(), py_stop, py_tot, py_peak.bit_length())}"
            )
    return len(samples)


def run_engine(
    range_end: int | None,
    mersenne_max: int | None,
    threads: int | None = None,
    sieve_bits: int | None = None,
    max_steps: int | None = None,
    asan: bool = False,
    verify_python: bool = True,
) -> dict[str, Any]:
    """Invoke the compiled C binary, verify records in Python, and attach `deterministic_sha256`."""
    bin_path = ensure_compiled(asan=asan)
    cmd = [str(bin_path)]
    if range_end is not None and range_end > 0:
        cmd.extend(["--range-end", str(range_end)])
    if mersenne_max is not None and mersenne_max > 0:
        cmd.extend(["--mersenne-max", str(mersenne_max)])
    if threads is not None:
        cmd.extend(["--threads", str(threads)])
    if sieve_bits is not None:
        cmd.extend(["--sieve-bits", str(sieve_bits)])
    if max_steps is not None:
        cmd.extend(["--max-steps", str(max_steps)])

    data = run_json_engine(bin_path, cmd[1:])
    canon = data["canonical"]
    if verify_python:
        if "mode1_range" in canon:
            verify_mode1_records_python(canon["mode1_range"])
        if "mode2_mersenne" in canon:
            verify_mode2_samples_python(canon["mode2_mersenne"])
    return data


def run_self_test(range_end: int, sieve_bits: int, asan: bool = False) -> dict[str, Any]:
    """Verify classic Collatz records, sieve equivalence, thread determinism, and budget guard."""
    test_range = max(range_end, 100_000)
    data = run_engine(
        range_end=test_range,
        mersenne_max=700,
        sieve_bits=sieve_bits,
        asan=asan,
        verify_python=True,
    )
    canon = data["canonical"]
    if canon["overflow_count"] != 0:
        raise AssertionError(f"Unexpected overflow_count={canon['overflow_count']}")

    m1 = canon["mode1_range"]
    if not m1["all_converged"] or m1["verified_count"] != test_range:
        raise AssertionError("Mode 1 failed full convergence verification")

    by_total = {r["n"]: r for r in m1["total_stopping_time_records"]}
    by_stop = {r["n"]: r for r in m1["stopping_time_records"]}
    by_peak = {r["n"]: r for r in m1["peak_ratio_records"]}

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

    # Mode 2 Mersenne, extended, & Terras/Roosendaal high-glide checks (11*700 + 699 = 8,399 seeds)
    m2 = canon["mode2_mersenne"]
    if not m2["all_converged"] or m2["tested_count"] != 8399:
        raise AssertionError(f"Mode 2 check failed: {m2}")
    if canon["u128_bigint_fallbacks"] == 0:
        raise AssertionError("Expected u128->bigint fallback to exercise at k <= 700")

    # Sieve equivalence proof on 1..1,200,000 (> 2^20): 0 vs 16 vs 18 vs 20 vs 22 vs 24
    equiv_ref = None
    for sb in (0, 16, 18, 20, 22, 24):
        sub = run_engine(
            range_end=1_200_000,
            mersenne_max=None,
            sieve_bits=sb,
            asan=asan,
            verify_python=True,
        )["canonical"]["mode1_range"]
        sig = (
            sub["verified_count"],
            sub["all_converged"],
            sub["stopping_time_records"],
            sub["total_stopping_time_records"],
            sub["peak_ratio_records"],
        )
        if equiv_ref is None:
            equiv_ref = sig
        elif sig != equiv_ref:
            raise AssertionError(f"Sieve equivalence failed for --sieve-bits {sb}")

    # Multi-thread determinism proof crossing SEQ_CUTOFF (1..1,500,000)
    d1 = check_thread_determinism(
        lambda t: run_engine(
            range_end=1_500_000, mersenne_max=60, threads=t, sieve_bits=sieve_bits, asan=asan
        )
    )

    # Explicit budget diagnostic check (zero silent truncation on --max-steps 20 for n=27)
    bin_path = ensure_compiled(asan=asan)
    budget_res = subprocess.run(
        [str(bin_path), "--range-end", "30", "--max-steps", "20", "--sieve-bits", "0"],
        capture_output=True,
        text=True,
        check=False,
    )
    if budget_res.returncode != 10:
        raise AssertionError(f"Expected exit code 10 on budget exhaustion, got {budget_res.returncode}")
    diag_json = loads_strict_json(budget_res.stdout)["canonical"].get("failure_diagnostic", {})
    if diag_json.get("kind") != "step_budget_exceeded" or diag_json.get("seed") != "27":
        raise AssertionError(f"Unexpected failure_diagnostic payload: {diag_json}")

    # Regression check on committed REF-012 10^10 + k<=2000 JSON artifact
    ref012_log = REPO_ROOT / "search" / "logs" / "glide_sweep_1e10_ref012.json"
    if ref012_log.exists():
        log_data = loads_strict_json(ref012_log.read_text(encoding="utf-8"))
        log_canon = log_data["canonical"]
        if canonical_sha256(log_canon) != log_data.get("deterministic_sha256"):
            raise AssertionError("REF-012 JSON artifact deterministic_sha256 mismatch")
        if (
            log_canon.get("overflow_count") != 0
            or log_canon.get("mode1_range", {}).get("verified_count") != 10_000_000_000
            or not log_canon.get("mode1_range", {}).get("all_converged")
            or log_canon.get("mode2_mersenne", {}).get("tested_count") != 23999
            or not log_canon.get("mode2_mersenne", {}).get("all_converged")
        ):
            raise AssertionError("REF-012 JSON artifact failed integrity assertions")

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
        help="Mode 2 max exponent K for Mersenne & Terras/Roosendaal lifts",
    )
    parser.add_argument(
        "--sieve-bits",
        type=int,
        choices=(0, 16, 18, 20, 22, 24),
        default=24,
        help="Affine pre-drop sieve modulus bits (0=off, 16, 18, 20, 22, or 24; default 24)",
    )
    parser.add_argument("--max-steps", type=int, default=None, help="Explicit step budget per seed")
    parser.add_argument("--threads", type=int, default=None, help="Worker thread count (1..64)")
    parser.add_argument("--asan", action="store_true", help="Compile/run with ASan+UBSan")
    parser.add_argument("--log-json", type=pathlib.Path, help="Write full JSON sweep log to path")
    parser.add_argument("--force-rebuild", action="store_true", help="Force gcc recompilation")
    args = parser.parse_args()

    t0 = time.monotonic()
    ensure_compiled(asan=args.asan, force=args.force_rebuild)

    if args.self_test:
        data = run_self_test(args.range_end, args.sieve_bits, asan=args.asan)
    else:
        data = run_engine(
            range_end=args.range_end if args.range_end > 0 else None,
            mersenne_max=args.mersenne_max if args.mersenne_max > 0 else None,
            threads=args.threads,
            sieve_bits=args.sieve_bits,
            max_steps=args.max_steps,
            asan=args.asan,
            verify_python=True,
        )

    elapsed = time.monotonic() - t0
    if args.log_json:
        dump_strict_json(data, args.log_json)

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
            f"range=1..{m1['range_end']:,} [sieve=2^{m1['sieve_bits']}] ({rate:,.0f} seeds/s, "
            f"max_stop={top_stop['stopping_time']}@{top_stop['n']}, "
            f"max_total={top_tot['total_steps']}@{top_tot['n']}, "
            f"max_glide={top_peak['peak_ratio']:.2f}x@{top_peak['n']})"
        )
    if "mode2_mersenne" in canon:
        m2 = canon["mode2_mersenne"]
        parts.append(
            f"structured=1..{m2['mersenne_max_k']} ({m2['tested_count']} seeds, "
            f"bigint_fallbacks={canon['u128_bigint_fallbacks']})"
        )
    parts.append(f"sha256={data['deterministic_sha256'][:16]}")
    parts.append(f"wall={elapsed:.3f}s")
    print(f"[{'PASS' if args.self_test else 'CLEAN'}] " + " | ".join(parts))
    return 0


if __name__ == "__main__":
    sys.exit(main())
