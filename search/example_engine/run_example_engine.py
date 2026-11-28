#!/usr/bin/env python3
"""Self-test for the example engine: Python cross-check, ASan build, 1-thread == 4-thread."""

from __future__ import annotations

import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

from engine import check_thread_determinism, compile_c, run_json_engine  # noqa: E402

SOURCE = HERE / "example_engine.c"


def run(n: int, threads: int, asan: bool = False) -> dict:
    binary = compile_c("solve_anything_example_engine", SOURCE, asan=asan)
    return run_json_engine(binary, ["--n", str(n), "--threads", str(threads)])


def self_test() -> int:
    n = 100_000
    expected = sum(bin(k).count("1") for k in range(1, n + 1))
    got = run(n, 4)["canonical"]["popcount_sum"]
    if got != expected:
        print(f"FAIL: example engine popcount_sum {got} != Python {expected}", file=sys.stderr)
        return 1
    run(n, 4, asan=True)
    sha = check_thread_determinism(lambda t: run(n, t))
    print(f"PASS: example engine matches Python, ASan clean, 1t == 4t (sha256={sha[:16]})")
    return 0


if __name__ == "__main__":
    sys.exit(self_test())
