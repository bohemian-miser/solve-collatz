#!/usr/bin/env bash
set -euo pipefail

if [ -f scripts/native_cache.py ]; then
  echo "=== Upstream Native Cache Self-Test ==="
  python3 scripts/native_cache.py --self-test
fi

if [ -f scripts/build_dashboard.py ]; then
  echo "=== Dashboard Builder Self-Test ==="
  python3 scripts/build_dashboard.py --self-test
fi

echo "=== Collatz Barrier Red-Team Harness ==="
python3 search/barrier_redteam.py --verify-barriers
python3 search/barrier_redteam.py --check-stopping-bound "lambda n, k: k <= 100 * n.bit_length()" --limit 1000

echo "=== Track B Diophantine Cycle-Hunter Smoke Test ==="
python3 search/cycle_hunter.py --self-test --max-k 200

echo "=== Track B C11 Glide-Hunter Self-Test & Smoke Sweep ==="
python3 search/glide_hunter/run_glide_hunter.py --self-test --range-end 100000 --sieve-bits 18

echo "=== Track B C11 M-Circuit Hunter Self-Test ==="
python3 search/mcircuit_hunter/run_mcircuit_hunter.py --self-test
