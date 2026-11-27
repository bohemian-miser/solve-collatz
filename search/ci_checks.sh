#!/usr/bin/env bash
set -euo pipefail

echo "=== Collatz Barrier Red-Team Harness ==="
python3 search/barrier_redteam.py --verify-barriers

echo "=== Track B Diophantine Cycle-Hunter Smoke Test ==="
python3 search/cycle_hunter.py --self-test --max-k 200

echo "=== Track B C11 Glide-Hunter Self-Test & Smoke Sweep ==="
python3 search/glide_hunter/run_glide_hunter.py --self-test --range-end 100000

echo "=== Track B C11 M-Circuit Hunter Self-Test ==="
python3 search/mcircuit_hunter/run_mcircuit_hunter.py --self-test

