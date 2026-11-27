#!/usr/bin/env bash
set -euo pipefail

echo "=== Collatz Barrier Red-Team Harness ==="
python3 search/barrier_redteam.py --verify-barriers

echo "=== Track B Diophantine Cycle-Hunter Smoke Test ==="
python3 search/cycle_hunter.py --max-k 200
