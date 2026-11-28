#!/usr/bin/env python3
"""Hard CI guard: ensure frozen human-owned files declared in `problem.toml` are unmodified."""

from __future__ import annotations

import pathlib
import subprocess
import sys
import tomllib

DEFAULT_FROZEN = {
    "Challenge.lean",
    "problem.toml",
    "lean-toolchain",
    "scripts/audit_axioms.py",
    "scripts/check_challenge_frozen.py",
    "scripts/check_source_guards.py",
    ".github/workflows/verify.yml",
    ".github/workflows/claims.yml",
    ".github/workflows/dashboard.yml",
    ".github/workflows/label-pr.yml",
}


def load_frozen_files() -> set[str]:
    cfg_path = pathlib.Path("problem.toml")
    if cfg_path.exists():
        cfg = tomllib.loads(cfg_path.read_text(encoding="utf-8"))
        extra = set(cfg.get("guards", {}).get("frozen_files", []))
        return DEFAULT_FROZEN | extra
    return DEFAULT_FROZEN


def main() -> int:
    if len(sys.argv) != 3:
        print("Usage: check_challenge_frozen.py <base_ref> <head_ref>", file=sys.stderr)
        return 2
    base, head = sys.argv[1], sys.argv[2]
    res = subprocess.run(
        ["git", "diff", "--name-only", base, head],
        capture_output=True,
        text=True,
        check=True,
    )
    changed = {line.strip() for line in res.stdout.splitlines() if line.strip()}
    violated = sorted(changed & load_frozen_files())
    if violated:
        print("FAIL: Frozen human-owned file(s) modified:", ", ".join(violated), file=sys.stderr)
        return 1
    print("PASS: All frozen challenge & verification files untouched.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
