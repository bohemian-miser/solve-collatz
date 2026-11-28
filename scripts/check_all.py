#!/usr/bin/env python3
"""Run the same checks as `.github/workflows/verify.yml`, locally, in one command.

Steps, in CI order: frozen files (against `--base`, counting uncommitted changes too), source
hygiene guards, `lake build`, axiom audit, and the problem's `[search].ci_hook`. Stops at the first failure and prints the
tail of that step's output. Prints one summary line per step.

Usage:
  python3 scripts/check_all.py                  # everything, frozen check against origin/main
  python3 scripts/check_all.py --skip-search    # skip the search hook (the slow part)
  python3 scripts/check_all.py --base upstream/main
  python3 scripts/check_all.py --allow-frozen   # owner-approved change to frozen files
"""

from __future__ import annotations

import argparse
import os
import pathlib
import subprocess
import sys
import time
import tomllib

REPO_ROOT = pathlib.Path(__file__).resolve().parent.parent
TAIL_LINES = 40


def git_ok(*args: str) -> bool:
    return subprocess.run(["git", *args], cwd=REPO_ROOT, capture_output=True).returncode == 0


def steps(base: str, skip_search: bool, allow_frozen: bool) -> list[tuple[str, list[str] | None]]:
    cfg = tomllib.loads((REPO_ROOT / "problem.toml").read_text(encoding="utf-8"))
    hook = cfg.get("search", {}).get("ci_hook", "").strip()
    frozen: list[str] | None = None
    if not allow_frozen and git_ok("rev-parse", "--verify", "--quiet", base):
        merge_base = subprocess.run(
            ["git", "merge-base", base, "HEAD"], cwd=REPO_ROOT, capture_output=True, text=True
        ).stdout.strip()
        frozen = [sys.executable, __file__, "--frozen-against", merge_base]
    search = None if skip_search or not hook or not (REPO_ROOT / hook).exists() else ["bash", hook]
    return [
        (f"frozen files vs {base}", frozen),
        ("source guards", [sys.executable, "scripts/check_source_guards.py"]),
        ("lake build", ["lake", "build"]),
        ("axiom audit", [sys.executable, "scripts/audit_axioms.py"]),
        (f"search hook {hook}", search),
    ]


def check_frozen_worktree(base: str) -> int:
    """Like `check_challenge_frozen.py`, but also counts uncommitted and untracked changes."""
    sys.path.insert(0, str(REPO_ROOT / "scripts"))
    from check_challenge_frozen import load_frozen_files

    def names(*args: str) -> set[str]:
        out = subprocess.run(["git", *args], cwd=REPO_ROOT, capture_output=True, text=True, check=True)
        return {line.strip() for line in out.stdout.splitlines() if line.strip()}

    changed = names("diff", "--name-only", base) | names("ls-files", "--others", "--exclude-standard")
    violated = sorted(changed & load_frozen_files())
    if violated:
        print("FAIL: frozen file(s) changed (committed or not):", ", ".join(violated), file=sys.stderr)
        return 1
    print("PASS: frozen files untouched, including uncommitted changes.")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--frozen-against", metavar="REF", help=argparse.SUPPRESS)
    ap.add_argument("--base", default="origin/main", help="ref to compare frozen files against")
    ap.add_argument("--skip-search", action="store_true", help="skip the search CI hook")
    ap.add_argument("--allow-frozen", action="store_true", help="skip the frozen-file check")
    args = ap.parse_args()
    if args.frozen_against:
        return check_frozen_worktree(args.frozen_against)

    env = dict(os.environ)
    elan_bin = pathlib.Path.home() / ".elan" / "bin"
    env["PATH"] = f"{elan_bin}{os.pathsep}{env.get('PATH', '')}"

    failed = False
    for name, cmd in steps(args.base, args.skip_search, args.allow_frozen):
        if cmd is None:
            print(f"SKIP  {name}")
            continue
        t0 = time.monotonic()
        res = subprocess.run(cmd, cwd=REPO_ROOT, env=env, capture_output=True, text=True)
        dt = time.monotonic() - t0
        if res.returncode == 0:
            print(f"PASS  {name} ({dt:.1f}s)")
            continue
        print(f"FAIL  {name} ({dt:.1f}s): {' '.join(cmd)}")
        out = (res.stdout + res.stderr).splitlines()
        print("\n".join("      " + line for line in out[-TAIL_LINES:]))
        failed = True
        break
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
