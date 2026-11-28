#!/usr/bin/env python3
"""Audit the axioms of every declaration in the problem's Lean library.

Reads `lean_root` from `problem.toml`, imports it together with `Challenge`, and runs
`collectAxioms` on every non-internal constant those modules define. Anything outside
`propext`, `Classical.choice` and `Quot.sound` fails the audit. That catches `sorryAx` and
`native_decide` (`Lean.ofReduceBool` on older toolchains, a generated `*._native.*` axiom on
newer ones). No hand-kept list of theorems: a new file is
audited as soon as it is imported by the library root.

Usage:
  python3 scripts/audit_axioms.py              # audit, print offenders, exit 1 on any
  python3 scripts/audit_axioms.py --json       # one JSON object per constant on stdout
  python3 scripts/audit_axioms.py --self-test  # check the audit catches sorry/native_decide
"""

from __future__ import annotations

import argparse
import json
import pathlib
import shutil
import subprocess
import sys
import tempfile
import tomllib

REPO_ROOT = pathlib.Path(__file__).resolve().parent.parent
ALLOWED = frozenset({"propext", "Classical.choice", "Quot.sound"})

# `{imports}` and `{roots}` are filled in; `{extra}` is Lean source appended for the self-test.
LEAN_TEMPLATE = """import Lean
{imports}
open Lean Elab Command

{extra}

#eval show CommandElabM Unit from do
  let env ← getEnv
  let roots : Array Name := #[{roots}]
  let emit (mod c : Name) : CommandElabM Unit := do
    let axs ← liftCoreM (collectAxioms c)
    let axStr := ",".intercalate (axs.toList.map fun a => "\\"" ++ a.toString ++ "\\"")
    IO.println ("AXIOMS " ++ "{{\\"module\\":\\"" ++ mod.toString ++ "\\",\\"decl\\":\\""
      ++ c.toString ++ "\\",\\"axioms\\":[" ++ axStr ++ "]}}")
  for mod in env.header.moduleNames, md in env.header.moduleData do
    unless roots.any (·.isPrefixOf mod) do continue
    for c in md.constNames do
      unless c.isInternalDetail do emit mod c
  for (c, _) in env.constants.map₂.toList do
    unless c.isInternalDetail do emit `_local c
"""


def lean_name(dotted: str) -> str:
    return "`" + dotted


def build_script(lean_root: str, extra: str = "") -> str:
    return LEAN_TEMPLATE.format(
        imports=f"import Challenge\nimport {lean_root}",
        roots=", ".join(lean_name(r) for r in (lean_root, "Challenge")),
        extra=extra,
    )


def run_audit(lean_root: str, extra: str = "") -> list[dict]:
    lake = shutil.which("lake") or str(pathlib.Path.home() / ".elan" / "bin" / "lake")
    with tempfile.TemporaryDirectory() as tmp:
        script = pathlib.Path(tmp) / "AuditAxioms.lean"
        script.write_text(build_script(lean_root, extra), encoding="utf-8")
        res = subprocess.run(
            [lake, "env", "lean", str(script)],
            cwd=REPO_ROOT, capture_output=True, text=True, check=False,
        )
    rows, errors = [], []
    for line in res.stdout.splitlines():
        if line.startswith("AXIOMS "):
            rows.append(json.loads(line[len("AXIOMS "):]))
        elif "error" in line:
            errors.append(line)
    if res.returncode != 0 or errors:
        raise RuntimeError("Lean audit script failed:\n" + "\n".join(errors) + res.stderr)
    return rows


def offenders(rows: list[dict]) -> list[dict]:
    return [r for r in rows if set(r["axioms"]) - ALLOWED]


def self_test(lean_root: str) -> int:
    planted = (
        "theorem auditPlantedNative : 2 + 2 = 4 := by native_decide\n"
        "set_option warningAsError false in\n"
        "theorem auditPlantedSorry : 1 = 2 := sorry\n"
    )
    rows = run_audit(lean_root, planted)
    bad = {r["decl"]: r["axioms"] for r in offenders(rows)}
    library = [r for r in rows if r["module"] != "_local"]
    ok = (
        "auditPlantedNative" in bad
        and "sorryAx" in bad.get("auditPlantedSorry", [])
        and len(library) > 0
    )
    if not ok:
        print(f"FAIL: audit self-test did not catch planted axioms: {bad}", file=sys.stderr)
        return 1
    print(f"PASS: audit self-test caught planted sorry/native_decide ({len(library)} library decls).")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--json", action="store_true", help="print one JSON row per constant")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()

    cfg = tomllib.loads((REPO_ROOT / "problem.toml").read_text(encoding="utf-8"))
    lean_root = cfg["problem"]["lean_root"]
    if args.self_test:
        return self_test(lean_root)

    rows = run_audit(lean_root)
    if args.json:
        for r in rows:
            print(json.dumps(r))
    bad = offenders(rows)
    for r in bad:
        extra = sorted(set(r["axioms"]) - ALLOWED)
        print(f"FAIL: {r['decl']} ({r['module']}) depends on {extra}", file=sys.stderr)
    if bad:
        return 1
    if not args.json:
        print(f"PASS: {len(rows)} declarations under {lean_root}/ and Challenge use standard axioms only.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
