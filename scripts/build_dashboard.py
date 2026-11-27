#!/usr/bin/env python3
"""Build static GitHub Pages Frontier Dashboard + machine-readable `frontier.json`.

Reads all problem metadata dynamically from `problem.toml` and `GITHUB_REPOSITORY`,
so downstream theorem repos inherit dashboard upgrades cleanly via `git merge upstream/main`.
"""

from __future__ import annotations

import argparse
import datetime as dt
import html
import json
import os
import pathlib
import re
import tempfile
import tomllib


LEAN_DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*|(?:public|private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(?:theorem|lemma)\s+([^\s:({[]+)"
)


def load_problem_meta(root_dir: pathlib.Path = pathlib.Path(".")) -> dict[str, str]:
    cfg_path = root_dir / "problem.toml"
    cfg = tomllib.loads(cfg_path.read_text(encoding="utf-8")) if cfg_path.exists() else {}
    prob = cfg.get("problem", {})
    repo = (
        os.environ.get("GITHUB_REPOSITORY")
        or prob.get("repo")
        or f"bohemian-miser/{prob.get('name', 'solve-anything')}"
    )
    return {
        "name": prob.get("name", "solve-anything"),
        "title": prob.get("title", "Theorem Swarm Frontier"),
        "tagline": prob.get(
            "tagline",
            "Lean 4 kernel-verified dual-track crowd-swarm (Track A: Prove · Track B: Disprove)",
        ),
        "lean_root": prob.get("lean_root", "Problem"),
        "challenge_file": prob.get("challenge_file", "Challenge.lean"),
        "repo": repo,
    }


def _strip_lean_comments(lines: list[str]) -> list[tuple[int, str]]:
    """Strip `--` line comments, nested `/- ... -/` block comments, and `"..."` string literals."""
    stripped_lines: list[tuple[int, str]] = []
    comment_depth = 0
    in_string = False
    for lineno, line in enumerate(lines, 1):
        out: list[str] = []
        i = 0
        n = len(line)
        while i < n:
            if in_string:
                if line[i] == "\\":
                    if i + 1 < n:
                        out.append("  ")
                        i += 2
                    else:
                        out.append(" ")
                        i += 1
                    continue
                if line[i] == '"':
                    in_string = False
                    out.append('"')
                    i += 1
                    continue
                out.append(" ")
                i += 1
                continue

            if comment_depth == 0 and line[i] == '"':
                in_string = True
                out.append('"')
                i += 1
                continue
            if comment_depth == 0 and line[i : i + 2] == "--":
                break
            if line[i : i + 2] == "/-":
                comment_depth += 1
                i += 2
                continue
            if comment_depth > 0 and line[i : i + 2] == "-/":
                comment_depth -= 1
                i += 2
                continue
            if comment_depth == 0:
                out.append(line[i])
            i += 1
        code = "".join(out).strip()
        if code:
            stripped_lines.append((lineno, code))
    return stripped_lines


def collect_lean_stats(
    lean_root: pathlib.Path,
    root_dir: pathlib.Path = pathlib.Path("."),
    challenge_file: str = "Challenge.lean",
) -> tuple[list[dict[str, str]], int, int]:
    """Count Lean source files, total LOC, and `theorem`/`lemma` declarations outside `Challenge.lean`."""
    if not lean_root.exists():
        return [], 0, 0

    root_resolved = root_dir.resolve()
    challenge_resolved = (root_dir / challenge_file).resolve()
    scripts_resolved = (root_dir / "scripts").resolve()

    decls: list[dict[str, str]] = []
    lean_files = 0
    lean_loc = 0
    for path in sorted(lean_root.rglob("*.lean")):
        resolved = path.resolve()
        try:
            rel_parts = resolved.relative_to(root_resolved).parts
        except ValueError:
            rel_parts = path.relative_to(lean_root).parts
        if ".lake" in rel_parts:
            continue
        if resolved == challenge_resolved or scripts_resolved in resolved.parents:
            continue
        lean_files += 1
        lines = path.read_text(encoding="utf-8").splitlines()
        lean_loc += len(lines)
        try:
            rel = resolved.relative_to(root_resolved).as_posix()
        except ValueError:
            rel = path.as_posix()
        for lineno, code in _strip_lean_comments(lines):
            m = LEAN_DECL_RE.match(code)
            if m:
                decls.append({"file": rel, "line": str(lineno), "name": m.group(1)})
    return decls, lean_files, lean_loc


def count_lean_theorems(root: pathlib.Path) -> list[dict[str, str]]:
    """Backwards-compatible wrapper returning verified Lean theorem/lemma declarations."""
    decls, _, _ = collect_lean_stats(root, root_dir=root.parent if root.name else pathlib.Path("."))
    return decls


def parse_refuted(path: pathlib.Path) -> list[dict[str, str]]:
    if not path.exists():
        return []
    text = path.read_text(encoding="utf-8")
    entries: list[dict[str, str]] = []
    # Format 1: Markdown table rows `| ID | Conjecture | Status | Witness |`
    for line in text.splitlines():
        if line.startswith("|") and not line.startswith("| ID") and not line.startswith("|---"):
            cols = [c.strip() for c in line.strip("|").split("|")]
            if len(cols) >= 4 and cols[0]:
                entries.append(
                    {
                        "id": cols[0].strip("`"),
                        "conjecture": cols[1],
                        "status": cols[2].strip("`"),
                        "witness": cols[3],
                    }
                )
    if entries:
        return entries
    # Format 2: Structured `### REF-NNN — Title` sections with `- **Status:**` / `- **Counterexample` bullets
    blocks = re.split(r"(?m)^###\s+", text)
    for blk in blocks[1:]:
        lines = [l.strip() for l in blk.splitlines() if l.strip()]
        if not lines:
            continue
        hdr = lines[0]
        m = re.match(r"`?([A-Z]+-\d+)`?\s*[—–:-]\s*(.+)", hdr)
        if not m:
            continue
        rid, title = m.group(1).strip(), m.group(2).strip()
        status = "REFUTED"
        witness_parts: list[str] = []
        for l in lines[1:]:
            if l.startswith("- **Status:**"):
                raw_st = l.split(":**", 1)[1].strip()
                status = raw_st.split()[0].strip("`")
            elif (
                l.startswith("- **Counterexample")
                or l.startswith("- **Witness")
                or l.startswith("- **Barrier")
                or l.startswith("- **Takeaway")
            ):
                witness_parts.append(l.split(":**", 1)[1].strip())
        entries.append(
            {
                "id": rid,
                "conjecture": title,
                "status": status,
                "witness": " ".join(witness_parts) or "(see frontier/REFUTED.md)",
            }
        )
    return entries


def load_claims(path: pathlib.Path | None) -> dict[str, dict]:
    if not path or not path.exists():
        return {}
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
        return data.get("claims", {}) if isinstance(data, dict) else {}
    except Exception:
        return {}


def render_html(payload: dict) -> str:
    meta = payload["meta"]
    nodes = payload["nodes"]
    claims = payload["active_claims"]
    counts = payload["summary"]
    theorems = payload["lean_theorems"]
    refuted = payload["refuted"]

    def badge(text: str, cls: str) -> str:
        safe_cls = html.escape(cls, quote=True)
        return f'<span class="badge {safe_cls}">{html.escape(text)}</span>'

    rows_html = []
    for n in nodes:
        nid = n["id"]
        status = n.get("status", "OPEN_SUBGOAL")
        track = n.get("track", "Core")
        track_slug = re.sub(r"[^a-z0-9_-]+", "-", track.lower()).strip("-") or "unknown"
        claim = claims.get(nid)
        if status == "PROVED":
            st_html = badge("PROVED", "ok")
        elif status in ("REFUTED", "BARRIER_BLOCKED"):
            st_html = badge(status, "err")
        elif claim:
            st_html = badge(f"CLAIMED by @{claim['user']}", "warn")
        else:
            st_html = badge(status, "open")

        needs = ", ".join(n.get("needs", [])) or "none"
        target = n.get("lean_file") or n.get("target_file") or ""
        claim_cmd = f"/claim {nid}" if status == "OPEN_SUBGOAL" and not claim else "—"
        rows_html.append(
            f"<tr>"
            f"<td><code>{html.escape(nid)}</code></td>"
            f"<td>{badge(track, 'track-' + track_slug)}</td>"
            f"<td>{st_html}</td>"
            f"<td><strong>{html.escape(n.get('title', ''))}</strong>"
            f"<div class='sub'>{html.escape(n.get('barrier_notes', ''))}</div></td>"
            f"<td><code>{html.escape(target)}</code></td>"
            f"<td><code>{html.escape(needs)}</code></td>"
            f"<td><code>{html.escape(claim_cmd)}</code></td>"
            f"</tr>"
        )

    thm_items = "".join(
        f"<li><code>{html.escape(t['name'])}</code> <span class='sub'>({html.escape(t['file'])}:{t['line']})</span></li>"
        for t in theorems
    ) or "<li class='sub'>No Lean theorems proved yet.</li>"
    ref_rows = "".join(
        f"<tr><td><code>{html.escape(r['id'])}</code></td><td>{html.escape(r['conjecture'])}</td>"
        f"<td>{badge(r['status'], 'err')}</td><td>{html.escape(r['witness'])}</td></tr>"
        for r in refuted
    ) or "<tr><td colspan='4' class='sub'>No refuted entries logged yet.</td></tr>"

    lean_files = counts.get("lean_files", 0)
    lean_loc = counts.get("lean_loc", 0)

    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8" />
<meta name="viewport" content="width=device-width,initial-scale=1" />
<title>{html.escape(meta['name'])} — {html.escape(meta['title'])}</title>
<style>
  :root {{
    --bg: #0d1117; --card: #161b22; --border: #30363d; --text: #e6edf3;
    --muted: #8b949e; --accent: #58a6ff; --ok: #238636; --warn: #9e6a03; --err: #da3633;
  }}
  * {{ box-sizing: border-box; }}
  body {{ margin: 0; font-family: system-ui, -apple-system, sans-serif; background: var(--bg); color: var(--text); line-height: 1.5; }}
  .wrap {{ max-width: 1220px; margin: 0 auto; padding: 28px 20px 60px; }}
  header {{ display: flex; flex-wrap: wrap; justify-content: space-between; align-items: baseline; gap: 12px; border-bottom: 1px solid var(--border); padding-bottom: 16px; margin-bottom: 24px; }}
  h1 {{ margin: 0; font-size: 1.8rem; }}
  h2 {{ margin: 28px 0 12px; font-size: 1.2rem; color: var(--accent); }}
  a {{ color: var(--accent); text-decoration: none; }}
  a:hover {{ text-decoration: underline; }}
  .grid {{ display: grid; grid-template-columns: repeat(auto-fit, minmax(150px, 1fr)); gap: 14px; margin-bottom: 24px; }}
  .card {{ background: var(--card); border: 1px solid var(--border); border-radius: 10px; padding: 16px; }}
  .metric {{ font-size: 1.8rem; font-weight: 700; }}
  .label {{ color: var(--muted); font-size: 0.85rem; }}
  table {{ width: 100%; border-collapse: collapse; background: var(--card); border: 1px solid var(--border); border-radius: 10px; overflow: hidden; font-size: 0.9rem; }}
  th, td {{ text-align: left; padding: 10px 12px; border-bottom: 1px solid var(--border); vertical-align: top; }}
  th {{ background: #1f242c; color: var(--muted); font-weight: 600; font-size: 0.8rem; text-transform: uppercase; letter-spacing: .04em; }}
  code {{ font-family: ui-monospace, SFMono-Regular, Menlo, monospace; font-size: 0.84em; background: #0b0f14; padding: 2px 5px; border-radius: 4px; }}
  .sub {{ color: var(--muted); font-size: 0.82rem; margin-top: 3px; }}
  .badge {{ display: inline-block; padding: 2px 8px; border-radius: 999px; font-size: 0.74rem; font-weight: 600; white-space: nowrap; }}
  .badge.ok {{ background: rgba(35,134,54,.25); color: #3fb950; border: 1px solid #238636; }}
  .badge.open {{ background: rgba(88,166,255,.16); color: #79c0ff; border: 1px solid #388bfd; }}
  .badge.warn {{ background: rgba(158,106,3,.25); color: #e3b341; border: 1px solid #9e6a03; }}
  .badge.err {{ background: rgba(218,54,51,.22); color: #ff7b72; border: 1px solid #da3633; }}
  .badge.track-core {{ background: #21262d; color: #c9d1d9; }}
  .badge.track-known {{ background: rgba(163,113,247,.2); color: #d2a8ff; }}
  .badge.track-prove {{ background: rgba(63,185,80,.18); color: #56d364; }}
  .badge.track-disprove {{ background: rgba(255,123,114,.18); color: #ffa198; }}
  .badge.track-search {{ background: rgba(210,153,34,.22); color: #e3b341; }}
  ul {{ margin: 0; padding-left: 20px; columns: 2; column-gap: 24px; }}
  li {{ margin-bottom: 6px; break-inside: avoid; }}
  @media (max-width: 800px) {{ ul {{ columns: 1; }} }}
</style>
</head>
<body>
<div class="wrap">
  <header>
    <div>
      <h1>{html.escape(meta['name'])} &mdash; {html.escape(meta['title'])}</h1>
      <div class="sub">{html.escape(meta['tagline'])}</div>
    </div>
    <div class="sub">
      <a href="https://github.com/{html.escape(meta['repo'])}">GitHub Repo</a> &middot;
      <a href="frontier.json">frontier.json</a> &middot;
      Powered by <a href="https://github.com/bohemian-miser/solve-anything">solve-anything</a> &middot;
      Updated {html.escape(payload['generated_at'])}
    </div>
  </header>

  <div class="grid">
    <div class="card"><div class="metric">{counts['proved']} / {counts['total_nodes']}</div><div class="label">Frontier Nodes Proved</div></div>
    <div class="card"><div class="metric">{counts['open_unclaimed']}</div><div class="label">Open &amp; Claimable Nodes</div></div>
    <div class="card"><div class="metric">{counts['active_claims']}</div><div class="label">Active Swarm Leases</div></div>
    <div class="card"><div class="metric">{counts['lean_theorems']}</div><div class="label">Verified Lean Theorems &amp; Lemmas</div></div>
    <div class="card"><div class="metric">{counts['refuted']}</div><div class="label">Refuted Hypotheses (REF-XXX)</div></div>
    <div class="card"><div class="metric">{lean_files}</div><div class="label">Lean Source Files</div></div>
    <div class="card"><div class="metric">{lean_loc:,}</div><div class="label">Total Lean LOC</div></div>
  </div>

  <h2>Living Research DAG (frontier/FRONTIER.toml)</h2>
  <p class="sub">To claim an open node, comment <code>/claim &lt;NODE_ID&gt;</code> on the pinned <strong>Frontier Claims</strong> GitHub issue. Machine-readable feed: <a href="frontier.json"><code>frontier.json</code></a>.</p>
  <table>
    <thead>
      <tr><th>ID</th><th>Track</th><th>Status</th><th>Subgoal &amp; Barrier Notes</th><th>File</th><th>Needs</th><th>Claim</th></tr>
    </thead>
    <tbody>
      {"".join(rows_html)}
    </tbody>
  </table>

  <h2>Kernel-Verified Lean 4 Theorems &amp; Lemmas ({counts['lean_theorems']} declarations across {lean_files} files, {lean_loc:,} LOC)</h2>
  <div class="card"><ul>{thm_items}</ul></div>

  <h2>Negative Knowledge Base (frontier/REFUTED.md &mdash; {counts['refuted']} entries)</h2>
  <table>
    <thead><tr><th>ID</th><th>Conjecture / Idea</th><th>Status</th><th>Counterexample / Barrier</th></tr></thead>
    <tbody>{ref_rows}</tbody>
  </table>
</div>
</body>
</html>
"""


def run_self_test() -> int:
    """Verify Lean comment/string parsing, Unicode/modifier decls, `.lake` filter, and HTML escaping."""
    with tempfile.TemporaryDirectory(prefix="dashboard_selftest_") as tmp:
        # Place root inside a parent named `.lake` to ensure relative `.lake` filtering is used.
        root = pathlib.Path(tmp) / ".lake" / "repo"
        prob = root / "Problem"
        lake_sub = prob / ".lake"
        prob.mkdir(parents=True)
        lake_sub.mkdir()

        (lake_sub / "Ignored.lean").write_text("theorem should_ignore : True := by trivial\n", encoding="utf-8")
        (prob / "Adversarial.lean").write_text(
            "\n".join(
                [
                    'def s1 : String := "/- not a block comment"',
                    'def s2 : String := "escaped \\"/- still string\\"',
                    'theorem fake_in_string : True := by trivial',
                    '"',
                    "/-- Docstring with unmatched quote \"",
                    "theorem fake_in_comment : True := by trivial",
                    "-/",
                    "@[simp] private noncomputable theorem real_thm1 : True := by trivial",
                    "private @[simp] theorem real_thm2 : True := by trivial",
                    "lemma h₁ : True := by trivial",
                ]
            )
            + "\n",
            encoding="utf-8",
        )

        decls, lean_files, _ = collect_lean_stats(prob, root_dir=root)
        names = [d["name"] for d in decls]
        if lean_files != 1 or names != ["real_thm1", "real_thm2", "h₁"]:
            raise AssertionError(f"Unexpected Lean stats: files={lean_files}, decls={names}")

        html_out = render_html(
            {
                "meta": {
                    "name": "test",
                    "title": "Test",
                    "tagline": "Tag",
                    "repo": "org/repo",
                },
                "generated_at": "2026-01-01T00:00:00Z",
                "summary": {
                    "proved": 0,
                    "total_nodes": 1,
                    "open_unclaimed": 1,
                    "active_claims": 0,
                    "lean_theorems": len(decls),
                    "lean_files": lean_files,
                    "lean_loc": 10,
                    "refuted": 0,
                },
                "nodes": [
                    {
                        "id": "N1",
                        "track": 'Prove" onmouseover="alert(1)',
                        "status": "OPEN_SUBGOAL",
                        "title": "Test",
                    }
                ],
                "active_claims": {},
                "lean_theorems": decls,
                "refuted": [],
            }
        )
        if 'onmouseover="alert(1)"' in html_out:
            raise AssertionError("Unescaped HTML attribute injection detected in render_html output")
        if 'class="badge track-prove-onmouseover-alert-1"' not in html_out:
            raise AssertionError("Sanitized track CSS class missing from render_html output")

    print("PASS: scripts/build_dashboard.py self-test passed (Lean parser & XSS escaping).")
    return 0


def main() -> int:
    p = argparse.ArgumentParser(description="Build solve-anything static Pages dashboard")
    p.add_argument("--out", type=pathlib.Path, default=pathlib.Path("site"))
    p.add_argument("--claims", type=pathlib.Path, default=None)
    p.add_argument("--root", type=pathlib.Path, default=pathlib.Path("."))
    p.add_argument("--self-test", action="store_true", help="Run built-in unit self-tests")
    args = p.parse_args()
    if args.self_test:
        return run_self_test()

    root_dir = args.root
    meta = load_problem_meta(root_dir)
    frontier = tomllib.loads((root_dir / "frontier/FRONTIER.toml").read_text(encoding="utf-8"))
    nodes = frontier.get("node", [])
    claims = load_claims(args.claims)
    theorems, lean_files, lean_loc = collect_lean_stats(
        root_dir / meta["lean_root"],
        root_dir=root_dir,
        challenge_file=meta["challenge_file"],
    )
    refuted = parse_refuted(root_dir / "frontier/REFUTED.md")

    now = dt.datetime.now(dt.timezone.utc)
    active_claims: dict[str, dict] = {}
    for nid, info in claims.items():
        exp = info.get("expires_at")
        if exp:
            try:
                if dt.datetime.fromisoformat(exp.replace("Z", "+00:00")) <= now:
                    continue
            except ValueError:
                pass
        active_claims[nid] = info

    proved_n = sum(1 for n in nodes if n.get("status") == "PROVED")
    open_unclaimed = sum(
        1 for n in nodes if n.get("status") == "OPEN_SUBGOAL" and n["id"] not in active_claims
    )

    payload = {
        "schema": "solve-anything-dashboard/v1",
        "meta": meta,
        "generated_at": now.strftime("%Y-%m-%dT%H:%M:%SZ"),
        "summary": {
            "total_nodes": len(nodes),
            "proved": proved_n,
            "open_unclaimed": open_unclaimed,
            "active_claims": len(active_claims),
            "lean_theorems": len(theorems),
            "lean_files": lean_files,
            "lean_loc": lean_loc,
            "refuted": len(refuted),
        },
        "nodes": nodes,
        "active_claims": active_claims,
        "lean_theorems": theorems,
        "refuted": refuted,
    }

    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / "frontier.json").write_text(
        json.dumps(payload, indent=2, allow_nan=False) + "\n", encoding="utf-8"
    )
    (args.out / "index.html").write_text(render_html(payload), encoding="utf-8")
    print(
        f"PASS: Wrote {args.out / 'frontier.json'} and {args.out / 'index.html'} "
        f"({len(nodes)} nodes, {len(theorems)} Lean theorems across {lean_files} files / "
        f"{lean_loc} LOC, {len(refuted)} refuted)."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
