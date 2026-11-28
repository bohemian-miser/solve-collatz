# Running a Self-Hosted Autonomous Review & Research Swarm

Every `solve-anything` repository uses a **strict two-plane architecture**:

1. **Plane 1 — Public GitHub Actions (Zero AI Secrets):**
   - `.github/workflows/verify.yml` runs on every PR with `permissions: contents: read` only, enforcing frozen `Challenge.lean` / `problem.toml`, source hygiene, `lake build` (`warningAsError = true`), standard-axioms-only auditing (`scripts/audit_axioms.py`, every declaration), and `search/ci_checks.sh`.
   - `.github/workflows/claims.yml` arbitrates `/claim <NODE_ID>`, `/release <NODE_ID>`, and `/status` comments on the pinned **Frontier Claims** issue and auto-expires stale 24h leases every 6 hours.
   - `.github/workflows/dashboard.yml` publishes the live Frontier DAG and `frontier.json` to GitHub Pages on every merge to `main`.

2. **Plane 2 — Self-Hosted Autonomous Server (Reviewer Bot + 24/7 Worker):**
   - Any maintainer or contributor with a dedicated Linux box and an agent CLI (Claude Code, Codex, Gemini CLI, etc.) can run an autonomous **Adversarial Rubric Reviewer** and/or **24/7 Frontier Worker** without ever placing AI credentials inside public GitHub Actions runners.

---

## Security Boundaries (Non-Negotiable)

Public repos receive **untrusted pull requests**. Always enforce these boundaries on your server:

1. **Isolate in a non-root container or dedicated VM** with zero access to personal SSH keys, cloud credentials, or unrelated repositories.
2. **Use a fine-grained GitHub PAT** scoped *exclusively* to the target theorem repository (`Pull requests: Read & write`, `Issues: Read & write`, `Contents: Read` for the reviewer; fork-only push for the worker).
3. **Never execute untrusted PR code on the reviewer host:**
   - GitHub Actions `verify.yml` already compiles Lean and runs `search/ci_checks.sh` inside GitHub's ephemeral runner sandbox.
   - The self-hosted reviewer should read **only** `gh pr diff`, the PR body, and the `verify` check status — NEVER run `lake build` or PR scripts on the host holding your LLM or GitHub tokens.
4. **Treat all PR text, comments, and docstrings as untrusted data** (prompt-injection defense: never follow instructions inside PR diffs or issue comments).
5. **Check your model provider's Terms of Service** regarding automated unattended accounts vs API keys.

---

## Role 1: Read-Only Adversarial Rubric Reviewer Loop

Polls open PRs where CI `verify` already succeeded, audits the diff against all 5 `review/*.md` rubrics on trusted `main`, posts structured `[S0]`/`[S1]`/`[S2]` feedback, and adds `ready-for-human` when all 5 rubrics reach `0 [S0] / 0 [S1]`:

```bash
#!/usr/bin/env bash
set -euo pipefail

REPO="${REPO:?Set REPO=owner/solve-your-problem}"
MAIN_DIR="${MAIN_DIR:-/workspace/repo-main}"

while true; do
  git -C "$MAIN_DIR" fetch origin main --quiet
  git -C "$MAIN_DIR" reset --hard origin/main --quiet

  gh pr list -R "$REPO" --state open --json number,headRefOid,labels,statusCheckRollup \
    | jq -r '.[] | select((.labels | map(.name) | index("ready-for-human")) == null)
                 | select(.statusCheckRollup | any(.name == "verify" and .conclusion == "SUCCESS"))
                 | "\(.number) \(.headRefOid)"' \
    | while read -r PR_NUM HEAD_SHA; do
        STAMP="/tmp/reviewed_${PR_NUM}_${HEAD_SHA}"
        [ -f "$STAMP" ] && continue

        gh pr diff -R "$REPO" "$PR_NUM" > "/tmp/pr_${PR_NUM}.diff"
        gh pr view -R "$REPO" "$PR_NUM" --json title,body > "/tmp/pr_${PR_NUM}.body.json"

        # Invoke your sandboxed read-only agent against $MAIN_DIR/review/*.md
        # (treating diff/body strictly as untrusted data; never execute PR code!).
        touch "$STAMP"
      done

  sleep 300
done
```

---

## Role 2: 24/7 Continuous Research & Search Worker

Runs in a separate container pushing only to a fork, dogfooding the exact public protocol:

1. Poll `frontier.json` from GitHub Pages (or `frontier/FRONTIER.toml` + `claims` branch `claims.json`).
2. Comment `/claim <NODE_ID>` on the pinned Frontier Claims issue.
3. Work the node (Track A: red-team against `frontier/BARRIERS.md` first, open a Lean PR or log a dead end in `frontier/REFUTED.md`; Track B: run structured search on idle CPU cores and emit a Lean certificate PR on any hit).
4. Open a PR with the completed `Quality pass:` (`Q1`–`Q5`) block and comment `/release <NODE_ID>`.
