#!/usr/bin/env python3
"""Read-only historical CI radar and deterministic SHADOW admission advice for MHB.

No command in this file creates PRs, grants leases, changes labels, or merges code.
"""
from __future__ import annotations

import argparse
import datetime as dt
import json
import re
import statistics
import subprocess
import sys
from collections import Counter
from pathlib import Path

SHA = re.compile(r"^[a-f0-9]{40}$")
LANE = re.compile(r"^[a-z][a-z0-9-]*$")
BRANCH = re.compile(r"^hamster/([a-z][a-z0-9-]*)/.+$")
ACTIVE_STATES = frozenset({"verifying", "awaiting-merge"})
KNOWN_STATES = ACTIVE_STATES | {"blocked", "superseded"}
JOB_NAMES = {"CI", "Proofs", "Phase 1 Audit Reconciliation Conformance",
             "Phase 1 Warning-Free Haskell Integration"}


def api(repo: str, endpoint: str) -> dict:
    """Fetch JSON through an existing authenticated gh CLI session."""
    command = ["gh", "api", f"repos/{repo}/{endpoint}"]
    p = subprocess.run(command, capture_output=True, text=True, check=False)
    if p.returncode:
        raise RuntimeError(f"GitHub API failed for {endpoint}: {p.stderr.strip()}")
    value = json.loads(p.stdout)
    if not isinstance(value, dict):
        raise ValueError(f"Expected API object from {endpoint}")
    return value


def seconds(start: str | None, end: str | None) -> float | None:
    if not start or not end:
        return None
    a = dt.datetime.fromisoformat(start.replace("Z", "+00:00"))
    b = dt.datetime.fromisoformat(end.replace("Z", "+00:00"))
    return round((b - a).total_seconds(), 1) if b >= a else None


def summarize_day(day: str, runs: list[dict], total: int, jobs: list[dict]) -> dict:
    """Report whole-day API count separately from explicitly sampled detail."""
    by_head = Counter(str(r.get("head_sha") or "unknown") for r in runs)
    by_event = Counter(str(r.get("event") or "unknown") for r in runs)
    by_outcome = Counter(str(r.get("conclusion") or r.get("status") or "unknown") for r in runs)
    waits = [seconds(j.get("created_at"), j.get("started_at")) for j in jobs]
    runtimes = [seconds(j.get("started_at"), j.get("completed_at")) for j in jobs]
    waits = [x for x in waits if x is not None]
    runtimes = [x for x in runtimes if x is not None]
    return {
        "date_utc": day,
        "reported_total_workflow_runs": total,
        "sampled_workflow_runs": len(runs),
        "sample_is_complete": len(runs) == total,
        "sampled_event_counts": dict(sorted(by_event.items())),
        "sampled_outcomes": dict(sorted(by_outcome.items())),
        "sampled_top_revision_bursts": [
            {"sha": sha, "observed_workflow_runs": count}
            for sha, count in sorted(by_head.items(), key=lambda x: (-x[1], x[0]))[:6]
        ],
        "sampled_jobs": len(jobs),
        "started_jobs": len(waits),
        "completed_jobs": len(runtimes),
        "queue_wait_seconds": {
            "max": max(waits) if waits else None,
            "median": statistics.median(waits) if waits else None,
        },
        "execution_seconds": {
            "max": max(runtimes) if runtimes else None,
            "median": statistics.median(runtimes) if runtimes else None,
        },
    }


def scan_day(repo: str, day: str, pages: int, job_limit: int) -> dict:
    # Do not silently treat an invalid date as an empty day.
    dt.date.fromisoformat(day)
    if not re.fullmatch(r"\d{4}-\d\d-\d\d", day):
        raise ValueError("Use ISO dates YYYY-MM-DD")
    runs: list[dict] = []
    total: int | None = None
    for page in range(1, pages + 1):
        data = api(repo, f"actions/runs?created={day}..{day}&per_page=100&page={page}")
        if total is None:
            total = int(data["total_count"])
        batch = data.get("workflow_runs", [])
        if not isinstance(batch, list):
            raise ValueError("Malformed workflow runs response")
        runs.extend(batch)
        if not batch or len(runs) >= total:
            break

    # Most recent per (revision, workflow) to avoid sampling repeated retries.
    chosen: list[dict] = []
    seen: set[tuple[str, str]] = set()
    for run in runs if job_limit > 0 else []:
        key = (str(run.get("head_sha")), str(run.get("name")))
        if run.get("name") not in JOB_NAMES or key in seen:
            continue
        seen.add(key)
        chosen.append(run)
        if len(chosen) == job_limit:
            break

    jobs: list[dict] = []
    for run in chosen:
        data = api(repo, f"actions/runs/{int(run['id'])}/jobs?per_page=100")
        batch = data.get("jobs", [])
        if not isinstance(batch, list):
            raise ValueError("Malformed jobs response")
        if int(data.get("total_count", len(batch))) != len(batch):
            raise ValueError("Job page truncated: refusing misleading sample")
        jobs.extend(batch)
    return summarize_day(day, runs, int(total or 0), jobs)


def recommend(snapshot: dict) -> dict:
    """Fail-closed SHADOW recommendation; never an authorization to create a PR."""
    capacity = snapshot.get("capacity", 1)
    if type(capacity) is not int or capacity < 1:
        raise ValueError("capacity must be a positive integer")
    admitted = snapshot.get("admitted")
    candidates = snapshot.get("candidates")
    if not isinstance(admitted, list) or not isinstance(candidates, list):
        raise ValueError("admitted and candidates must both be lists")

    seen_branches: set[str] = set()
    active = 0
    for item in admitted:
        if not isinstance(item, dict) or item.get("state") not in KNOWN_STATES:
            raise ValueError("unknown admitted PR state: fail closed")
        if not SHA.fullmatch(str(item.get("head_sha", ""))):
            raise ValueError("missing or malformed admitted exact head SHA")
        if item["state"] in ACTIVE_STATES:
            active += 1
    if active >= capacity:
        return {"decision": "hold", "reason": "verification capacity occupied",
                "active": active, "capacity": capacity}

    validated: list[tuple[dt.datetime, str, str, str]] = []
    for item in candidates:
        if not isinstance(item, dict):
            raise ValueError("malformed candidate")
        branch = str(item.get("branch", ""))
        match = BRANCH.fullmatch(branch)
        sha = str(item.get("head_sha", ""))
        if not match or not LANE.fullmatch(match.group(1)) or not SHA.fullmatch(sha):
            raise ValueError("invalid candidate lane, branch, or SHA")
        if branch in seen_branches:
            raise ValueError("duplicate candidate branch")
        seen_branches.add(branch)
        stamp = dt.datetime.fromisoformat(str(item["enqueued_at"]).replace("Z", "+00:00"))
        if stamp.tzinfo is None:
            raise ValueError("candidate enqueued_at must include timezone")
        validated.append((stamp.astimezone(dt.timezone.utc), match.group(1), branch, sha))

    if not validated:
        return {"decision": "hold", "reason": "no candidates", "active": active,
                "capacity": capacity}

    # FIFO by durable enqueue time; branch and head SHA tie-break deterministically.
    _, lane, branch, sha = min(validated)
    return {"decision": "would-admit", "lane": lane, "branch": branch,
            "head_sha": sha, "active": active, "capacity": capacity,
            "warning": "shadow-only; live SHA, ownership and check policy must be revalidated"}


def markdown(reports: list[dict]) -> str:
    lines = ["### Mecha Hamster Ball — read-only CI radar", "",
             "Whole-day run counts are GitHub API totals. All other statistics",
             "are **samples**, biased to the newest pages and selected workflows.",
             "They are not percentile estimates or billing totals.", "",
             "| UTC date | Runs reported | Runs sampled | Jobs sampled | Median queue | Max queue |",
             "|---|---:|---:|---:|---:|---:|"]
    for r in reports:
        q = r["queue_wait_seconds"]
        f = lambda x: "n/a" if x is None else f"{x:.0f}s"
        lines.append(f"| {r['date_utc']} | {r['reported_total_workflow_runs']} | "
                     f"{r['sampled_workflow_runs']} | {r['sampled_jobs']} | "
                     f"{f(q['median'])} | {f(q['max'])} |")
    lines += ["", "This is observational only. Admission and merge authority are unchanged."]
    return "\n".join(lines)


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo", default="", help="GitHub owner/repo (or GH_REPO env)")
    p.add_argument("--date", action="append", help="UTC YYYY-MM-DD; repeat for history")
    p.add_argument("--max-pages", type=int, default=2)
    p.add_argument("--jobs-per-day", type=int, default=6)
    p.add_argument("--format", choices=("json", "markdown"), default="markdown")
    p.add_argument("--admission-snapshot", type=Path,
                   help="offline snapshot JSON; print shadow decision, never mutate GitHub")
    args = p.parse_args()
    if args.admission_snapshot:
        print(json.dumps(recommend(json.loads(args.admission_snapshot.read_text())),
                         sort_keys=True, indent=2))
        return 0
    import os
    repo = args.repo or os.environ.get("GH_REPO") or os.environ.get("GITHUB_REPOSITORY", "")
    if not re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repo):
        p.error("a valid --repo owner/name or GITHUB_REPOSITORY is required")
    if not (1 <= args.max_pages <= 10 and 0 <= args.jobs_per_day <= 30):
        p.error("max-pages must be 1..10 and jobs-per-day 0..30")
    dates = args.date or [dt.datetime.now(dt.timezone.utc).date().isoformat()]
    reports = [scan_day(repo, day, args.max_pages, args.jobs_per_day) for day in dates]
    if args.format == "json":
        print(json.dumps({"reports": reports}, sort_keys=True, indent=2))
    else:
        print(markdown(reports))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, RuntimeError, KeyError, json.JSONDecodeError) as exc:
        print(f"MHB-ATC radar failed closed: {exc}", file=sys.stderr)
        sys.exit(2)
