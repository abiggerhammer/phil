#!/usr/bin/env python3
"""Pure, fail-closed MHB-ATC slot release and interrupted-admission recovery.

Never infer that a check passed or that a PR is safe to merge. This only
reconciles reservation state with the observed open/closed PR lifecycle.
"""
from __future__ import annotations

import argparse
import datetime as dt
import json
import sys

from mhb_atc_admit import ACTIVE_LABEL, STAGED_LABEL, TRUSTED_CREATOR, machine_record, names

ADMITTING_LABEL = "atc: admitting"
STATES = (STAGED_LABEL, ADMITTING_LABEL, ACTIVE_LABEL)
MIN_RETRY_AGE = dt.timedelta(minutes=15)


def timestamp(value: str) -> dt.datetime:
    if not isinstance(value, str):
        raise ValueError("missing timestamp")
    parsed = dt.datetime.fromisoformat(value.replace("Z", "+00:00"))
    if parsed.tzinfo is None:
        raise ValueError("timestamp must contain a timezone")
    return parsed.astimezone(dt.timezone.utc)


def candidate(issue: dict) -> dict:
    if not isinstance(issue, dict) or issue.get("state") != "open":
        raise ValueError("reconciliation requires open candidate issues")
    labels = names(issue)
    states = set(STATES) & labels
    if len(states) != 1:
        raise ValueError("candidate must have exactly one ATC state label")
    if "pull_request" in issue:
        raise ValueError("PR cannot masquerade as a candidate issue")
    if not isinstance(issue.get("user"), dict) or issue["user"].get("login") != TRUSTED_CREATOR:
        raise ValueError("untrusted candidate creator")
    number = issue.get("number")
    if type(number) is not int or number <= 0:
        raise ValueError("bad candidate issue number")
    record = machine_record(issue)
    if issue.get("title") != "ATC candidate: " + record["branch"]:
        raise ValueError("candidate title mismatch")
    lane_labels = {label for label in labels if label.startswith("lane: ")}
    if lane_labels != {"lane: " + record["lane"]}:
        raise ValueError("candidate lane ownership mismatch")
    return {"issue": number, "state": next(iter(states)), "lane": record["lane"],
            "branch": record["branch"], "head_sha": record["head_sha"],
            "updated_at": timestamp(issue.get("updated_at")),
            "created_at": timestamp(issue.get("created_at"))}


def pr_for_issue(pr: dict, item: dict, repo: str) -> dict:
    """Require a unique exact-SHA PR with a canonical link to its candidate."""
    if not isinstance(pr, dict) or pr.get("state") not in ("open", "closed"):
        raise ValueError("unknown PR lifecycle state")
    number = pr.get("number")
    if type(number) is not int or number <= 0:
        raise ValueError("invalid PR number")
    head, base = pr.get("head"), pr.get("base")
    if not isinstance(head, dict) or not isinstance(base, dict):
        raise ValueError("PR missing branch identities")
    hrepo, brepo = head.get("repo"), base.get("repo")
    if not isinstance(hrepo, dict) or not isinstance(brepo, dict):
        raise ValueError("PR repository provenance missing")
    if (head.get("ref") != item["branch"] or head.get("sha") != item["head_sha"]
        or hrepo.get("full_name") != repo or base.get("ref") != "main"
        or brepo.get("full_name") != repo):
        raise ValueError("PR branch/head/base identity mismatch")
    if pr.get("title") != "MHB-ATC admission: " + item["lane"] + " / " + str(item["issue"]):
        raise ValueError("PR admission title mismatch")
    body = pr.get("body")
    expected_lines = [
        "MHB-ATC admitted staged candidate; this PR is **not** merge clearance.",
        "- Candidate issue: #" + str(item["issue"]),
        "- Lane: " + item["lane"],
        "- Staged branch: " + item["branch"],
        "- Exact registered head: " + item["head_sha"],
    ]
    if not isinstance(body, str) or any(body.splitlines().count(line) != 1 for line in expected_lines):
        raise ValueError("PR admission binding missing or ambiguous")
    label_set = names(pr)
    lane_labels = {l for l in label_set if l.startswith("lane: ")}
    if lane_labels and lane_labels != {"lane: " + item["lane"]}:
        raise ValueError("PR has conflicting lane ownership labels")
    if STAGED_LABEL in label_set or ADMITTING_LABEL in label_set:
        raise ValueError("PR has an invalid ATC state label")
    return {"pr": number, "state": pr["state"],
            "needs_label": ACTIVE_LABEL not in label_set or
                           "lane: " + item["lane"] not in label_set}


def plan(issues: list, prs: list, repo: str, now: dt.datetime) -> dict:
    """Return at most one idempotent write or a diagnostic hold.

    All candidates are validated before any action is returned. Unknown or
    ambiguous linked PRs fail closed; a stale reservation with no PR may be
    returned to the staging queue only after a grace period.
    """
    if not isinstance(issues, list) or not isinstance(prs, list):
        raise ValueError("incomplete reconciliation snapshot")
    if not isinstance(repo, str) or "/" not in repo:
        raise ValueError("repository identity required")
    if now.tzinfo is None:
        raise ValueError("now must be timezone-aware")
    now = now.astimezone(dt.timezone.utc)
    candidates = [candidate(issue) for issue in issues]
    branches = [i["branch"] for i in candidates]
    if len(branches) != len(set(branches)):
        raise ValueError("duplicate queue identities")
    all_branches = set(branches)
    by_branch: dict[str, list[dict]] = {b: [] for b in all_branches}
    for pr in prs:
        if not isinstance(pr, dict) or not isinstance(pr.get("head"), dict):
            raise ValueError("malformed PR snapshot")
        branch = pr["head"].get("ref")
        if branch not in all_branches:
            raise ValueError("PR from unknown candidate branch in snapshot")
        by_branch[branch].append(pr)

    actions = []
    for item in candidates:
        related = by_branch[item["branch"]]
        if len(related) > 1:
            raise ValueError("multiple PRs exist for candidate branch")
        pr = pr_for_issue(related[0], item, repo) if related else None
        state = item["state"]
        if pr is not None and pr["state"] == "closed":
            # A closed PR consumes no active CI slot. An explicit admission
            # reservation must have happened before we can release the issue.
            if state == STAGED_LABEL:
                raise ValueError("closed PR associated with unreserved staged issue")
            actions.append({"action": "release", "issue": item["issue"], "lane": item["lane"],
                            "pr": pr["pr"], "branch": item["branch"],
                            "head_sha": item["head_sha"], "prior_state": state})
        elif pr is not None and pr["state"] == "open":
            if state == STAGED_LABEL:
                raise ValueError("staged issue has unreserved open PR")
            if pr["needs_label"] or state == ADMITTING_LABEL:
                actions.append({"action": "repair", "issue": item["issue"], "lane": item["lane"],
                                "pr": pr["pr"], "branch": item["branch"],
                                "head_sha": item["head_sha"],
                                "prior_state": state,
                                "needs_label": pr["needs_label"]})
        elif state == ADMITTING_LABEL:
            if now - item["updated_at"] >= MIN_RETRY_AGE:
                actions.append({"action": "retry", "issue": item["issue"], "lane": item["lane"],
                                "branch": item["branch"], "head_sha": item["head_sha"],
                                "prior_state": state})
        elif state == ACTIVE_LABEL:
            # Never release without positive evidence of a closed exact-head PR.
            raise ValueError("admitted issue has no matching PR; manual investigation required")

    if not actions:
        return {"decision": "hold", "reason": "no eligible reconciliation"}
    priority = {"release": 0, "repair": 1, "retry": 2}
    chosen = min(actions, key=lambda a: (priority[a["action"]], a["issue"]))
    return {"decision": "reconcile", **chosen}


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--issues", required=True)
    p.add_argument("--prs", required=True)
    p.add_argument("--repo", required=True)
    p.add_argument("--branches-only", action="store_true",
                   help="emit validated candidate branch list and no actions")
    args = p.parse_args()
    with open(args.issues, encoding="utf-8") as handle:
        issues = json.load(handle)
    if args.branches_only:
        items = [candidate(i) for i in issues]
        branches = [i["branch"] for i in items]
        if len(branches) != len(set(branches)):
            raise ValueError("duplicate candidate branches")
        print(json.dumps(sorted(branches)))
        return 0
    with open(args.prs, encoding="utf-8") as handle:
        prs = json.load(handle)
    print(json.dumps(plan(issues, prs, args.repo,
                          dt.datetime.now(dt.timezone.utc)), sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, TypeError, ValueError, KeyError, AttributeError,
            json.JSONDecodeError) as exc:
        print("MHB-ATC reconciliation failed closed: " + str(exc), file=sys.stderr)
        sys.exit(2)
