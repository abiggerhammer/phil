#!/usr/bin/env python3
"""MHB ATC: fail-closed single-slot admission planning from a GitHub snapshot.

The planner is pure and grants no authorization. The trusted GitHub Actions
caller must revalidate the live branch head immediately before creating a PR.
"""
from __future__ import annotations

import argparse
import datetime as dt
import json
import re
import sys

from mhb_atc_stage import MARKER, parse_intent

MARKER_FENCE = re.compile(r"~~~json\n(\{.*?\})\n~~~", re.DOTALL)
SHA = re.compile(r"[a-f0-9]{40}\Z")
ACTIVE_LABEL = "atc: admitted"
STAGED_LABEL = "atc: staged"
TRUSTED_CREATOR = "github-actions[bot]"


def names(obj: dict) -> set[str]:
    labels = obj.get("labels", [])
    if not isinstance(labels, list):
        raise ValueError("malformed labels")
    output = set()
    for label in labels:
        if not isinstance(label, dict) or not isinstance(label.get("name"), str):
            raise ValueError("malformed label record")
        output.add(label["name"])
    return output


def machine_record(issue: dict) -> dict:
    body = issue.get("body", "")
    if not isinstance(body, str) or not body.startswith(MARKER + "\n"):
        raise ValueError("candidate missing trusted staging marker")
    found = MARKER_FENCE.search(body)
    if not found:
        raise ValueError("candidate missing machine record")
    record = json.loads(found.group(1))
    if not isinstance(record, dict) or set(record) != {"version", "lane", "branch", "head_sha"}:
        raise ValueError("candidate machine record has unexpected schema")
    if type(record["version"]) is not int or record["version"] != 1:
        raise ValueError("unsupported candidate record version")
    parsed = parse_intent(record["branch"], record["head_sha"], record["head_sha"])
    if parsed["lane"] != record["lane"]:
        raise ValueError("candidate record lane mismatch")
    return parsed


def plan(issues: list, prs: list) -> dict:
    """Do not admit until *all* MHB-managed in-flight PRs are cleared."""
    if not isinstance(issues, list) or not isinstance(prs, list):
        raise ValueError("incomplete API snapshot")
    active_prs: list[int] = []
    active_branches: set[str] = set()
    for pr in prs:
        if not isinstance(pr, dict) or pr.get("state") != "open":
            raise ValueError("unexpected PR in open-PR snapshot")
        head = pr.get("head")
        if not isinstance(head, dict) or not isinstance(head.get("ref"), str):
            raise ValueError("PR missing head ref")
        branch = head["ref"]
        label_names = names(pr)
        if branch.startswith("hamster/staged/") or ACTIVE_LABEL in label_names:
            number = pr.get("number")
            if type(number) is not int or number < 1:
                raise ValueError("invalid active PR number")
            active_prs.append(number)
            active_branches.add(branch)

    candidates = []
    admitted_issues: list[int] = []
    seen_branches: set[str] = set()
    for issue in issues:
        if not isinstance(issue, dict) or issue.get("state") != "open":
            raise ValueError("unexpected issue in open-issue snapshot")
        labels = names(issue)
        if STAGED_LABEL not in labels and ACTIVE_LABEL not in labels:
            continue
        if "pull_request" in issue:
            # PRs appear in the GitHub Issues API. We already scanned all open
            # PRs separately; reject a PR masquerading as a queue issue.
            raise ValueError("PR is incorrectly labelled as an ATC candidate issue")
        if issue.get("user", {}).get("login") != TRUSTED_CREATOR:
            raise ValueError("ATC candidate not created by trusted stage bot")
        number = issue.get("number")
        if type(number) is not int or number < 1:
            raise ValueError("invalid candidate issue number")
        if STAGED_LABEL in labels and ACTIVE_LABEL in labels:
            raise ValueError("ambiguous candidate state labels")
        record = machine_record(issue)
        branch = record["branch"]
        if branch in seen_branches:
            raise ValueError("duplicate staged branch records")
        seen_branches.add(branch)
        if str(issue.get("title")) != "ATC candidate: " + branch:
            raise ValueError("candidate title does not match machine branch")
        lane_labels = {label for label in labels if label.startswith("lane: ")}
        if lane_labels != {"lane: " + record["lane"]}:
            raise ValueError("candidate lane labels inconsistent")
        if ACTIVE_LABEL in labels:
            admitted_issues.append(number)
            continue
        created = issue.get("created_at")
        if not isinstance(created, str):
            raise ValueError("candidate missing enqueue timestamp")
        at = dt.datetime.fromisoformat(created.replace("Z", "+00:00"))
        if at.tzinfo is None:
            raise ValueError("candidate has naive enqueue timestamp")
        candidates.append((at.astimezone(dt.timezone.utc), number, record))

    # An admitted issue may be waiting for a manual closeout. Fail closed
    # rather than declaring the slot free simply because the PR disappeared.
    if active_prs or admitted_issues:
        return {"decision": "hold", "reason": "active or unreconciled admissions",
                "open_staged_prs": sorted(active_prs),
                "unreconciled_issue_ids": sorted(admitted_issues)}
    if not candidates:
        return {"decision": "hold", "reason": "no staged candidates"}
    _, number, record = min(candidates, key=lambda v: (v[0], v[1]))
    return {"decision": "would-admit", "candidate_issue": number,
            "lane": record["lane"], "branch": record["branch"],
            "head_sha": record["head_sha"], "capacity": 1,
            "warning": "revalidate branch head and PR state before writing; no merge authority"}


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--issues", required=True, help="JSON array of all open issues")
    p.add_argument("--prs", required=True, help="JSON array of all open PRs")
    args = p.parse_args()
    with open(args.issues, encoding="utf-8") as f:
        issues = json.load(f)
    with open(args.prs, encoding="utf-8") as f:
        prs = json.load(f)
    print(json.dumps(plan(issues, prs), sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, TypeError, AttributeError, KeyError) as exc:
        print(f"MHB-ATC admission denied: {exc}", file=sys.stderr)
        sys.exit(2)
