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
from mhb_atc_immutable import contract, github_ref_sha, verify_pr

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


def pr_for_issue(pr: dict, item: dict, repo: str, publisher: dict) -> dict:
    """Bind a PR to the canonical protected admitted head, never staged ref."""
    binding = contract(item["issue"], item["lane"], item["branch"],
                       item["head_sha"], repo)
    check = verify_pr(pr, binding, publisher)
    label_set = names(pr)
    lane_labels = {l for l in label_set if l.startswith("lane: ")}
    if lane_labels and lane_labels != {"lane: " + item["lane"]}:
        raise ValueError("PR has conflicting lane ownership labels")
    if STAGED_LABEL in label_set or ADMITTING_LABEL in label_set:
        raise ValueError("PR has an invalid ATC state label")
    return {"pr": check["pr"], "state": pr["state"],
            "needs_label": ACTIVE_LABEL not in label_set or
                           "lane: " + item["lane"] not in label_set}

def plan(issues: list, prs: list, refs: list, repo: str, now: dt.datetime, publisher: dict) -> dict:
    """Return at most one idempotent write or a diagnostic hold.

    All candidates are validated before any action is returned. Unknown or
    ambiguous linked PRs fail closed; a stale reservation with no PR may be
    returned to the staging queue only after a grace period.
    """
    if not isinstance(issues, list) or not isinstance(prs, list) or not isinstance(refs, list):
        raise ValueError("incomplete reconciliation snapshot")
    if not isinstance(repo, str) or "/" not in repo:
        raise ValueError("repository identity required")
    if now.tzinfo is None:
        raise ValueError("now must be timezone-aware")
    now = now.astimezone(dt.timezone.utc)
    if not isinstance(publisher, dict) or not isinstance(publisher.get("bot_login"), str):
        raise ValueError("authenticated publisher identity is required")
    candidates = [candidate(issue) for issue in issues]
    branches = [i["branch"] for i in candidates]
    if len(branches) != len(set(branches)):
        raise ValueError("duplicate queue identities")
    # Every live candidate has a deterministic admitted-ref identity.
    bindings = {i["branch"]: contract(i["issue"], i["lane"], i["branch"],
                                      i["head_sha"], repo) for i in candidates}
    by_admitted: dict[str, list[dict]] = {
        b["admitted_branch"]: [] for b in bindings.values()}
    for pr in prs:
        if not isinstance(pr, dict) or not isinstance(pr.get("head"), dict):
            raise ValueError("malformed PR snapshot")
        branch = pr["head"].get("ref")
        if branch not in by_admitted:
            raise ValueError("PR from unknown admitted candidate in snapshot")
        by_admitted[branch].append(pr)

    actions = []
    for item in candidates:
        binding = bindings[item["branch"]]
        admitted = binding["admitted_branch"]
        related = by_admitted[admitted]
        if len(related) > 1:
            raise ValueError("multiple PRs exist for admitted candidate")
        ref_sha = github_ref_sha(refs, admitted)
        if ref_sha is not None and ref_sha != item["head_sha"]:
            raise ValueError("admitted protected ref SHA drift")
        if related and ref_sha is None:
            raise ValueError("linked PR exists but admitted ref is missing")
        pr = pr_for_issue(related[0], item, repo, publisher) if related else None
        if pr is None and ref_sha is not None:
            # An interrupted create-ref -> create-PR transaction must never
            # be auto-requeued: another attempt would reuse/squat the ref.
            raise ValueError("orphan admitted ref without PR: manual reconciliation required")
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
    p.add_argument("--refs", required=True, help="complete admitted-ref API snapshot")
    p.add_argument("--publisher-json", required=True,
                   help="verified GitHub App/bot platform identity snapshot")
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
        print(json.dumps(sorted(contract(i["issue"], i["lane"], i["branch"],
                                         i["head_sha"], args.repo)["admitted_branch"]
                                for i in items)))
        return 0
    with open(args.prs, encoding="utf-8") as handle:
        prs = json.load(handle)
    with open(args.refs, encoding="utf-8") as handle:
        refs = json.load(handle)
    with open(args.publisher_json, encoding="utf-8") as handle:
        publisher = json.load(handle)
    print(json.dumps(plan(issues, prs, refs, args.repo,
                          dt.datetime.now(dt.timezone.utc), publisher), sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, TypeError, ValueError, KeyError, AttributeError,
            json.JSONDecodeError) as exc:
        print("MHB-ATC reconciliation failed closed: " + str(exc), file=sys.stderr)
        sys.exit(2)
