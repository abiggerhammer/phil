#!/usr/bin/env python3
"""Fail-closed Phase 2 staged candidate WIP guard (read-only pure policy).

Called by the trusted default-branch ATC staging workflow *before* changing
candidate issues. Does not grant admission, create PRs, or certify anything.
"""
from __future__ import annotations

import argparse
import json
import sys

from mhb_atc_admit import (
    ACTIVE_LABEL, ADMITTING_LABEL, STAGED_LABEL,
    TRUSTED_CREATOR, machine_record, names,
)

LANES = {"phase2-selfhost", "phase2-embedded"}
STATES = {STAGED_LABEL, ADMITTING_LABEL, ACTIVE_LABEL}


def plan(issues: list, lane: str, branch: str) -> dict:
    if lane not in LANES or not branch.startswith("hamster/staged/" + lane + "/"):
        raise ValueError("unapproved Phase 2 lane or branch")
    if not isinstance(issues, list):
        raise ValueError("incomplete open-issue snapshot")

    staged, active = [], []
    seen = set()
    for issue in issues:
        if not isinstance(issue, dict) or issue.get("state") != "open":
            raise ValueError("malformed open issue")
        labels = names(issue)
        states = STATES & labels
        if not states:
            continue
        if "pull_request" in issue:
            # The issues endpoint includes PR records; admission scans those
            # separately. A PR may not impersonate a queue candidate.
            if STAGED_LABEL in states or ADMITTING_LABEL in states:
                raise ValueError("PR masquerades as staged issue")
            continue
        if issue.get("user", {}).get("login") != TRUSTED_CREATOR:
            raise ValueError("untrusted ATC candidate")
        if len(states) != 1:
            raise ValueError("ambiguous ATC candidate labels")
        record = machine_record(issue)
        lane_labels = {name for name in labels if name.startswith("lane: ")}
        if lane_labels != {"lane: " + record["lane"]}:
            raise ValueError("ATC candidate lane mismatch")
        if issue.get("title") != "ATC candidate: " + record["branch"]:
            raise ValueError("ATC candidate title mismatch")
        if record["branch"] in seen:
            raise ValueError("duplicate ATC candidate")
        seen.add(record["branch"])
        if record["lane"] != lane:
            continue
        if STAGED_LABEL in states:
            staged.append(record["branch"])
        else:
            active.append(record["branch"])

    if len(staged) > 1 or len(active) > 1:
        raise ValueError("Phase 2 lane WIP is already over capacity")
    if branch in active:
        raise ValueError("cannot restage admitting/admitted branch")
    if staged and staged != [branch]:
        raise ValueError("Phase 2 lane already has one distinct staged successor")
    return {"decision": "allow-stage", "lane": lane, "branch": branch,
            "active_count": len(active), "staged_count": len(staged),
            "note": "registration only, not admission or merge clearance"}


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--issues", required=True)
    p.add_argument("--lane", required=True)
    p.add_argument("--branch", required=True)
    args = p.parse_args()
    with open(args.issues, encoding="utf-8") as handle:
        issues = json.load(handle)
    print(json.dumps(plan(issues, args.lane, args.branch), sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, TypeError, KeyError, AttributeError) as exc:
        print("MHB-ATC Phase 2 stage denied: " + str(exc), file=sys.stderr)
        sys.exit(2)
