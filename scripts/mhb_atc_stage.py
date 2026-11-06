#!/usr/bin/env python3
"""Validate an opt-in MHB-ATC staging intent; pure, no GitHub mutations.

Candidate registration occurs in a trusted main-branch repository_dispatch
workflow, not in code loaded from a hamster's staged working branch.
"""
from __future__ import annotations

import argparse
import json
import re
import sys

SHA = re.compile(r"[0-9a-f]{40}\Z")
LANE = re.compile(r"[a-z][a-z0-9-]*\Z")
SEGMENT = re.compile(r"[a-zA-Z0-9][a-zA-Z0-9._-]*\Z")
PREFIX = "hamster/staged/"
MARKER = "<!-- MHB-ATC-STAGED-V1 -->"


def parse_intent(branch: str, head_sha: str, live_sha: str) -> dict[str, str]:
    """Reject malformed/mismatched identities before producing an issue record."""
    if not branch.startswith(PREFIX) or len(branch) > 240:
        raise ValueError("branch must be within hamster/staged/")
    parts = branch.removeprefix(PREFIX).split("/")
    if len(parts) < 2 or len(parts) > 10:
        raise ValueError("branch must identify a lane and one or more name segments")
    if not LANE.fullmatch(parts[0]):
        raise ValueError("invalid lane identifier")
    if any(not SEGMENT.fullmatch(p) or p in (".", "..")
           or p.endswith(".lock") for p in parts[1:]):
        raise ValueError("invalid or unsafe branch path segment")
    if not SHA.fullmatch(head_sha) or not SHA.fullmatch(live_sha):
        raise ValueError("invalid exact SHA")
    if head_sha != live_sha:
        raise ValueError("stale candidate head: requested revision is not live")
    lane = parts[0]
    title = "ATC candidate: " + branch
    machine = {
        "version": 1,
        "lane": lane,
        "branch": branch,
        "head_sha": head_sha,
    }
    body = (
        f"{MARKER}\n"
        "This is a **staged candidate**, not an admitted PR or merge approval.\n"
        "The issue creation time is the durable enqueue time; updates keep it.\n"
        "The branch SHA must be checked again immediately before admission.\n\n"
        "Machine record (do not edit without the ATC controller):\n"
        + "~~~json\n" + json.dumps(machine, sort_keys=True, indent=2) + "\n~~~\n"
    )
    return {"title": title, "body": body, "lane": lane,
            "branch": branch, "head_sha": head_sha}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--branch", required=True)
    parser.add_argument("--head-sha", required=True)
    parser.add_argument("--live-sha", required=True)
    args = parser.parse_args()
    print(json.dumps(parse_intent(args.branch, args.head_sha, args.live_sha),
                     sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except ValueError as exc:
        print(f"MHB-ATC staging denied: {exc}", file=sys.stderr)
        sys.exit(2)
