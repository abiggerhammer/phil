#!/usr/bin/env python3
"""Complete immutable-ref namespace census; fail closed on *every* unknown ref.

Read-only planner. The trusted-main snapshot shell fetches every canonical
ref's issue (even if closed/unlabelled) and every associated open/closed PR.
No issue lifecycle label is trusted to enumerate the protected namespace.
"""
from __future__ import annotations

import argparse
import json
import re
import sys

from mhb_atc_immutable import contract, verified_publisher, verify_pr

PREFIX = "refs/heads/hamster/admitted/"
ADMITTED = re.compile(r"atc-([1-9][0-9]*)-([a-z][a-z0-9-]*)-([0-9a-f]{40})\Z")
SHA = re.compile(r"[0-9a-f]{40}\Z")
STATES = {"atc: staged", "atc: admitting", "atc: admitted"}


def enumerate_refs(refs: list) -> list[dict]:
    """Parse every GitHub ref from the prefix listing (never ignore unknown)."""
    if not isinstance(refs, list):
        raise ValueError("complete protected-ref list required")
    found = []
    names = set()
    for raw in refs:
        if not isinstance(raw, dict) or not isinstance(raw.get("ref"), str):
            raise ValueError("malformed protected ref record")
        name = raw["ref"]
        if not name.startswith(PREFIX):
            # GitHub list-matching-refs is a PREFIX search. Querying
            # heads/hamster/admitted may also return 'admitted-other' or
            # the branch named 'admitted' itself; neither matches our
            # protected slash-delimited ruleset namespace. Ignore only
            # such outside-prefix siblings, NOT unknown refs under PREFIX.
            if name.startswith(PREFIX.removesuffix("/")):
                continue
            raise ValueError("unexpected branch returned by admitted-ref census")
        match = ADMITTED.fullmatch(name.removeprefix(PREFIX))
        if match is None:
            raise ValueError("unknown noncanonical branch in protected admitted namespace")
        if name in names:
            raise ValueError("duplicate protected ref returned")
        names.add(name)
        obj = raw.get("object")
        sha = obj.get("sha") if isinstance(obj, dict) else None
        if (not isinstance(sha, str) or not SHA.fullmatch(sha)
                or sha != match.group(3)):
            raise ValueError("protected ref SHA differs from encoded exact SHA")
        found.append({"branch": name.removeprefix("refs/heads/"),
                      "issue": int(match.group(1)), "lane": match.group(2),
                      "head_sha": sha})
    return sorted(found, key=lambda e: e["branch"])


def validate_inventory(refs: list, issues: list, prs: list,
                       repo: str, publisher: dict) -> dict:
    """Accept only genuine closed history or authenticated active admissions."""
    from mhb_atc_admit import machine_record, names, TRUSTED_CREATOR

    entries = enumerate_refs(refs)
    if not isinstance(issues, list) or not isinstance(prs, list):
        raise ValueError("missing complete protected issue/PR lookups")
    issue_map: dict[int, dict] = {}
    for issue in issues:
        if (not isinstance(issue, dict) or
            type(issue.get("number")) is not int or
            issue.get("state") not in ("open", "closed") or
            issue["number"] in issue_map):
            raise ValueError("invalid or duplicated census issue")
        issue_map[issue["number"]] = issue
    pr_by_ref: dict[str, list[dict]] = {x["branch"]: [] for x in entries}
    for pr in prs:
        if (not isinstance(pr, dict) or not isinstance(pr.get("head"), dict)
            or pr["head"].get("ref") not in pr_by_ref):
            raise ValueError("unmatched or malformed census PR")
        pr_by_ref[pr["head"]["ref"]].append(pr)
    if set(issue_map) != {e["issue"] for e in entries}:
        raise ValueError("protected issue snapshot incomplete or unrelated")
    history, active = [], []
    for entry in entries:
        issue = issue_map[entry["issue"]]
        if (issue.get("user", {}).get("login") != TRUSTED_CREATOR or
            "pull_request" in issue or
            issue.get("title") is None):
            raise ValueError("protected ref points to noncanonical/untrusted issue")
        record = machine_record(issue)
        if (issue["title"] != "ATC candidate: " + record["branch"] or
            record["lane"] != entry["lane"] or
            record["head_sha"] != entry["head_sha"]):
            raise ValueError("original staged issue identity disagrees with admitted ref")
        bound = contract(entry["issue"], entry["lane"], record["branch"],
                         entry["head_sha"], repo)
        if bound["admitted_branch"] != entry["branch"]:
            raise ValueError("protected ref does not match candidate binding")
        matches = pr_by_ref[entry["branch"]]
        if len(matches) != 1:
            raise ValueError("unresolved orphan or duplicate protected-ref PR")
        verify_pr(matches[0], bound, publisher)
        labels = STATES & names(issue)
        if issue["state"] == "open":
            if len(labels) != 1 or labels == {"atc: staged"}:
                raise ValueError("open protected admission has no single valid reservation")
            active.append({"issue": entry["issue"], "pr": matches[0]["number"],
                           "pr_state": matches[0]["state"], "ref": entry["branch"]})
        elif matches[0]["state"] == "closed":
            history.append({"issue": entry["issue"], "pr": matches[0]["number"],
                            "ref": entry["branch"]})
        else:
            raise ValueError("closed issue has an open protected PR")
    return {"decision": "inventory-validated",
            "active_refs": active, "closed_history": history,
            "total_refs": len(entries),
            "admission_clear": not active}


def _load(path: str):
    with open(path, encoding="utf-8") as fp:
        return json.load(fp)


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--refs", required=True)
    p.add_argument("--repo")
    p.add_argument("--issues")
    p.add_argument("--prs")
    p.add_argument("--publisher-json")
    p.add_argument("--list", action="store_true",
                   help="print all canonical ref issue/branch pairs for GitHub lookups")
    args = p.parse_args()
    refs = _load(args.refs)
    if args.list:
        result = enumerate_refs(refs)
    else:
        if not all((args.repo, args.issues, args.prs, args.publisher_json)):
            raise ValueError("inventory validation needs all snapshot inputs")
        result = validate_inventory(refs, _load(args.issues), _load(args.prs),
                                    args.repo, _load(args.publisher_json))
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, TypeError, KeyError, AttributeError, OSError,
            json.JSONDecodeError) as exc:
        print("MHB-ATC full protected namespace denied: " + str(exc), file=sys.stderr)
        sys.exit(2)
