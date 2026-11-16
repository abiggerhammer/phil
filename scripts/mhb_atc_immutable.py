#!/usr/bin/env python3
"""Pure SHA-bound MHB-ATC immutable PR-head/receipt/ruleset validation.

No GitHub API calls, no merge permissions, and no code from a staged branch.
The trusted workflow does each GitHub read/write and rechecks these contracts.
"""
from __future__ import annotations

import argparse
import json
import re
import sys

from mhb_atc_stage import parse_intent

ADMITTED_PREFIX = "hamster/admitted/"
RULESET_PATTERNS = {"refs/heads/hamster/admitted/*", "hamster/admitted/*"}
SHA = re.compile(r"[a-f0-9]{40}\Z")
REPO = re.compile(r"[a-zA-Z0-9_.-]+/[a-zA-Z0-9_.-]+\Z")


def contract(issue: int, lane: str, staged: str, sha: str, repo: str) -> dict:
    if type(issue) is not int or issue < 1 or not isinstance(repo, str) or not REPO.fullmatch(repo):
        raise ValueError("invalid candidate number or repository")
    if not isinstance(sha, str) or not SHA.fullmatch(sha):
        raise ValueError("invalid exact SHA")
    parsed = parse_intent(staged, sha, sha)
    if parsed["lane"] != lane:
        raise ValueError("lane does not match staged branch")
    admitted = f"{ADMITTED_PREFIX}atc-{issue}-{lane}-{sha}"
    title = f"MHB-ATC immutable admission: {lane} / {issue}"
    body = "\n".join([
        "MHB-ATC admitted immutable exact-head candidate; this PR is **not** merge clearance.",
        "",
        f"- Candidate issue: #{issue}",
        f"- Lane: {lane}",
        f"- Staged branch: {staged}",
        f"- Admitted branch: {admitted}",
        f"- Exact registered head: {sha}",
        f"- Base repository: {repo}",
        "- Base branch: main",
        "- Publisher: dedicated MHB-ATC GitHub App",
        "",
        "Required CI checks and independent merge clearance remain mandatory.",
        "",
    ])
    return {"candidate_issue": issue, "lane": lane, "staged_branch": staged,
            "admitted_branch": admitted, "head_sha": sha, "repo": repo,
            "title": title, "body": body}


def github_ref_sha(refs: list, branch: str) -> str | None:
    if not isinstance(refs, list):
        raise ValueError("incomplete admitted-ref snapshot")
    target = "refs/heads/" + branch
    seen = []
    for entry in refs:
        if not isinstance(entry, dict) or not isinstance(entry.get("ref"), str):
            raise ValueError("malformed Git ref entry")
        if entry["ref"] != target:
            continue
        obj = entry.get("object")
        sha = obj.get("sha") if isinstance(obj, dict) else None
        if not isinstance(sha, str) or not SHA.fullmatch(sha):
            raise ValueError("malformed admitted-ref object")
        seen.append(sha)
    if len(seen) > 1:
        raise ValueError("duplicate admitted refs")
    return seen[0] if seen else None


def check_ref(refs: list, binding: dict, expected: str) -> dict:
    if expected not in ("absent", "present"):
        raise ValueError("invalid required ref state")
    sha = github_ref_sha(refs, binding["admitted_branch"])
    if expected == "absent" and sha is not None:
        raise ValueError("admitted ref already exists: orphan/reuse blocked")
    if expected == "present" and sha != binding["head_sha"]:
        raise ValueError("missing or drifted admitted ref SHA")
    return {"decision": "admitted-ref-validated", "state": expected,
            "admitted_branch": binding["admitted_branch"],
            "head_sha": binding["head_sha"]}


def check_ruleset(rule: dict, repo: str, app_id: int, ruleset_id: int) -> dict:
    """A conservative preflight, not a substitute for negative write tests."""
    if type(app_id) is not int or app_id < 1 or type(ruleset_id) is not int or ruleset_id < 1:
        raise ValueError("numeric App and ruleset IDs required")
    if not isinstance(rule, dict):
        raise ValueError("invalid ruleset response")
    if rule.get("id") != ruleset_id or rule.get("target") != "branch" or rule.get("enforcement") != "active":
        raise ValueError("wrong/inactive ruleset")
    if rule.get("source_type") != "Repository" or rule.get("source") != repo:
        raise ValueError("ruleset not scoped to exact repository")
    conditions = rule.get("conditions")
    ref_name = conditions.get("ref_name") if isinstance(conditions, dict) else None
    if not isinstance(ref_name, dict) or set(ref_name.get("include", [])) not in (
        {"refs/heads/hamster/admitted/*"}, {"hamster/admitted/*"}
    ) or ref_name.get("exclude") != []:
        raise ValueError("ruleset target must be the exact single-level admitted-ref namespace")
    types = {x.get("type") for x in rule.get("rules", []) if isinstance(x, dict)}
    if not {"creation", "update", "deletion", "non_fast_forward"} <= types:
        raise ValueError("ruleset missing creation/update/delete or non-fast-forward protections")
    bypass = rule.get("bypass_actors")
    if (not isinstance(bypass, list) or len(bypass) != 1 or
        bypass[0].get("actor_type") != "Integration" or
        bypass[0].get("actor_id") != app_id or
        bypass[0].get("bypass_mode") != "always"):
        raise ValueError("ruleset bypass must be only the dedicated publisher App")
    return {"decision": "ruleset-preflight-valid", "ruleset_id": ruleset_id,
            "app_id": app_id, "namespace": ADMITTED_PREFIX}


def verify_pr(pr: dict, binding: dict) -> dict:
    if not isinstance(pr, dict) or pr.get("state") not in ("open", "closed"):
        raise ValueError("bad PR state")
    head, base = pr.get("head"), pr.get("base")
    if not isinstance(head, dict) or not isinstance(base, dict):
        raise ValueError("PR branch information absent")
    hrepo, brepo = head.get("repo"), base.get("repo")
    if not isinstance(hrepo, dict) or not isinstance(brepo, dict):
        raise ValueError("PR repository information absent")
    if (head.get("ref") != binding["admitted_branch"] or
        head.get("sha") != binding["head_sha"] or
        hrepo.get("full_name") != binding["repo"] or
        base.get("ref") != "main" or brepo.get("full_name") != binding["repo"]):
        raise ValueError("PR immutable head/base/repository mismatch")
    if pr.get("title") != binding["title"]:
        raise ValueError("PR canonical title mismatch")
    if not isinstance(pr.get("body"), str) or pr["body"].rstrip("\n") != binding["body"].rstrip("\n"):
        raise ValueError("PR checked publisher receipt mismatch")
    if type(pr.get("number")) is not int or pr["number"] < 1:
        raise ValueError("bad PR number")
    return {"decision": "immutable-pr-validated", "pr": pr["number"],
            "admitted_branch": binding["admitted_branch"],
            "head_sha": binding["head_sha"]}


def _args():
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest="command", required=True)
    for name in ("contract", "ref", "verify-pr"):
        s = sub.add_parser(name)
        s.add_argument("--issue", type=int, required=True)
        s.add_argument("--lane", required=True)
        s.add_argument("--staged", required=True)
        s.add_argument("--sha", required=True)
        s.add_argument("--repo", required=True)
        if name == "ref":
            s.add_argument("--refs", required=True)
            s.add_argument("--expect", choices=["absent", "present"], required=True)
        if name == "verify-pr":
            s.add_argument("--pr-json", required=True)
    s = sub.add_parser("ruleset")
    s.add_argument("--ruleset-json", required=True)
    s.add_argument("--repo", required=True)
    s.add_argument("--app-id", type=int, required=True)
    s.add_argument("--ruleset-id", type=int, required=True)
    return p.parse_args()


def main() -> int:
    args = _args()
    if args.command == "ruleset":
        with open(args.ruleset_json, encoding="utf-8") as f:
            result = check_ruleset(json.load(f), args.repo, args.app_id, args.ruleset_id)
    else:
        binding = contract(args.issue, args.lane, args.staged, args.sha, args.repo)
        if args.command == "contract":
            result = binding
        elif args.command == "ref":
            with open(args.refs, encoding="utf-8") as f:
                result = check_ref(json.load(f), binding, args.expect)
        else:
            with open(args.pr_json, encoding="utf-8") as f:
                result = verify_pr(json.load(f), binding)
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, TypeError, AttributeError, KeyError,
            json.JSONDecodeError) as exc:
        print("MHB-ATC immutable admission denied: " + str(exc), file=sys.stderr)
        sys.exit(2)
