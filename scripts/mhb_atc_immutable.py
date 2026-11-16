#!/usr/bin/env python3
"""Pure SHA-bound MHB-ATC immutable PR-head/receipt/ruleset validation.

No GitHub API calls, no merge permissions, and no code from a staged branch.
The trusted workflow does each GitHub read/write and rechecks these contracts.
"""
from __future__ import annotations

import argparse
import datetime as dt
import json
import re
import sys
from pathlib import Path

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


def _load_owner_attestation() -> dict:
    """Reviewed, owner-authenticated ruleset attestation in the trusted main tree.

    The workflow token may see only a REDACTED ruleset. The live version stamp
    must exactly match the owner-reviewed version; every GitHub policy mutation
    invalidates the certificate and stops publication until a reviewed update.
    """
    path = Path(__file__).resolve().parents[1] / ".github/atc-publisher-policy.json"
    with path.open(encoding="utf-8") as fp:
        return json.load(fp)


def _timestamp(value) -> dt.datetime:
    if not isinstance(value, str):
        raise ValueError("ruleset timestamp absent")
    try:
        result = dt.datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError as exc:
        raise ValueError("invalid GitHub ruleset timestamp") from exc
    if result.tzinfo is None:
        raise ValueError("ruleset timestamp missing timezone")
    return result.astimezone(dt.timezone.utc)


def check_ruleset(rule: dict, repo: str, app_id: int, ruleset_id: int,
                  attestation: dict | None = None) -> dict:
    """Fail closed on a missing/changed live policy or unreviewed bypass.

    A low-privilege GITHUB_TOKEN need not see bypass_actors. In that case this
    validates GitHub's live updated_at and full unredacted trusted-main
    owner attestation; it never guesses who can bypass from visible fields.
    """
    if type(app_id) is not int or app_id < 1 or type(ruleset_id) is not int or ruleset_id < 1:
        raise ValueError("numeric App and ruleset IDs required")
    if not isinstance(rule, dict):
        raise ValueError("invalid ruleset response")
    policy = _load_owner_attestation() if attestation is None else attestation
    if (not isinstance(policy, dict) or
        policy.get("format") != "MHB-ATC-OWNER-RULESET-ATTESTATION-V1" or
        policy.get("repository") != repo or policy.get("ruleset_id") != ruleset_id or
        policy.get("publisher_app_id") != app_id or
        policy.get("attested_bypass_actors") != [{
            "actor_type": "Integration", "actor_id": app_id,
            "bypass_mode": "always"}]):
        raise ValueError("reviewed owner ruleset attestation missing or inconsistent")
    if (_timestamp(rule.get("created_at")) !=
        _timestamp(policy.get("ruleset_created_at")) or
        _timestamp(rule.get("updated_at")) !=
        _timestamp(policy.get("ruleset_updated_at"))):
        raise ValueError("live ruleset version differs from reviewed owner attestation")
    if rule.get("id") != ruleset_id or rule.get("target") != "branch" or rule.get("enforcement") != "active":
        raise ValueError("wrong/inactive ruleset")
    if rule.get("source_type") != "Repository" or rule.get("source") != repo:
        raise ValueError("ruleset not scoped to exact repository")
    conditions = rule.get("conditions")
    ref_name = conditions.get("ref_name") if isinstance(conditions, dict) else None
    if not isinstance(ref_name, dict) or ref_name.get("include") != [
        "refs/heads/hamster/admitted/*"] or ref_name.get("exclude") != []:
        raise ValueError("ruleset target must be exact admitted-ref namespace")
    rules = rule.get("rules")
    if not isinstance(rules, list) or not all(isinstance(x, dict) for x in rules):
        raise ValueError("malformed live ruleset rule list")
    types = {x.get("type") for x in rules}
    if not {"creation", "update", "deletion", "non_fast_forward"} <= types:
        raise ValueError("ruleset missing creation/update/delete or non-fast-forward protections")
    bypass = rule.get("bypass_actors")
    if bypass is not None and bypass != policy["attested_bypass_actors"]:
        raise ValueError("live bypass conflicts with reviewed owner attestation")
    if bypass is not None and not isinstance(bypass, list):
        raise ValueError("malformed live bypass actor list")
    return {"decision": "ruleset-preflight-valid", "ruleset_id": ruleset_id,
            "app_id": app_id, "namespace": ADMITTED_PREFIX,
            "evidence": ("unredacted-live-plus-version" if bypass is not None
                         else "redacted-live-plus-pinned-owner-version"),
            "pinned_updated_at": policy["ruleset_updated_at"]}

def verified_publisher(app: dict, bot: dict, slug: str, app_id: int) -> dict:
    """Require GitHub's authenticated App and bot-user identities to agree."""
    if (not isinstance(slug, str) or
        not re.fullmatch(r"[a-zA-Z0-9][a-zA-Z0-9-]*", slug) or
        type(app_id) is not int or app_id <= 0):
        raise ValueError("publisher App slug/id not configured")
    if (not isinstance(app, dict) or app.get("id") != app_id or
        app.get("slug") != slug):
        raise ValueError("publisher App slug does not resolve to pinned App ID")
    login = slug + "[bot]"
    if (not isinstance(bot, dict) or bot.get("login") != login or
        bot.get("type") != "Bot" or type(bot.get("id")) is not int or
        bot.get("id") <= 0):
        raise ValueError("publisher bot user identity missing or inconsistent")
    return {"app_id": app_id, "app_slug": slug,
            "bot_login": login, "bot_id": bot["id"]}


def verify_pr(pr: dict, binding: dict, publisher: dict) -> dict:
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
    if (not isinstance(publisher, dict) or
        type(publisher.get("app_id")) is not int or
        not isinstance(publisher.get("bot_login"), str) or
        type(publisher.get("bot_id")) is not int):
        raise ValueError("verified publisher identity is required")
    author = pr.get("user")
    if (not isinstance(author, dict) or
        author.get("login") != publisher["bot_login"] or
        author.get("id") != publisher["bot_id"] or
        author.get("type") != "Bot"):
        raise ValueError("PR was not created by the authenticated publisher bot")
    via = pr.get("performed_via_github_app")
    if via is not None and (not isinstance(via, dict) or
                            via.get("id") != publisher["app_id"]):
        raise ValueError("GitHub-reported PR App attribution contradicts publisher")
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
            s.add_argument("--publisher-json", required=True)
    s = sub.add_parser("publisher")
    s.add_argument("--app-json", required=True)
    s.add_argument("--bot-json", required=True)
    s.add_argument("--app-slug", required=True)
    s.add_argument("--app-id", type=int, required=True)
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
    elif args.command == "publisher":
        with open(args.app_json, encoding="utf-8") as f:
            app = json.load(f)
        with open(args.bot_json, encoding="utf-8") as f:
            bot = json.load(f)
        result = verified_publisher(app, bot, args.app_slug, args.app_id)
    else:
        binding = contract(args.issue, args.lane, args.staged, args.sha, args.repo)
        if args.command == "contract":
            result = binding
        elif args.command == "ref":
            with open(args.refs, encoding="utf-8") as f:
                result = check_ref(json.load(f), binding, args.expect)
        else:
            with open(args.pr_json, encoding="utf-8") as f:
                with open(args.publisher_json, encoding="utf-8") as identity_file:
                    publisher = json.load(identity_file)
                result = verify_pr(json.load(f), binding, publisher)
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, TypeError, AttributeError, KeyError,
            json.JSONDecodeError) as exc:
        print("MHB-ATC immutable admission denied: " + str(exc), file=sys.stderr)
        sys.exit(2)
