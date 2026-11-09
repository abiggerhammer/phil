#!/usr/bin/env python3
"""FSEM slice claims: atomic Git-ref acquisition; issue ledger; fail-closed PR guard.

The unique refs/heads/coord/fsem-claims/<slice> ref is the lock.  Its commit
contains .fsem-claim.json, with a predeclared PR branch. A commit is prepared
*before* creating the ref, so two contenders cannot both acquire the same
slice and there is never an incomplete live ref. GitHub issue comments are an
audit trail, not the lock. This does NOT implement MHB-ATC runner admission.
"""
from __future__ import annotations

import argparse
import base64
import datetime as dt
import json
import os
import re
import sys
import urllib.error
import urllib.parse
import urllib.request

REPO = "abiggerhammer/phil"
TRACKING_ISSUE = 1613
MARKER = "<!-- FSEM-SLICE-CLAIM-V1 -->"
RELEASE_MARKER = "<!-- FSEM-SLICE-RELEASE-V1 -->"
CLAIM_FILE = ".fsem-claim.json"
CLAIM_PREFIX = "refs/heads/coord/fsem-claims/"
SLICE_RE = re.compile(r"fsem-[0-9]{2}\Z")
BRANCH_RE = re.compile(r"formal-semantics/[a-z0-9][a-z0-9._/-]*\Z")
BODY_SLICE_RE = re.compile(r"(?im)^FSEM-Slice:\s*(fsem-[0-9]{2})\s*$")


class ClaimFailure(Exception):
    pass


class GitHub:
    def __init__(self, repo: str = REPO, token: str | None = None):
        self.repo = repo
        self.token = token or os.getenv("GH_TOKEN") or os.getenv("GITHUB_TOKEN")
        if not self.token:
            raise ClaimFailure("GH_TOKEN or GITHUB_TOKEN is required")

    def request(self, method: str, endpoint: str, payload: dict | None = None):
        url = "https://api.github.com/repos/" + self.repo + endpoint
        data = None if payload is None else json.dumps(payload).encode("utf-8")
        req = urllib.request.Request(
            url, data=data, method=method,
            headers={
                "Authorization": "Bearer " + self.token,
                "Accept": "application/vnd.github+json",
                "X-GitHub-Api-Version": "2022-11-28",
                "User-Agent": "phil-fsem-claim-v1",
                "Content-Type": "application/json",
            },
        )
        try:
            with urllib.request.urlopen(req, timeout=30) as response:
                raw = response.read()
                return json.loads(raw) if raw else None
        except urllib.error.HTTPError as exc:
            detail = exc.read().decode("utf-8", errors="replace")[:450]
            raise ClaimFailure(f"GitHub {method} {endpoint}: HTTP {exc.code}: {detail}") from exc
        except urllib.error.URLError as exc:
            raise ClaimFailure(f"GitHub unreachable: {exc}") from exc

    def pages(self, endpoint: str):
        # Fail closed when lists cannot be fully read. No stale, truncated snapshot.
        page = 1
        while True:
            join = "&" if "?" in endpoint else "?"
            items = self.request("GET", f"{endpoint}{join}per_page=100&page={page}")
            if not isinstance(items, list):
                raise ClaimFailure("unexpected paginated GitHub response")
            yield from items
            if len(items) < 100:
                return
            page += 1
            if page > 100:
                raise ClaimFailure("GitHub pagination limit exceeded")


def validate_slice(value: str) -> str:
    if not SLICE_RE.fullmatch(value):
        raise ClaimFailure("slice must be a canonical family key, e.g. fsem-01")
    return value


def validate_branch(value: str) -> str:
    if not BRANCH_RE.fullmatch(value) or "//" in value or value.endswith(("/", ".", ".lock")):
        raise ClaimFailure("branch must be a valid formal-semantics/<slug> source branch")
    if ".." in value or "@{" in value or ".git" in value:
        raise ClaimFailure("unsafe branch name")
    return value


def claim_ref(slice_key: str) -> str:
    return CLAIM_PREFIX + validate_slice(slice_key)


def slice_of_pr(pr: dict) -> str | None:
    body = pr.get("body") or ""
    found = BODY_SLICE_RE.search(body)
    if found:
        return found.group(1)
    title = pr.get("title") or ""
    inferred = re.match(r"(?i)^FSEM[- ]0*([0-9]{1,2})\b", title)
    if inferred:
        return f"fsem-{int(inferred.group(1)):02d}"
    return None


def has_lane(pr: dict) -> bool:
    labels = pr.get("labels", [])
    if not isinstance(labels, list):
        raise ClaimFailure("malformed PR labels")
    return any(isinstance(x, dict) and x.get("name") == "lane: formal-semantics"
               for x in labels)


def conflicts(prs: list, slice_key: str) -> list[int]:
    conflicts_found = []
    for pr in prs:
        if pr.get("state") != "open":
            continue
        head = pr.get("head", {})
        branch = head.get("ref", "") if isinstance(head, dict) else ""
        if not (has_lane(pr) or branch.startswith("formal-semantics/")):
            continue
        explicit = slice_of_pr(pr)
        # An active formal-semantics PR without a declared family is ambiguous;
        # do not assume it cannot touch the same semantic interface.
        if explicit in (None, slice_key):
            number = pr.get("number")
            if type(number) is not int:
                raise ClaimFailure("malformed PR number")
            conflicts_found.append(number)
    return conflicts_found


def make_claim(slice_key: str, branch: str, actor: str, main_sha: str) -> dict:
    validate_slice(slice_key)
    validate_branch(branch)
    if not actor or len(actor) > 128 or "\n" in actor:
        raise ClaimFailure("provide a concise, nonempty --actor for accountability")
    return {
        "version": 1, "slice": slice_key, "lane": "formal-semantics",
        "issue": TRACKING_ISSUE, "branch": branch, "actor": actor,
        "main_sha": main_sha,
        "claimed_at": dt.datetime.now(dt.timezone.utc).isoformat(),
    }


def claim_comment(record: dict, commit_sha: str) -> str:
    metadata = dict(record, claim_commit=commit_sha)
    return (
        f"{MARKER}\n"
        f"**Claimed:** `{record['slice']}` by `{record['actor']}` "
        f"for branch `{record['branch']}`. Claim ref: `{claim_ref(record['slice'])}`.\n"
        "This is a reservation, **not** a PR merge or a proof result.\n"
        "\n```json\n" + json.dumps(metadata, sort_keys=True) + "\n```\n"
    )


def recorded_claims(comments: list) -> list[dict]:
    found = []
    for comment in comments:
        body = comment.get("body") or ""
        if not body.startswith(MARKER):
            continue
        match = re.search(r"```json\n(\{[^\n]*\})\n```", body)
        if not match:
            raise ClaimFailure("malformed FSEM claim audit comment")
        record = json.loads(match.group(1))
        if not isinstance(record, dict):
            raise ClaimFailure("malformed claim audit JSON")
        found.append(record)
    return found


def live_claim(api: GitHub, slice_key: str) -> tuple[dict, str]:
    ref = claim_ref(slice_key)
    # 'git/ref/heads/...' uses path segments with the full nested ref tail.
    detail = api.request("GET", "/git/ref/" + ref.removeprefix("refs/"))
    if not isinstance(detail, dict):
        raise ClaimFailure("malformed claim ref")
    obj = detail.get("object")
    sha = obj.get("sha") if isinstance(obj, dict) else None
    if not isinstance(sha, str) or not re.fullmatch(r"[0-9a-f]{40}", sha):
        raise ClaimFailure("malformed claim ref SHA")
    # Read the record from the immutable SHA we just looked up, not from a
    # potentially moved branch name between API calls.
    query = urllib.parse.quote(sha, safe="")
    item = api.request("GET", "/contents/" + CLAIM_FILE + "?ref=" + query)
    if not isinstance(item, dict) or item.get("encoding") != "base64":
        raise ClaimFailure("claim ref missing machine-readable record")
    try:
        record = json.loads(base64.b64decode(item["content"]))
    except (KeyError, ValueError) as exc:
        raise ClaimFailure("invalid claim record") from exc
    required = {"version", "slice", "lane", "issue", "branch", "actor",
                "main_sha", "claimed_at"}
    if not isinstance(record, dict) or set(record) != required:
        raise ClaimFailure("unknown/incomplete claim schema")
    if (record["version"] != 1 or record["slice"] != slice_key or
            record["lane"] != "formal-semantics" or record["issue"] != TRACKING_ISSUE):
        raise ClaimFailure("wrong claim identity/version")
    validate_branch(record["branch"])
    return record, sha


def require_issue_record(api: GitHub, record: dict, sha: str):
    comments = list(api.pages(f"/issues/{TRACKING_ISSUE}/comments"))
    matches = [x for x in recorded_claims(comments)
               if x.get("claim_commit") == sha and
               all(x.get(k) == v for k, v in record.items())]
    if len(matches) != 1:
        raise ClaimFailure("exact claim not recorded once in tracking issue #1613")


def acquire(api: GitHub, slice_key: str, branch: str, actor: str):
    validate_slice(slice_key)
    validate_branch(branch)
    existing = conflicts(list(api.pages("/pulls?state=open")), slice_key)
    if existing:
        raise ClaimFailure(f"open formal-semantics PR(s) {existing} still own/overlap this slice")
    main = api.request("GET", "/git/ref/heads/main")
    base_sha = main["object"]["sha"]
    base_commit = api.request("GET", "/git/commits/" + base_sha)
    record = make_claim(slice_key, branch, actor, base_sha)
    tree = api.request("POST", "/git/trees", {
        "base_tree": base_commit["tree"]["sha"],
        "tree": [{"path": CLAIM_FILE, "mode": "100644", "type": "blob",
                  "content": json.dumps(record, sort_keys=True) + "\n"}]
    })
    commit = api.request("POST", "/git/commits", {
        "message": f"coord: claim {slice_key} for {branch}",
        "tree": tree["sha"], "parents": [base_sha]
    })
    # ATOMIC CLAIM: create the unique ref. HTTP 422 means somebody else won.
    api.request("POST", "/git/refs", {"ref": claim_ref(slice_key), "sha": commit["sha"]})
    print(f"Claim ref acquired: {claim_ref(slice_key)} @ {commit['sha']}")
    # If the comment fails, the ref remains locked and verification fails closed.
    # Retry 'announce' (not 'acquire') to restore its missing audit comment.
    api.request("POST", f"/issues/{TRACKING_ISSUE}/comments",
                {"body": claim_comment(record, commit["sha"])})
    print(f"Recorded claim in issue #{TRACKING_ISSUE}; PR body needs FSEM-Slice: {slice_key}")


def announce(api: GitHub, slice_key: str):
    record, sha = live_claim(api, slice_key)
    comments = list(api.pages(f"/issues/{TRACKING_ISSUE}/comments"))
    existing = [c for c in recorded_claims(comments)
                if c.get("claim_commit") == sha]
    if existing:
        require_issue_record(api, record, sha)
        print("Matching audit comment already recorded")
        return
    api.request("POST", f"/issues/{TRACKING_ISSUE}/comments",
                {"body": claim_comment(record, sha)})
    print("Restored missing audit comment")


def verify(api: GitHub, number: int):
    pr = api.request("GET", f"/pulls/{number}")
    if pr.get("state") != "open":
        raise ClaimFailure("PR is not open")
    head = pr.get("head") or {}
    branch = head.get("ref", "")
    if not (has_lane(pr) and branch.startswith("formal-semantics/")):
        raise ClaimFailure("formal-semantics claim requires lane label and branch prefix")
    if (head.get("repo") or {}).get("full_name") != api.repo:
        raise ClaimFailure("cross-repository head is not supported")
    match = BODY_SLICE_RE.search(pr.get("body") or "")
    if not match:
        raise ClaimFailure("PR description missing exact 'FSEM-Slice: fsem-XX' line")
    slice_key = match.group(1)
    if slice_of_pr(pr) != slice_key:
        raise ClaimFailure("PR family does not match stated slice")
    record, sha = live_claim(api, slice_key)
    if record["branch"] != branch:
        raise ClaimFailure(f"slice already claimed by branch {record['branch']}")
    started = dt.datetime.fromisoformat(record["claimed_at"])
    opened = dt.datetime.fromisoformat(pr["created_at"].replace("Z", "+00:00"))
    if started > opened:
        raise ClaimFailure("claim must predate opening this PR (no retroactive claim)")
    require_issue_record(api, record, sha)
    competing = [x for x in conflicts(list(api.pages("/pulls?state=open")), slice_key)
                 if x != number]
    if competing:
        raise ClaimFailure(f"competing open PR(s) in same slice: {competing}")
    print(f"PASS: PR #{number} owns {slice_key} via {claim_ref(slice_key)} @ {sha}")


def abort_unopened(api: GitHub, slice_key: str, actor: str):
    """Explicitly abandon a claim that has no open PR; never time-expire it."""
    record, sha = live_claim(api, slice_key)
    if record["actor"] != actor:
        raise ClaimFailure("only the recorded claimant may request normal abandonment")
    competitors = conflicts(list(api.pages("/pulls?state=open")), slice_key)
    if competitors:
        raise ClaimFailure(f"open PR(s) {competitors}: close the PR before release")
    require_issue_record(api, record, sha)
    api.request("DELETE", "/git/refs/" + claim_ref(slice_key).removeprefix("refs/"))
    api.request("POST", f"/issues/{TRACKING_ISSUE}/comments", {
        "body": (f"{RELEASE_MARKER}\nAbandoned unopened `{slice_key}` "
                 f"claim `{sha}` by `{actor}`; no PR was open.")
    })
    print(f"Abandoned unopened {slice_key} claim")


def release(api: GitHub, number: int, *, expected_sha: str | None = None,
            require_merged: bool = False):
    """Release a closed PR's exact claim; recovery additionally requires a merge.

    Never trust only a close-event payload or a previously observed claim SHA.
    The live record, tracking-issue audit, PR and competing PRs are all read
    again immediately before deleting the uniquely named family ref.
    """
    pr = api.request("GET", f"/pulls/{number}")
    if pr.get("state") != "closed":
        raise ClaimFailure("release requires a CLOSED PR (merged or abandoned)")
    head = pr.get("head") or {}
    if (not has_lane(pr) or
            (head.get("repo") or {}).get("full_name") != api.repo or
            not head.get("ref", "").startswith("formal-semantics/")):
        raise ClaimFailure("closed claim PR needs exact lane and same-repo source branch")
    if require_merged and not pr.get("merged_at"):
        raise ClaimFailure("automatic recovery requires a MERGED PR")
    match = BODY_SLICE_RE.search(pr.get("body") or "")
    if not match:
        raise ClaimFailure("closed PR missing FSEM-Slice declaration")
    slice_key = match.group(1)
    record, sha = live_claim(api, slice_key)
    if expected_sha is not None and sha != expected_sha:
        raise ClaimFailure("claim SHA changed since recovery was authorized")
    if record["branch"] != head.get("ref"):
        raise ClaimFailure("claim belongs to another branch; refuse release")
    claimed = dt.datetime.fromisoformat(record["claimed_at"])
    opened = dt.datetime.fromisoformat(pr["created_at"].replace("Z", "+00:00"))
    if claimed > opened:
        raise ClaimFailure("claim postdates this PR; refuse stale close-event release")
    require_issue_record(api, record, sha)
    competitors = conflicts(list(api.pages("/pulls?state=open")), slice_key)
    if competitors:
        raise ClaimFailure(
            f"open same-family/unclassified PR(s) {competitors}; refuse release")
    # Re-read the exact ref before deletion. GitHub's delete-ref endpoint
    # offers no conditional SHA argument, so this is fail-closed preflight
    # under the protocol's rule against out-of-band ref writes.
    path = claim_ref(slice_key).removeprefix("refs/")
    current = api.request("GET", "/git/ref/" + path)
    if (not isinstance(current, dict) or
            (current.get("object") or {}).get("sha") != sha):
        raise ClaimFailure("claim ref changed during release preflight")
    api.request("DELETE", "/git/refs/" + path)
    api.request("POST", f"/issues/{TRACKING_ISSUE}/comments", {
        "body": (f"{RELEASE_MARKER}\nReleased `{slice_key}` claim `{sha}` "
                 f"after [PR #{number}](https://github.com/{api.repo}/pull/{number}) "
                 "closed. This says nothing about proof or merge quality.")
    })
    print(f"Released {slice_key} after PR #{number} closed")


def reconcile(api: GitHub):
    """Recover merged-but-still-claimed slices after lost close-event jobs.

    Only a unique merged PR on the declared branch, opened after the
    immutable claim, can be considered. Open or abandoned claims are left
    alone. Every candidate is rechecked by release() before deletion.
    """
    refs = list(api.pages("/git/matching-refs/heads/coord/fsem-claims/"))
    seen = set()
    released = []
    for item in refs:
        ref = item.get("ref") if isinstance(item, dict) else None
        if not isinstance(ref, str) or not ref.startswith(CLAIM_PREFIX):
            raise ClaimFailure("unexpected FSEM claim listing entry")
        slice_key = validate_slice(ref[len(CLAIM_PREFIX):])
        if slice_key in seen:
            raise ClaimFailure("duplicate claim ref in recovery snapshot")
        seen.add(slice_key)
        record, sha = live_claim(api, slice_key)
        if (item.get("object") or {}).get("sha") != sha:
            raise ClaimFailure("claim moved during recovery snapshot")
        head = api.repo.split("/", 1)[0] + ":" + record["branch"]
        endpoint = "/pulls?state=closed&head=" + urllib.parse.quote(head, safe="")
        merged = []
        claimed_at = dt.datetime.fromisoformat(record["claimed_at"])
        for pr in api.pages(endpoint):
            pr_head = pr.get("head") or {}
            if (pr.get("state") != "closed" or not pr.get("merged_at") or
                    pr_head.get("ref") != record["branch"] or
                    (pr_head.get("repo") or {}).get("full_name") != api.repo or
                    not has_lane(pr)):
                continue
            match = BODY_SLICE_RE.search(pr.get("body") or "")
            if not match or match.group(1) != slice_key:
                continue
            created = dt.datetime.fromisoformat(
                pr["created_at"].replace("Z", "+00:00"))
            if created < claimed_at:
                continue
            if type(pr.get("number")) is not int:
                raise ClaimFailure("malformed candidate PR number")
            merged.append(pr["number"])
        if len(merged) > 1:
            raise ClaimFailure(
                f"ambiguous merged PRs for {slice_key} claim {sha}: {merged}")
        if not merged:
            print(f"Retaining {slice_key} @ {sha}: no unique matching merged PR")
            continue
        release(api, merged[0], expected_sha=sha, require_merged=True)
        released.append((slice_key, merged[0], sha))
    print(f"Recovery complete; released {len(released)} exact merged claims")
    return released


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("acquire", "announce", "verify", "release", "abort",
                                        "recover", "reconcile"))
    parser.add_argument("--slice", dest="slice_key")
    parser.add_argument("--branch")
    parser.add_argument("--actor")
    parser.add_argument("--pr", type=int)
    parser.add_argument("--expected-claim-sha")
    parser.add_argument("--repo", default=REPO)
    args = parser.parse_args(argv)
    try:
        api = GitHub(repo=args.repo)
        if args.command == "acquire":
            if not args.slice_key or not args.branch or not args.actor:
                raise ClaimFailure("acquire needs --slice, --branch and --actor")
            acquire(api, args.slice_key, args.branch, args.actor)
        elif args.command == "announce":
            if not args.slice_key:
                raise ClaimFailure("announce needs --slice")
            announce(api, args.slice_key)
        elif args.command == "abort":
            if not args.slice_key or not args.actor:
                raise ClaimFailure("abort needs --slice and --actor")
            abort_unopened(api, args.slice_key, args.actor)
        elif args.command == "reconcile":
            reconcile(api)
        elif args.command == "recover":
            if (not args.pr or args.pr < 1 or
                    not args.expected_claim_sha or
                    not re.fullmatch(r"[0-9a-f]{40}", args.expected_claim_sha)):
                raise ClaimFailure(
                    "recover needs --pr NUMBER and --expected-claim-sha SHA40")
            release(api, args.pr, expected_sha=args.expected_claim_sha,
                    require_merged=True)
        else:
            if not args.pr or args.pr < 1:
                raise ClaimFailure(f"{args.command} needs --pr NUMBER")
            (verify if args.command == "verify" else release)(api, args.pr)
        return 0
    except ClaimFailure as exc:
        print(f"FSEM claim denied: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
