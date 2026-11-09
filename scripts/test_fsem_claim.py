#!/usr/bin/env python3
"""Offline, deterministic regression tests for FSEM claim CAS and PR guard."""
import base64
import json
import pathlib
import urllib.parse
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import fsem_claim as f


SHA_MAIN = "a" * 40
SHA_CLAIM = "b" * 40
ISSUE = f.TRACKING_ISSUE
BRANCH = "formal-semantics/fsem01-next-proof"


def pr(number=99, branch=BRANCH, slice_key="fsem-01", state="open",
       created="2099-01-01T00:00:00Z", title="FSEM-01: next proof",
       merged_at=None):
    return {"number": number, "state": state, "merged_at": merged_at,
        "base": {"ref": "main", "repo": {"full_name": f.REPO}}, "head": {
        "ref": branch, "repo": {"full_name": f.REPO}},
        "created_at": created, "title": title,
        "labels": [{"name": "lane: formal-semantics"}],
        "body": f"FSEM-Slice: {slice_key}\nIssue: #{ISSUE}"}


class FakeGitHub:
    repo = f.REPO

    def __init__(self):
        self.refs = {}
        self.rec = None
        self.commits = {}
        self.comments = []
        self.prs = []
        self.deleted = []
        self.calls = []

    def pages(self, endpoint):
        if endpoint.startswith("/git/matching-refs/heads/coord/fsem-claims/"):
            return iter({"ref": key, "object": {"sha": sha}}
                        for key, sha in sorted(self.refs.items()))
        if endpoint.startswith("/pulls?state=closed&head="):
            head = urllib.parse.unquote(endpoint.partition("&head=")[2])
            _, branch = head.split(":", 1)
            return iter(x for x in self.prs if
                        x["state"] == "closed" and x["head"]["ref"] == branch)
        if endpoint.startswith("/pulls?"):
            return iter(self.prs)
        if endpoint == f"/issues/{ISSUE}/comments":
            return iter(self.comments)
        raise AssertionError(endpoint)

    def request(self, method, endpoint, payload=None):
        self.calls.append((method, endpoint))
        if method == "GET" and endpoint == "/git/ref/heads/main":
            return {"object": {"sha": SHA_MAIN}}
        if method == "GET" and endpoint == "/git/commits/" + SHA_MAIN:
            return {"tree": {"sha": "c" * 40}}
        if method == "POST" and endpoint == "/git/trees":
            self.rec = json.loads(payload["tree"][0]["content"])
            return {"sha": "d" * 40}
        if method == "POST" and endpoint == "/git/commits":
            sha = format(1000 + len(self.commits), "040x")
            self.commits[sha] = self.rec
            return {"sha": sha}
        if method == "POST" and endpoint == "/git/refs":
            key = payload["ref"]
            if key in self.refs:
                raise f.ClaimFailure("GitHub 422: ref already exists")
            self.refs[key] = payload["sha"]
            return {"ref": key}
        if method == "GET" and endpoint.startswith("/git/ref/heads/coord/fsem-claims/"):
            key = "refs/" + endpoint.removeprefix("/git/ref/")
            if key not in self.refs:
                raise f.ClaimFailure("GitHub 404: claim missing")
            return {"object": {"sha": self.refs[key]}}
        if method == "GET" and endpoint.startswith("/contents/" + f.CLAIM_FILE):
            sha = urllib.parse.unquote(endpoint.partition("?ref=")[2])
            if sha not in self.commits:
                raise f.ClaimFailure("claim missing record")
            record = self.commits[sha]
            return {"encoding": "base64", "content":
                    base64.b64encode(json.dumps(record).encode()).decode()}
        if method == "POST" and endpoint == f"/issues/{ISSUE}/comments":
            self.comments.append({"body": payload["body"]})
            return {"id": len(self.comments)}
        if method == "GET" and endpoint.startswith("/pulls/"):
            number = int(endpoint.rsplit("/", 1)[-1])
            return next(x for x in self.prs if x["number"] == number)
        if method == "DELETE" and endpoint.startswith("/git/refs/"):
            key = "refs/" + endpoint.removeprefix("/git/refs/")
            if key not in self.refs:
                raise f.ClaimFailure("already released")
            self.deleted.append(key)
            del self.refs[key]
            return None
        raise AssertionError((method, endpoint, payload))


class CoordinationTests(unittest.TestCase):
    def test_invalid_identifiers_fail_closed(self):
        for value in ("fsem-1", "FSEM-01", "fsem-01/part", "../fsem-01"):
            with self.subTest(value=value), self.assertRaises(f.ClaimFailure):
                f.validate_slice(value)
        for value in ("main", "formal-semantics/../main",
                      "formal-semantics/x.lock", "formal-semantics//x"):
            with self.subTest(value=value), self.assertRaises(f.ClaimFailure):
                f.validate_branch(value)

    def test_existing_same_family_and_unscoped_pr_block_acquire(self):
        self.assertEqual(f.conflicts([pr()], "fsem-01"), [99])
        unscoped = pr()
        unscoped["body"] = ""
        unscoped["title"] = "Unclassified work"
        self.assertEqual(f.conflicts([unscoped], "fsem-01"), [99])
        self.assertEqual(f.conflicts([pr()], "fsem-02"), [])

    def test_atomic_ref_has_exactly_one_winner(self):
        api = FakeGitHub()
        f.acquire(api, "fsem-01", BRANCH, "chat:docs-lane")
        self.assertIn(f.claim_ref("fsem-01"), api.refs)
        with self.assertRaisesRegex(f.ClaimFailure, "422"):
            f.acquire(api, "fsem-01", "formal-semantics/other", "chat:other")
        winner_sha = api.refs[f.claim_ref("fsem-01")]
        self.assertEqual(api.commits[winner_sha]["branch"], BRANCH)
        self.assertEqual(len(f.recorded_claims(api.comments)), 1)

    def test_verification_and_release_require_correct_pr(self):
        api = FakeGitHub()
        f.acquire(api, "fsem-01", BRANCH, "chat:docs-lane")
        api.prs = [pr()]
        f.verify(api, 99)
        api.prs[0]["head"]["ref"] = "formal-semantics/another"
        with self.assertRaisesRegex(f.ClaimFailure, "already claimed"):
            f.verify(api, 99)
        api.prs[0]["head"]["ref"] = BRANCH
        with self.assertRaisesRegex(f.ClaimFailure, "CLOSED"):
            f.release(api, 99)
        api.prs[0]["state"] = "closed"
        f.release(api, 99)
        self.assertEqual(api.refs, {})
        self.assertEqual(api.deleted, [f.claim_ref("fsem-01")])
        self.assertIn(f.RELEASE_MARKER, api.comments[-1]["body"])

    def test_missing_issue_audit_blocks_pr(self):
        api = FakeGitHub()
        f.acquire(api, "fsem-01", BRANCH, "chat:docs-lane")
        api.comments.clear()
        api.prs = [pr()]
        with self.assertRaisesRegex(f.ClaimFailure, "not recorded"):
            f.verify(api, 99)
        f.announce(api, "fsem-01")
        f.verify(api, 99)

    def test_old_closed_pr_cannot_release_new_claim(self):
        api = FakeGitHub()
        f.acquire(api, "fsem-01", BRANCH, "chat:docs-lane")
        api.prs = [pr(state="closed", created="2026-01-01T00:00:00Z")]
        with self.assertRaisesRegex(f.ClaimFailure, "postdates"):
            f.release(api, 99)
        self.assertIn(f.claim_ref("fsem-01"), api.refs)

    def test_unopened_abandonment_requires_matching_actor_and_no_open_pr(self):
        api = FakeGitHub()
        f.acquire(api, "fsem-01", BRANCH, "chat:docs-lane")
        with self.assertRaisesRegex(f.ClaimFailure, "recorded claimant"):
            f.abort_unopened(api, "fsem-01", "chat:other")
        api.prs = [pr()]
        with self.assertRaisesRegex(f.ClaimFailure, "open PR"):
            f.abort_unopened(api, "fsem-01", "chat:docs-lane")
        api.prs = []
        f.abort_unopened(api, "fsem-01", "chat:docs-lane")
        self.assertNotIn(f.claim_ref("fsem-01"), api.refs)

    def test_open_competitor_blocks_claimed_pr(self):
        api = FakeGitHub()
        f.acquire(api, "fsem-01", BRANCH, "chat:docs-lane")
        api.prs = [pr(), pr(number=100, branch="formal-semantics/rogue")]
        with self.assertRaisesRegex(f.ClaimFailure, "competing"):
            f.verify(api, 99)


    def test_reconcile_releases_only_unique_merged_exact_claim(self):
        api = FakeGitHub()
        f.acquire(api, "fsem-01", BRANCH, "chat:pair-programming")
        other_branch = "formal-semantics/fsem02-restricted-predecessor-replay"
        f.acquire(api, "fsem-02", other_branch, "hamster:fsem")
        api.prs = [
            pr(number=99),  # Open FSEM-01 must remain claimed.
            pr(number=1707, branch=other_branch, slice_key="fsem-02",
               state="closed", title="FSEM-02: predecessor replay",
               merged_at="2099-01-01T00:01:00Z"),
        ]
        old_sha = api.refs[f.claim_ref("fsem-02")]
        result = f.reconcile(api)
        self.assertEqual(result, [("fsem-02", 1707, old_sha)])
        self.assertIn(f.claim_ref("fsem-01"), api.refs)
        self.assertNotIn(f.claim_ref("fsem-02"), api.refs)
        self.assertEqual(api.deleted, [f.claim_ref("fsem-02")])
        self.assertIn("PR #1707", api.comments[-1]["body"])

    def test_reconcile_keeps_unmerged_or_old_closed_prs_locked(self):
        api = FakeGitHub()
        f.acquire(api, "fsem-01", BRANCH, "chat:pair-programming")
        api.prs = [pr(state="closed")]
        self.assertEqual(f.reconcile(api), [])
        self.assertTrue(api.refs)
        api.prs[0]["merged_at"] = "2026-01-01T00:00:00Z"
        api.prs[0]["created_at"] = "2026-01-01T00:00:00Z"
        self.assertEqual(f.reconcile(api), [])
        self.assertEqual(len(api.deleted), 0)

    def test_reconcile_rejects_ambiguous_merged_prs(self):
        api = FakeGitHub()
        f.acquire(api, "fsem-01", BRANCH, "chat:pair-programming")
        api.prs = [
            pr(number=99, state="closed", merged_at="2099-01-01T00:01:00Z"),
            pr(number=100, state="closed", merged_at="2099-01-01T00:02:00Z"),
        ]
        with self.assertRaisesRegex(f.ClaimFailure, "ambiguous merged"):
            f.reconcile(api)
        self.assertEqual(api.deleted, [])

    def test_reconcile_refuses_missing_issue_audit(self):
        api = FakeGitHub()
        f.acquire(api, "fsem-01", BRANCH, "chat:pair-programming")
        api.comments.clear()
        api.prs = [
            pr(state="closed", merged_at="2099-01-01T00:01:00Z"),
        ]
        with self.assertRaisesRegex(f.ClaimFailure, "not recorded"):
            f.reconcile(api)
        self.assertEqual(api.deleted, [])

    def test_reconcile_refuses_open_competing_family_pr(self):
        api = FakeGitHub()
        f.acquire(api, "fsem-01", BRANCH, "chat:pair-programming")
        api.prs = [
            pr(state="closed", merged_at="2099-01-01T00:01:00Z"),
            pr(number=100, branch="formal-semantics/unclassified",
               title="Unclassified", slice_key="fsem-01"),
        ]
        with self.assertRaisesRegex(f.ClaimFailure, "open same-family"):
            f.reconcile(api)
        self.assertEqual(api.deleted, [])

    def test_manual_recovery_requires_merged_exact_sha(self):
        api = FakeGitHub()
        f.acquire(api, "fsem-01", BRANCH, "chat:pair-programming")
        api.prs = [pr(state="closed")]
        sha = api.refs[f.claim_ref("fsem-01")]
        with self.assertRaisesRegex(f.ClaimFailure, "MERGED"):
            f.release(api, 99, expected_sha=sha, require_merged=True)
        api.prs[0]["merged_at"] = "2099-01-01T00:01:00Z"
        with self.assertRaisesRegex(f.ClaimFailure, "SHA changed"):
            f.release(api, 99, expected_sha="f" * 40, require_merged=True)
        self.assertEqual(api.deleted, [])
        f.release(api, 99, expected_sha=sha, require_merged=True)
        self.assertEqual(api.deleted, [f.claim_ref("fsem-01")])

    def test_reconcile_does_not_release_non_main_merge(self):
        api = FakeGitHub()
        f.acquire(api, "fsem-01", BRANCH, "chat:pair-programming")
        p = pr(state="closed", merged_at="2099-01-01T00:01:00Z")
        p["base"]["ref"] = "feature"
        api.prs = [p]
        self.assertEqual(f.reconcile(api), [])
        sha = api.refs[f.claim_ref("fsem-01")]
        with self.assertRaisesRegex(f.ClaimFailure, "merge into main"):
            f.release(api, 99, expected_sha=sha, require_merged=True)
        self.assertEqual(api.deleted, [])

    def test_reconcile_ignores_foreign_or_unlabeled_pr(self):
        api = FakeGitHub()
        f.acquire(api, "fsem-01", BRANCH, "chat:pair-programming")
        p = pr(state="closed", merged_at="2099-01-01T00:01:00Z")
        p["head"]["repo"]["full_name"] = "other/repo"
        api.prs = [p]
        self.assertEqual(f.reconcile(api), [])
        p["head"]["repo"]["full_name"] = f.REPO
        p["labels"] = []
        self.assertEqual(f.reconcile(api), [])
        self.assertEqual(api.deleted, [])


if __name__ == "__main__":
    unittest.main()
