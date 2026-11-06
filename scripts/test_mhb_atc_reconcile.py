#!/usr/bin/env python3
"""Offline recovery and closed-PR slot-release replays; no GitHub I/O."""
from __future__ import annotations

import datetime as dt
import unittest
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from mhb_atc_stage import parse_intent
from mhb_atc_reconcile import ADMITTING_LABEL, plan
from mhb_atc_admit import ACTIVE_LABEL, STAGED_LABEL

A = "a" * 40
B = "b" * 40
REPO = "abiggerhammer/phil"
NOW = dt.datetime(2026, 11, 6, 14, 0, tzinfo=dt.timezone.utc)
BRANCH = "hamster/staged/mhb-atc/first"
OTHER = "hamster/staged/stdlib/second"


def label(name):
    return {"name": name}


def issue(n=1701, branch=BRANCH, sha=A, state=ACTIVE_LABEL,
          updated="2026-11-06T13:20:00Z", created="2026-11-06T13:00:00Z"):
    r = parse_intent(branch, sha, sha)
    return {"number": n, "state": "open", "title": r["title"],
            "body": r["body"], "created_at": created, "updated_at": updated,
            "user": {"login": "github-actions[bot]"},
            "labels": [label(state), label("lane: " + r["lane"])]}


def pr(n=1702, issue_number=1701, branch=BRANCH, sha=A,
       state="closed", labels=True):
    lane = branch.split("/")[2]
    return {"number": n, "state": state, "title": "MHB-ATC admission: " + lane
            + " / " + str(issue_number),
            "body": "\n".join([
                "MHB-ATC admitted staged candidate; this PR is **not** merge clearance.",
                "", "- Candidate issue: #" + str(issue_number),
                "- Lane: " + lane, "- Staged branch: " + branch,
                "- Exact registered head: " + sha,
                "", "Required checks and integration safety must still be verified before any merge."]),
            "head": {"ref": branch, "sha": sha,
                     "repo": {"full_name": REPO}},
            "base": {"ref": "main", "repo": {"full_name": REPO}},
            "labels": [label(ACTIVE_LABEL), label("lane: " + lane)] if labels else []}


class RecoveryTests(unittest.TestCase):
    def test_release_after_close(self):
        r = plan([issue()], [pr()], REPO, NOW)
        self.assertEqual(r["action"], "release")
        self.assertEqual(r["issue"], 1701)
        self.assertEqual(r["pr"], 1702)
        self.assertEqual(r["head_sha"], A)

    def test_release_interrupted_reservation_if_pr_closed(self):
        r = plan([issue(state=ADMITTING_LABEL)], [pr()], REPO, NOW)
        self.assertEqual(r["action"], "release")

    def test_repair_partial_open_pr(self):
        r = plan([issue(state=ADMITTING_LABEL)], [pr(state="open", labels=False)], REPO, NOW)
        self.assertEqual(r["action"], "repair")
        self.assertTrue(r["needs_label"])

    def test_repair_missing_pr_label_after_issue_admitted(self):
        r = plan([issue()], [pr(state="open", labels=False)], REPO, NOW)
        self.assertEqual(r["action"], "repair")
        self.assertEqual(r["prior_state"], ACTIVE_LABEL)

    def test_inflight_normal_admission_is_not_released(self):
        r = plan([issue()], [pr(state="open")], REPO, NOW)
        self.assertEqual(r["decision"], "hold")

    def test_retry_expired_reservation_without_pr(self):
        r = plan([issue(state=ADMITTING_LABEL)], [], REPO, NOW)
        self.assertEqual(r["action"], "retry")
        self.assertEqual(r["issue"], 1701)

    def test_not_retry_fresh_reservation(self):
        x = issue(state=ADMITTING_LABEL, updated="2026-11-06T13:58:00Z")
        r = plan([x], [], REPO, NOW)
        self.assertEqual(r["decision"], "hold")

    def test_no_candidate_no_op(self):
        self.assertEqual(plan([], [], REPO, NOW)["decision"], "hold")

    def test_never_release_admitted_issue_without_pr(self):
        with self.assertRaisesRegex(ValueError, "no matching PR"):
            plan([issue()], [], REPO, NOW)

    def test_never_promote_staged_issue_with_pr(self):
        for state in ("open", "closed"):
            with self.subTest(state=state):
                with self.assertRaisesRegex(ValueError, "unreserved"):
                    plan([issue(state=STAGED_LABEL)], [pr(state=state)], REPO, NOW)

    def test_mismatched_sha_fails_closed(self):
        with self.assertRaisesRegex(ValueError, "identity mismatch"):
            plan([issue()], [pr(sha=B)], REPO, NOW)

    def test_modified_pr_link_fails_closed(self):
        mods = [
            lambda x: x.update(body="mismatched PR body"),
            lambda x: x.update(title="wrong title"),
            lambda x: x["base"].update(ref="elsewhere"),
            lambda x: x["head"]["repo"].update(full_name="other/fork"),
            lambda x: x["head"].update(sha=B),
            lambda x: x["labels"].append(label("lane: impl-audit")),
        ]
        for change in mods:
            x = pr()
            change(x)
            with self.subTest(pr=x):
                with self.assertRaises(ValueError):
                    plan([issue()], [x], REPO, NOW)

    def test_untrusted_issue_fails_closed(self):
        x = issue()
        x["user"]["login"] = "someone-else"
        with self.assertRaisesRegex(ValueError, "untrusted"):
            plan([x], [], REPO, NOW)

    def test_duplicate_issues_fail_closed(self):
        with self.assertRaisesRegex(ValueError, "duplicate queue"):
            plan([issue(1701), issue(1703)], [], REPO, NOW)

    def test_multiple_prs_fail_closed(self):
        with self.assertRaisesRegex(ValueError, "multiple PRs"):
            plan([issue()], [pr(1702), pr(1704)], REPO, NOW)

    def test_closed_release_takes_priority_over_repair(self):
        first = issue(1701, branch=BRANCH, state=ADMITTING_LABEL)
        second = issue(1703, branch=OTHER, sha=B, state=ACTIVE_LABEL)
        r = plan([first, second],
                 [pr(n=1702, issue_number=1701, state="open"),
                  pr(n=1704, issue_number=1703, branch=OTHER, sha=B, state="closed")],
                 REPO, NOW)
        self.assertEqual(r["action"], "release")
        self.assertEqual(r["issue"], 1703)

    def test_timezone_required(self):
        with self.assertRaises(ValueError):
            plan([], [], REPO, dt.datetime(2026, 11, 6))

    def test_missing_or_malformed_snapshot_fails_closed(self):
        for issues, prs in ((None, []), ([], None), ({}, []), ([], {}),
                            ([issue()], [{"head": {}}])):
            with self.subTest(issues=issues, prs=prs):
                with self.assertRaises(ValueError):
                    plan(issues, prs, REPO, NOW)


if __name__ == "__main__":
    unittest.main()
