#!/usr/bin/env python3
"""Offline replay of single-slot MHB-ATC admission decisions."""
from __future__ import annotations

import unittest
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from mhb_atc_stage import parse_intent
from mhb_atc_admit import plan, STAGED_LABEL, ACTIVE_LABEL

A, B = ("a" * 40, "b" * 40)


def label(name):
    return {"name": name}


def issue(n=101, branch="hamster/staged/mhb-atc/example",
          sha=A, created="2026-11-06T08:00:00Z", state="atc: staged"):
    data = parse_intent(branch, sha, sha)
    return {"state": "open", "number": n, "title": data["title"],
            "body": data["body"], "created_at": created,
            "user": {"login": "github-actions[bot]"},
            "labels": [label(state), label("lane: " + data["lane"])]}


def pr(n=555, branch="hamster/staged/mhb-atc/live"):
    return {"state": "open", "number": n, "head": {"ref": branch}, "labels": []}


class AdmissionTests(unittest.TestCase):
    def test_oldest_candidate_first(self):
        older = issue()
        newer = issue(102, "hamster/staged/stdlib/parser", B,
                      "2026-11-06T08:01:00Z")
        self.assertEqual(plan([newer, older], [])["candidate_issue"], 101)

    def test_ties_break_by_issue_number(self):
        a = issue(107)
        b = issue(102, "hamster/staged/stdlib/parser", B)
        self.assertEqual(plan([a, b], [])["candidate_issue"], 102)

    def test_active_stage_pr_blocks_slot(self):
        result = plan([issue()], [pr()])
        self.assertEqual(result["decision"], "hold")
        self.assertEqual(result["open_staged_prs"], [555])

    def test_admitted_pr_blocks_even_if_not_staged_namespace(self):
        live = pr(branch="some/other/branch")
        live["labels"].append(label(ACTIVE_LABEL))
        self.assertEqual(plan([issue()], [live])["decision"], "hold")

    def test_admitted_pr_seen_in_issues_api_is_not_a_candidate_issue(self):
        live = pr()
        live["labels"] = [label(ACTIVE_LABEL)]
        as_issue = {"state": "open", "number": 555,
                    "pull_request": {"url": "https://api.github.com/pr/555"},
                    "labels": [label(ACTIVE_LABEL)]}
        result = plan([as_issue, issue()], [live])
        self.assertEqual(result["decision"], "hold")
        self.assertEqual(result["open_staged_prs"], [555])

    def test_interrupted_admission_reserves_capacity_without_pr(self):
        result = plan([issue(state="atc: admitting")], [])
        self.assertEqual(result["decision"], "hold")
        self.assertEqual(result["unreconciled_issue_ids"], [101])

    def test_admitting_pr_in_issues_api_is_rejected(self):
        as_issue = {"state": "open", "number": 555,
                    "pull_request": {"url": "https://api.github.com/pr/555"},
                    "labels": [label("atc: admitting")]}
        with self.assertRaises(ValueError):
            plan([as_issue], [])

    def test_admitted_issue_without_pr_fails_closed(self):
        result = plan([issue(state=ACTIVE_LABEL)], [])
        self.assertEqual(result["decision"], "hold")
        self.assertEqual(result["unreconciled_issue_ids"], [101])

    def test_empty_queue_holds(self):
        self.assertEqual(plan([], [])["reason"], "no staged candidates")

    def test_mislabelled_and_unsafe_records_fail_closed(self):
        bads = []
        x = issue(); x["user"] = {"login": "untrusted"}; bads.append(x)
        x = issue(); x["labels"] = [label(STAGED_LABEL), label("lane: bogus")]; bads.append(x)
        x = issue(); x["title"] = "mismatched"; bads.append(x)
        x = issue(); x["body"] = "<invalid>"; bads.append(x)
        x = issue(); x["labels"].append(label(ACTIVE_LABEL)); bads.append(x)
        x = issue(); x["pull_request"] = {"url": "fake"}; bads.append(x)
        for bad in bads:
            with self.subTest(number=bad.get("number"), record=bad):
                with self.assertRaises(ValueError):
                    plan([bad], [])

    def test_duplicate_branch_records_fail_closed(self):
        with self.assertRaisesRegex(ValueError, "duplicate staged branch"):
            plan([issue(101), issue(103)], [])

    def test_incomplete_api_snapshots_fail_closed(self):
        for issues, prs in ((None, []), ([], None), ({}, []), ([], {})):
            with self.subTest(issues=issues, prs=prs):
                with self.assertRaises(ValueError):
                    plan(issues, prs)

    def test_invalid_open_prs_fail_closed(self):
        for bad in ({"state": "open", "head": None},
                    {"state": "closed", "head": {"ref": "foo"}, "labels": []}):
            with self.subTest(pr=bad):
                with self.assertRaises(ValueError):
                    plan([issue()], [bad])

    def test_only_staged_issues_are_candidates(self):
        arbitrary = {"state": "open", "number": 2, "labels": [],
                     "title": "ordinary issue"}
        self.assertEqual(plan([arbitrary, issue()], [])["candidate_issue"], 101)


if __name__ == "__main__":
    unittest.main()
