#!/usr/bin/env python3
"""Offline replay tests for trusted MHB-ATC staging intent validation."""
from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from mhb_atc_stage import MARKER, parse_intent
from mhb_atc_phase2_wip import plan as phase2_wip_plan

A = "a" * 40
B = "b" * 40


class StageIntentTests(unittest.TestCase):
    def test_authorized_exact_head_candidate(self):
        branch = "hamster/staged/mhb-atc/candidate-one"
        r = parse_intent(branch, A, A)
        self.assertEqual(r["lane"], "mhb-atc")
        self.assertEqual(r["head_sha"], A)
        self.assertEqual(r["title"], "ATC candidate: " + branch)
        self.assertTrue(r["body"].startswith(MARKER))
        self.assertIn('"head_sha": "' + A + '"', r["body"])
        self.assertIn("not an admitted PR", r["body"])

    def test_nested_staged_branches(self):
        r = parse_intent("hamster/staged/stdlib/regex/parser-v2", B, B)
        self.assertEqual(r["lane"], "stdlib")

    def test_head_sha_must_be_current(self):
        with self.assertRaisesRegex(ValueError, "stale candidate"):
            parse_intent("hamster/staged/mhb-atc/a", A, B)

    def test_invalid_shas_fail_closed(self):
        for sha in ("", "a" * 39, "A" * 40, "x" * 40, A + "x"):
            with self.subTest(sha=sha):
                with self.assertRaisesRegex(ValueError, "invalid exact SHA"):
                    parse_intent("hamster/staged/mhb-atc/a", sha, A)

    def test_unsafe_branches_fail_closed(self):
        for branch in (
            "hamster/impl-audit/legacy", "hamster/staged/",
            "hamster/staged/mhb-atc",
            "hamster/staged/BadLane/foo", "hamster/staged/mhb-atc/../evil",
            "hamster/staged/mhb-atc/x.lock", "hamster/staged/mhb-atc/x y",
            "hamster/staged/mhb-atc//empty", "hamster/staged/mhb-atc/foo@{bar}",
            "hamster/staged/mhb-atc/foo\nbar",
            "hamster/staged/mhb-atc/" + ("x" * 250),
        ):
            with self.subTest(branch=branch):
                with self.assertRaises(ValueError):
                    parse_intent(branch, A, A)

    def test_deterministic_machine_record(self):
        r1 = parse_intent("hamster/staged/surface/parser", A, A)
        r2 = parse_intent("hamster/staged/surface/parser", A, A)
        self.assertEqual(r1, r2)
        machine = r1["body"].split("~~~json\n", 1)[1].split("\n~~~", 1)[0]
        self.assertEqual(json.loads(machine), {
            "version": 1, "lane": "surface",
            "branch": "hamster/staged/surface/parser", "head_sha": A,
        })


def phase2_candidate(branch, state="atc: staged"):
    recorded = parse_intent(branch, A, A)
    return {
        "state": "open",
        "title": recorded["title"],
        "body": recorded["body"],
        "user": {"login": "github-actions[bot]"},
        "labels": [{"name": state}, {"name": "lane: " + recorded["lane"]}],
    }


class Phase2WIPPolicyTests(unittest.TestCase):
    BRANCH = "hamster/staged/phase2-selfhost/first"
    NEXT = "hamster/staged/phase2-selfhost/next"
    OTHER = "hamster/staged/phase2-embedded/other"

    def test_first_candidate_and_same_head_refresh(self):
        initial = phase2_wip_plan([], "phase2-selfhost", self.BRANCH)
        self.assertEqual(initial["decision"], "allow-stage")
        refreshed = phase2_wip_plan(
            [phase2_candidate(self.BRANCH)], "phase2-selfhost", self.BRANCH)
        self.assertEqual(refreshed["staged_count"], 1)

    def test_distinct_second_staged_candidate_refused(self):
        with self.assertRaisesRegex(ValueError, "staged successor"):
            phase2_wip_plan(
                [phase2_candidate(self.BRANCH)], "phase2-selfhost", self.NEXT)

    def test_one_active_and_one_successor_allowed(self):
        result = phase2_wip_plan(
            [phase2_candidate(self.BRANCH, "atc: admitted")],
            "phase2-selfhost", self.NEXT)
        self.assertEqual(result["active_count"], 1)
        self.assertEqual(result["staged_count"], 0)

    def test_one_active_plus_one_existing_staged_refreshed(self):
        result = phase2_wip_plan(
            [phase2_candidate(self.BRANCH, "atc: admitted"),
             phase2_candidate(self.NEXT)],
            "phase2-selfhost", self.NEXT)
        self.assertEqual((result["active_count"], result["staged_count"]),
                         (1, 1))

    def test_over_capacity_active_refused(self):
        with self.assertRaisesRegex(ValueError, "over capacity"):
            phase2_wip_plan(
                [phase2_candidate(self.BRANCH, "atc: admitting"),
                 phase2_candidate(self.NEXT, "atc: admitted")],
                "phase2-selfhost", self.NEXT)

    def test_admitted_branch_cannot_be_restaged(self):
        with self.assertRaisesRegex(ValueError, "cannot restage"):
            phase2_wip_plan(
                [phase2_candidate(self.BRANCH, "atc: admitted")],
                "phase2-selfhost", self.BRANCH)

    def test_different_lane_does_not_consume_our_lane_wip(self):
        result = phase2_wip_plan(
            [phase2_candidate(self.OTHER)],
            "phase2-selfhost", self.BRANCH)
        self.assertEqual(result["staged_count"], 0)

    def test_provenance_and_ambiguous_states_fail_closed(self):
        bad = phase2_candidate(self.BRANCH)
        bad["user"]["login"] = "untrusted"
        with self.assertRaisesRegex(ValueError, "untrusted"):
            phase2_wip_plan([bad], "phase2-selfhost", self.BRANCH)
        bad = phase2_candidate(self.BRANCH)
        bad["labels"].append({"name": "atc: admitted"})
        with self.assertRaisesRegex(ValueError, "ambiguous"):
            phase2_wip_plan([bad], "phase2-selfhost", self.BRANCH)

    def test_lane_allowlist_exact(self):
        with self.assertRaisesRegex(ValueError, "unapproved"):
            phase2_wip_plan([], "impl-audit",
                            "hamster/staged/impl-audit/candidate")

    def test_bridge_remains_disabled_without_explicit_switch(self):
        path = (Path(__file__).resolve().parents[1]
                / ".github/workflows/mhb-atc-phase2-stage-bridge.yml")
        content = path.read_text(encoding="utf-8")
        self.assertIn(
            "vars.MHB_ATC_PHASE2_STAGE_BRIDGE_ENABLED == 'true'", content)
        self.assertIn("          ref: main", content)
        self.assertIn("          persist-credentials: false", content)
        self.assertIn(
            "'hamster/staged/phase2-selfhost/**'", content)
        self.assertIn(
            "'hamster/staged/phase2-embedded/**'", content)
        self.assertIn("gh api --method POST", content)


if __name__ == "__main__":
    unittest.main()
