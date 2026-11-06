#!/usr/bin/env python3
"""Offline replay tests for MHB-ATC radar and shadow admission."""
from __future__ import annotations

import sys
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import mhb_atc as atc

A = "a" * 40
B = "b" * 40
C = "c" * 40


class RadarTests(unittest.TestCase):
    def test_queue_wait_and_execution(self):
        self.assertEqual(atc.seconds("2026-11-05T18:07:38Z",
                                     "2026-11-05T18:15:57Z"), 499)
        self.assertIsNone(atc.seconds(None, "2026-11-05T18:15:57Z"))
        self.assertIsNone(atc.seconds("2026-11-05T18:15:57Z",
                                      "2026-11-05T18:07:38Z"))

    def test_report_does_not_confuse_sample_with_total(self):
        runs = [
            {"head_sha": A, "event": "pull_request", "conclusion": "success"},
            {"head_sha": A, "event": "pull_request", "conclusion": "success"},
            {"head_sha": B, "event": "push", "conclusion": "cancelled"},
        ]
        jobs = [{"created_at": "2026-11-05T00:00:00Z",
                 "started_at": "2026-11-05T00:05:00Z",
                 "completed_at": "2026-11-05T00:07:00Z"}]
        report = atc.summarize_day("2026-11-05", runs, 2327, jobs)
        self.assertEqual(report["reported_total_workflow_runs"], 2327)
        self.assertEqual(report["sampled_workflow_runs"], 3)
        self.assertFalse(report["sample_is_complete"])
        self.assertEqual(report["sampled_top_revision_bursts"][0]["observed_workflow_runs"], 2)
        self.assertEqual(report["queue_wait_seconds"]["max"], 300)
        self.assertIn("samples", atc.markdown([report]))

    def test_github_scan_is_bounded_and_read_only(self):
        run = {"id": 42, "head_sha": A, "name": "CI",
               "event": "pull_request", "conclusion": "success"}
        responses = [
            {"total_count": 2, "workflow_runs": [run, dict(run, id=43, name="Proofs")]},
            {"total_count": 1, "jobs": [{"name": "build-and-test",
                                        "created_at": "2026-11-05T00:00:00Z",
                                        "started_at": "2026-11-05T00:00:02Z",
                                        "completed_at": "2026-11-05T00:10:02Z"}]},
        ]
        with patch.object(atc, "api", side_effect=responses) as mocked:
            result = atc.scan_day("owner/repo", "2026-11-05", pages=3, job_limit=1)
        self.assertEqual(mocked.call_count, 2)
        self.assertEqual(result["reported_total_workflow_runs"], 2)
        self.assertTrue(result["sample_is_complete"])
        self.assertEqual(result["queue_wait_seconds"]["max"], 2)

    def test_fail_if_sampled_jobs_page_incomplete(self):
        run = {"id": 42, "head_sha": A, "name": "CI"}
        with patch.object(atc, "api", side_effect=[
            {"total_count": 1, "workflow_runs": [run]},
            {"total_count": 2, "jobs": [{"name": "only one"}]},
        ]):
            with self.assertRaises(ValueError):
                atc.scan_day("owner/repo", "2026-11-05", pages=1, job_limit=1)


class ShadowAdmissionTests(unittest.TestCase):
    def candidate(self, sha=A, lane="rocq-refinement", at="2026-11-05T00:00:00Z"):
        return {"branch": f"hamster/{lane}/example", "head_sha": sha,
                "enqueued_at": at}

    def test_capacity_is_a_hard_gate(self):
        result = atc.recommend({
            "capacity": 1,
            "admitted": [{"state": "verifying", "head_sha": A}],
            "candidates": [self.candidate(sha=B)],
        })
        self.assertEqual(result["decision"], "hold")
        self.assertEqual(result["active"], 1)

    def test_fifo_and_sha_binding(self):
        late = self.candidate(sha=B, lane="impl-audit",
                              at="2026-11-05T00:01:00Z")
        early = self.candidate(sha=C, lane="proof-audit",
                               at="2026-11-05T00:00:00Z")
        result = atc.recommend({"admitted": [], "candidates": [late, early]})
        self.assertEqual(result["decision"], "would-admit")
        self.assertEqual(result["head_sha"], C)
        self.assertEqual(result["lane"], "proof-audit")
        self.assertIn("shadow-only", result["warning"])

    def test_timezone_comparison(self):
        later = self.candidate(sha=A, at="2026-11-05T01:00:00+01:00")
        early = self.candidate(sha=B, lane="impl-audit",
                               at="2026-11-04T23:00:00Z")
        result = atc.recommend({"admitted": [], "candidates": [later, early]})
        self.assertEqual(result["head_sha"], B)

    def test_unknown_admission_state_fails_closed(self):
        with self.assertRaises(ValueError):
            atc.recommend({"admitted": [{"state": "surprise", "head_sha": A}],
                           "candidates": []})

    def test_malformed_or_duplicate_candidates_fail_closed(self):
        first = self.candidate()
        for candidates in [[first, first], [dict(first, head_sha="bad")],
                           [dict(first, branch="other/missing")],
                           [dict(first, enqueued_at="2026-11-05T00:00:00")]]:
            with self.subTest(candidates=candidates):
                with self.assertRaises(ValueError):
                    atc.recommend({"admitted": [], "candidates": candidates})

    def test_blocked_revision_does_not_claim_runner_slot(self):
        result = atc.recommend({
            "admitted": [{"state": "blocked", "head_sha": A}],
            "candidates": [self.candidate(sha=B)],
        })
        self.assertEqual(result["decision"], "would-admit")

    def test_empty_queue_holds(self):
        result = atc.recommend({"admitted": [], "candidates": []})
        self.assertEqual(result["decision"], "hold")


if __name__ == "__main__":
    unittest.main()
