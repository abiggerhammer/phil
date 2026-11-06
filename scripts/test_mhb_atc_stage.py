#!/usr/bin/env python3
"""Offline replay tests for trusted MHB-ATC staging intent validation."""
from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from mhb_atc_stage import MARKER, parse_intent

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


if __name__ == "__main__":
    unittest.main()
