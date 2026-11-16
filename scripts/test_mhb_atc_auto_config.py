#!/usr/bin/env python3
"""Static safety regression tests for the opt-in ATC scheduling boundary.

No workflow run or GitHub mutation occurs here. GitHub itself validates YAML;
these tests pin the narrow opt-in decision and existing manual behavior.
"""
from pathlib import Path
import unittest

WORKFLOW = (Path(__file__).resolve().parents[1]
            / ".github/workflows/mhb-atc-admit.yml")


class ScheduledAdmissionGuardTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = WORKFLOW.read_text(encoding="utf-8")

    def test_schedule_does_not_admit_without_exact_opt_in(self):
        gate = (
            "    if: >-\n"
            "      github.event_name == 'workflow_dispatch' ||\n"
            "      (github.event_name == 'schedule' &&\n"
            "       vars.MHB_ATC_AUTO_ADMIT_ENABLED == 'true')\n"
        )
        self.assertEqual(self.source.count(gate), 1)
        self.assertEqual(
            self.source.count("vars.MHB_ATC_AUTO_ADMIT_ENABLED"), 1)

    def test_schedule_is_explicit_and_not_a_push_trigger(self):
        self.assertIn(
            "  schedule:\n    - cron: '7,22,37,52 * * * *'\n",
            self.source)
        self.assertNotIn("\n  push:", self.source)
        self.assertNotIn("\n  pull_request:", self.source)

    def test_manual_controls_and_single_shared_queue_still_exist(self):
        self.assertIn("  workflow_dispatch:\n", self.source)
        self.assertIn("        default: dry-run\n", self.source)
        self.assertIn("          - dry-run\n", self.source)
        self.assertIn("          - admit-one\n", self.source)
        self.assertIn("  group: mhb-atc-admission-global\n", self.source)
        self.assertIn("  queue: max\n", self.source)
        self.assertIn("  cancel-in-progress: false\n", self.source)
        self.assertIn("if [ \"$MODE\" = \"dry-run\" ]; then", self.source)
        self.assertIn("if [ \"$decision\" = \"hold\" ]; then", self.source)

    def test_schedule_uses_existing_exact_head_admit_one_path(self):
        self.assertIn(
            "MODE: ${{ github.event_name == 'schedule' && 'admit-one' || inputs.mode }}",
            self.source)
        self.assertIn("test \"$live\" = \"$expected\"", self.source)
        self.assertIn("gh issue edit \"$issue\" --repo \"$GH_REPO\" \\", self.source)
        self.assertIn("--add-label \"atc: admitting\"", self.source)
        self.assertIn("HAMSTER_PR_TOKEN: ${{ secrets.HAMSTER_PR_TOKEN }}",
                      self.source)


if __name__ == "__main__":
    unittest.main()
