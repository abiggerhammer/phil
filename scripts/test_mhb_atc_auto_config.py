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
            "      github.ref == 'refs/heads/main' &&\n"
            "      (github.event_name == 'workflow_dispatch' ||\n"
            "       (github.event_name == 'schedule' &&\n"
            "        vars.MHB_ATC_AUTO_ADMIT_ENABLED == 'true'))\n"
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
        self.assertIn('gh issue edit "$issue" --repo "$GH_REPO" --add-label "atc: admitting"', self.source)
        self.assertIn('gh issue edit "$issue" --repo "$GH_REPO" --remove-label "atc: staged"', self.source)
        self.assertIn("--add-label \"atc: admitting\"", self.source)
        self.assertNotIn("HAMSTER_PR_TOKEN", self.source)
        self.assertIn("    environment: atc-publisher", self.source)
        self.assertIn("uses: actions/create-github-app-token@64ab729a6294000f5aa4a4bc0b73d1f32bc45510 # v3", self.source)
        self.assertIn("IMMUTABLE_ENABLED: ${{ vars.MHB_ATC_IMMUTABLE_HEADS_ENABLED }}",
                      self.source)
        self.assertIn("PUBLISHER_TOKEN: ${{ steps.publisher_token.outputs.token }}",
                      self.source)


class ManualPublisherCredentialPreflightTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = (Path(__file__).resolve().parents[1] /
                      ".github/workflows/mhb-atc-publisher-token-preflight.yml").read_text(
                          encoding="utf-8")

    def test_manual_only_trusted_main_protected_environment(self):
        self.assertIn("  workflow_dispatch:\n", self.source)
        self.assertNotIn("\n  push:", self.source)
        self.assertNotIn("\n  schedule:", self.source)
        self.assertNotIn("\n  pull_request:", self.source)
        self.assertIn("github.ref == 'refs/heads/main'", self.source)
        self.assertIn("environment: atc-publisher", self.source)
        self.assertIn("ref: main", self.source)
        self.assertIn("persist-credentials: false", self.source)

    def test_preflight_requires_all_three_runtime_switches_off(self):
        for var in ("MHB_ATC_AUTO_ADMIT_ENABLED",
                    "MHB_ATC_PHASE2_STAGE_BRIDGE_ENABLED",
                    "MHB_ATC_IMMUTABLE_HEADS_ENABLED"):
            self.assertIn("vars." + var, self.source)
        self.assertIn('test "$enabled" != "true"', self.source)

    def test_mint_matches_actual_publisher_but_performs_only_reads(self):
        self.assertIn(
            "actions/create-github-app-token@64ab729a6294000f5aa4a4bc0b73d1f32bc45510",
            self.source)
        self.assertIn("permission-contents: write", self.source)
        self.assertIn("permission-pull-requests: write", self.source)
        self.assertIn("private-key: ${{ secrets.MHB_ATC_PUBLISHER_APP_PRIVATE_KEY }}",
                      self.source)
        self.assertIn("client-id: ${{ vars.MHB_ATC_PUBLISHER_APP_CLIENT_ID }}",
                      self.source)
        self.assertIn("steps.publisher_token.outputs.app-slug", self.source)
        self.assertIn('test "$ACTION_APP_SLUG" = "$PINNED_APP_SLUG"', self.source)
        self.assertIn('gh api "installation/repositories"', self.source)
        self.assertIn(".total_count == 1", self.source)
        self.assertIn('.repositories[0].full_name == $repo', self.source)
        self.assertIn("scripts/mhb_atc_publisher_identity_snapshot.sh", self.source)
        self.assertIn("scripts/mhb_atc_immutable.py ruleset", self.source)
        # The action mints a write-capable installation token, but every
        # actual GitHub command in this workflow must be a read.
        for line in self.source.splitlines():
            stripped = line.strip()
            if stripped.startswith("gh api "):
                self.assertNotIn(" --method POST", stripped)
                self.assertNotIn(" --method PATCH", stripped)
                self.assertNotIn(" --method PUT", stripped)
                self.assertNotIn(" --method DELETE", stripped)
                self.assertNotIn(" -X ", stripped)
        self.assertNotIn("gh pr create", self.source)
        self.assertNotIn("gh issue edit", self.source)
        self.assertNotIn("gh issue close", self.source)
        self.assertNotIn("gh label create", self.source)
        self.assertNotIn("git push", self.source)


if __name__ == "__main__":
    unittest.main()
