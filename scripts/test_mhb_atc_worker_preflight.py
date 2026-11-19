#!/usr/bin/env python3
"""Offline W1 invariants: shared worker App identity and manual token preflight."""
from __future__ import annotations

import json
import os
from pathlib import Path
import re
import subprocess
import textwrap
import unittest

ROOT = Path(__file__).resolve().parents[1]
POLICY = ROOT / ".github/atc-worker-policy.json"
WORKFLOW = ROOT / ".github/workflows/mhb-atc-worker-token-preflight.yml"


class WorkerPreflightTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.workflow = WORKFLOW.read_text(encoding="utf-8")
        cls.policy = json.loads(POLICY.read_text(encoding="utf-8"))

    def test_public_source_policy_has_exact_worker_identity_and_no_key(self):
        self.assertEqual(self.policy["schema"], "MHB-ATC-WORKER-POLICY-V1")
        self.assertEqual(self.policy["repository"], "abiggerhammer/phil")
        self.assertEqual(self.policy["worker_app_id"], 5836223)
        self.assertEqual(self.policy["worker_app_slug"], "phil-atc-worker")
        self.assertEqual(self.policy["environment"], "atc-worker-broker")
        self.assertEqual(self.policy["intended_permissions"], {
            "contents": "write", "metadata": "read", "pull_requests": "none"})
        self.assertEqual(self.policy["credential_holder"], "trusted-main-broker-only")
        self.assertIs(self.policy["direct_worker_installation_tokens"], False)
        self.assertEqual(self.policy["broker_activation"], "disabled")
        self.assertNotIn("private", POLICY.read_text(encoding="utf-8").lower())

    def test_dispatch_is_manual_main_only_and_environment_restricted(self):
        src = self.workflow
        self.assertIn("\non:\n  workflow_dispatch:\n", src)
        for trigger in ("\n  push:", "\n  pull_request:", "\n  schedule:",
                        "repository_dispatch:"):
            self.assertNotIn(trigger, src)
        self.assertIn("github.event_name == 'workflow_dispatch'", src)
        self.assertIn("github.ref == 'refs/heads/main'", src)
        self.assertIn("environment: atc-worker-broker", src)
        self.assertIn("ref: main", src)
        self.assertIn("persist-credentials: false", src)
        self.assertIn("permissions:\n  contents: read\n", src)

    def test_all_three_activation_flags_must_be_checked_before_token(self):
        src = self.workflow
        for name in ("MHB_ATC_AUTO_ADMIT_ENABLED",
                     "MHB_ATC_IMMUTABLE_HEADS_ENABLED",
                     "MHB_ATC_PHASE2_STAGE_BRIDGE_ENABLED"):
            self.assertIn("vars." + name, src)
        guard = 'test "$' + '{enabled,,}" != "true"'
        self.assertIn(guard, src)
        self.assertLess(src.index(guard), src.index("id: worker_token"))

    def test_runtime_shell_guard_rejects_mixed_case_true(self):
        src = self.workflow
        begin = src.index(
            '          for enabled in "$AUTO_ADMIT_ENABLED" "$IMMUTABLE_ENABLED" "$STAGE_BRIDGE_ENABLED"; do')
        end = src.index("          done\n", begin) + len("          done\n")
        guard = "set -euo pipefail\n" + textwrap.dedent(src[begin:end])
        for variable in ("AUTO_ADMIT_ENABLED", "IMMUTABLE_ENABLED", "STAGE_BRIDGE_ENABLED"):
            for value in ("true", "TRUE", "True", "tRuE"):
                env = dict(os.environ, AUTO_ADMIT_ENABLED="",
                           IMMUTABLE_ENABLED="", STAGE_BRIDGE_ENABLED="")
                env[variable] = value
                with self.subTest(variable=variable, value=value):
                    run = subprocess.run(["bash", "-c", guard],
                                         capture_output=True, text=True, env=env)
                    self.assertNotEqual(run.returncode, 0)
                    self.assertIn("activation switch is ON", run.stderr)
        for inactive in ("", "false", "FALSE", "False"):
            env = dict(os.environ, AUTO_ADMIT_ENABLED=inactive,
                       IMMUTABLE_ENABLED="", STAGE_BRIDGE_ENABLED="")
            with self.subTest(inactive=inactive):
                run = subprocess.run(["bash", "-c", guard],
                                     capture_output=True, text=True, env=env)
                self.assertEqual(run.returncode, 0, run.stderr)

    def test_no_pr_rights_requested_or_token_exposed_to_worker(self):
        src = self.workflow
        self.assertIn("permission-contents: write", src)
        self.assertNotIn("permission-pull-requests:", src)
        self.assertNotIn("permission-issues:", src)
        self.assertNotIn("permission-administration:", src)
        self.assertIn("vars.MHB_ATC_WORKER_APP_CLIENT_ID", src)
        self.assertIn("secrets.MHB_ATC_WORKER_APP_PRIVATE_KEY", src)
        self.assertIn(
            "actions/create-github-app-token@64ab729a6294000f5aa4a4bc0b73d1f32bc45510",
            src)
        self.assertIn("steps.worker_token.outputs.app-slug", src)
        self.assertIn('test "$ACTION_APP_SLUG" = "$EXPECTED_APP_SLUG"', src)
        self.assertIn('gh api "installation/repositories"', src)
        self.assertNotRegex(src, r"(?m)^\s+(?:owner|repositories):")
        self.assertNotIn("skip-token-revoke: true", src)
        self.assertNotIn("git push", src)
        self.assertNotIn("gh pr create", src)
        self.assertNotIn("gh issue edit", src)
        self.assertNotIn("gh label create", src)
        self.assertNotRegex(src, r"\bgh api\s+--method\s+(?:POST|PATCH|PUT|DELETE)\b")
        # After minting, the only GitHub API request is the read-only
        # installation/repositories endpoint; never use it for worker code.
        after = src.split("      - name: Verify authenticated worker identity", 1)[1]
        self.assertEqual(
            re.findall(r'(?m)^\s+gh api "([^"]+)"', after),
            ["installation/repositories"])

    def test_claims_do_not_conflate_preflight_with_confinement(self):
        src = self.workflow
        self.assertIn("token revocation: enabled; inspect post-action cleanup", src)
        self.assertIn("next gate: separate actual worker permission-denial", src)
        self.assertNotIn("token revoked successfully", src)
        self.assertIn("direct_worker_installation_tokens == false", src)


if __name__ == "__main__":
    unittest.main()
