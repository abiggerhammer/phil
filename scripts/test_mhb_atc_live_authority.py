#!/usr/bin/env python3
"""Offline negative regressions for owner-local live authority evidence.

All fixtures are synthetic. No gh login, credential, network or GitHub write.
"""
from __future__ import annotations

import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest

from mhb_atc_live_authority import (
    APP_ID, APPLE_KEYS, OWNER_ID, audit_snapshot, read_json,
)

ROOT = Path(__file__).resolve().parents[1]
HEAD = "a" * 40


def collection(key, names):
    return {
        "total_count": len(names),
        key: [{"name": name} for name in sorted(names)],
    }


def environment(name, reviewers=False):
    return {
        "name": name,
        "deployment_branch_policy": {
            "protected_branches": False,
            "custom_branch_policies": True,
        },
        "protection_rules": [
            {"type": "branch_policy"},
            *([{"type": "required_reviewers", "reviewers": [
                {"type": "User", "reviewer": {"login": "reviewer"}}]}]
              if reviewers else []),
        ],
    }


def snapshot():
    flags = [
        {"name": "MHB_ATC_WORKER_BROKER_ENABLED", "value": "false"},
        {"name": "MHB_ATC_IMMUTABLE_HEADS_ENABLED", "value": "false"},
        {"name": "MHB_ATC_PHASE2_STAGE_BRIDGE_ENABLED", "value": "false"},
        {"name": "MHB_ATC_AUTO_ADMIT_ENABLED", "value": "false"},
        {"name": "MHB_ATC_WORKER_APP_ID", "value": str(APP_ID)},
        {"name": "MHB_ATC_WORKER_APP_SLUG", "value": "phil-atc-worker"},
        {"name": "MHB_ATC_WORKER_APP_CLIENT_ID", "value": "Iv1.fixture-only"},
    ]
    return {
        "actor": {"login": "abiggerhammer", "id": OWNER_ID, "type": "User"},
        "main_before": {"object": {"sha": HEAD}},
        "main_after": {"object": {"sha": HEAD}},
        "checkout_sha": HEAD,
        "checkout_branch": "main",
        "default_token": {
            "default_workflow_permissions": "read",
            "can_approve_pull_request_reviews": False,
        },
        "variables": {"total_count": len(flags), "variables": flags},
        "repository_secrets": collection("secrets", {"HAMSTER_PR_TOKEN"}),
        "macos_environment": environment("macos-release", reviewers=True),
        "macos_branch_policies": collection("branch_policies", {"main"}),
        "macos_secrets": collection("secrets", APPLE_KEYS),
        "broker_environment": environment("atc-worker-broker"),
        "broker_branch_policies": collection("branch_policies", {"main"}),
        "broker_secrets": collection("secrets", {"MHB_ATC_WORKER_APP_PRIVATE_KEY"}),
        "publisher_environment": environment("atc-publisher"),
        "publisher_branch_policies": collection("branch_policies", {"main"}),
        "publisher_secrets": collection(
            "secrets", {"MHB_ATC_PUBLISHER_APP_PRIVATE_KEY"}),
        "app_public": {
            "id": APP_ID, "slug": "phil-atc-worker",
            "owner": {"login": "abiggerhammer", "id": OWNER_ID},
            "permissions": {"contents": "write", "metadata": "read"},
        },
    }


class LiveAuthorityAuditTests(unittest.TestCase):
    def test_complete_fixture_passes_but_never_certifies_w1_id_or_w3(self):
        record = audit_snapshot(snapshot())
        self.assertEqual(record["decision"], "PASS_SOURCE_SETTINGS")
        self.assertTrue(all(x == "PASS" for x in record["checks"].values()))
        self.assertFalse(record["w1_id_authenticated_by_app_jwt"])
        self.assertFalse(record["w3_negative_write_commissioned"])
        self.assertNotIn("Iv1.fixture-only", json.dumps(record))
        self.assertNotIn("HAMSTER_PR_TOKEN", json.dumps(record))

    def test_missing_or_inaccessible_live_api_data_fails_closed(self):
        for name in ("actor", "main_before", "main_after", "default_token",
                     "variables", "macos_environment", "macos_branch_policies",
                     "broker_environment", "broker_branch_policies",
                     "publisher_environment", "publisher_branch_policies",
                     "repository_secrets", "macos_secrets", "broker_secrets",
                     "publisher_secrets", "app_public"):
            s = snapshot()
            s[name] = {"_unavailable": True}
            with self.subTest(endpoint=name):
                self.assertEqual(audit_snapshot(s)["decision"],
                                 "BLOCKED_INCOMPLETE_OR_UNSAFE")

    def test_excessive_pagination_and_ambiguous_json_denied(self):
        for key, field in [
            ("variables", "variables"), ("macos_branch_policies", "branch_policies"),
            ("repository_secrets", "secrets"),
        ]:
            s = snapshot()
            s[key]["total_count"] = 101
            with self.subTest(key=key):
                self.assertEqual(audit_snapshot(s)["decision"],
                                 "BLOCKED_INCOMPLETE_OR_UNSAFE")
        with self.assertRaisesRegex(ValueError, "duplicate JSON key"):
            read_json('{"default_workflow_permissions":"read",'
                      '"default_workflow_permissions":"write"}')
        with self.assertRaisesRegex(ValueError, "oversized"):
            read_json('"' + 'x' * 2_000_001 + '"')

    def test_negative_environment_and_branch_conditions(self):
        mutations = [
            lambda s: s["macos_environment"].update(
                {"deployment_branch_policy": None}),
            lambda s: s["broker_branch_policies"]["branch_policies"].append(
                {"name": "hamster/*"}),
            lambda s: s["macos_environment"]["protection_rules"].clear(),
            lambda s: s["publisher_branch_policies"]["branch_policies"][0].update(
                {"name": "*"}),
            lambda s: s["macos_environment"].update({"name": "renamed"}),
        ]
        for i, change in enumerate(mutations):
            s = snapshot()
            change(s)
            with self.subTest(case=i):
                self.assertEqual(audit_snapshot(s)["decision"],
                                 "BLOCKED_INCOMPLETE_OR_UNSAFE")

    def test_negative_secret_custody_and_permission_conditions(self):
        mutations = [
            lambda s: s["repository_secrets"]["secrets"].append(
                {"name": "MHB_ATC_WORKER_APP_PRIVATE_KEY"}),
            lambda s: s["macos_secrets"]["secrets"].clear(),
            lambda s: s["broker_secrets"]["secrets"].clear(),
            lambda s: s["publisher_secrets"]["secrets"].clear(),
            lambda s: s["default_token"].update(
                {"default_workflow_permissions": "write"}),
            lambda s: s["default_token"].update(
                {"can_approve_pull_request_reviews": True}),
            lambda s: s["app_public"]["permissions"].update(
                {"pull_requests": "write"}),
            lambda s: s["app_public"].update({"id": 123}),
        ]
        for i, change in enumerate(mutations):
            s = snapshot()
            change(s)
            with self.subTest(case=i):
                self.assertEqual(audit_snapshot(s)["decision"],
                                 "BLOCKED_INCOMPLETE_OR_UNSAFE")

    def test_activation_and_principal_mismatches_fail(self):
        for name in ("MHB_ATC_WORKER_BROKER_ENABLED",
                     "MHB_ATC_IMMUTABLE_HEADS_ENABLED",
                     "MHB_ATC_AUTO_ADMIT_ENABLED",
                     "MHB_ATC_PHASE2_STAGE_BRIDGE_ENABLED"):
            s = snapshot()
            next(x for x in s["variables"]["variables"]
                 if x["name"] == name)["value"] = "TRUE"
            with self.subTest(name=name):
                self.assertEqual(audit_snapshot(s)["decision"],
                                 "BLOCKED_INCOMPLETE_OR_UNSAFE")
        for field, value in [("id", 1), ("login", "untrusted")]:
            s = snapshot()
            s["actor"][field] = value
            with self.subTest(field=field):
                self.assertEqual(audit_snapshot(s)["decision"],
                                 "BLOCKED_INCOMPLETE_OR_UNSAFE")
        s = snapshot()
        s["checkout_sha"] = "b" * 40
        self.assertEqual(audit_snapshot(s)["decision"],
                         "BLOCKED_INCOMPLETE_OR_UNSAFE")

    def test_live_collection_refuses_actions_even_without_gh_login(self):
        env = dict(os.environ, GITHUB_ACTIONS="true")
        ran = subprocess.run([sys.executable,
                              str(ROOT / "scripts/mhb_atc_live_authority.py")],
                             cwd=ROOT, env=env, capture_output=True, text=True)
        self.assertEqual(ran.returncode, 2)
        self.assertIn("Refusing live owner-settings capture", ran.stderr)


if __name__ == "__main__":
    unittest.main()
