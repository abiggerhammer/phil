#!/usr/bin/env python3
"""Synthetic W3 security-plan negative replays. NO live credential or GitHub write."""
from __future__ import annotations

import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from mhb_atc_w3_readiness import (
    REPO, WORKER_APP_ID, PUBLISHER_APP_ID, RULESET_ID,
    plan, load_json, unique_keys,
)

ROOT = Path(__file__).resolve().parents[1]
HEAD = "a" * 40
NONCE = "a1b2c3d4e5f6"


def fixture():
    worker = json.loads((ROOT / ".github/atc-worker-policy.json").read_text())
    lanes = json.loads((ROOT / ".github/atc-worker-lanes.json").read_text())
    publisher = json.loads((ROOT / ".github/atc-publisher-policy.json").read_text())
    rule = {
        "id": RULESET_ID,
        "target": "branch",
        "enforcement": "active",
        "source_type": "Repository",
        "source": REPO,
        "created_at": publisher["ruleset_created_at"],
        "updated_at": publisher["ruleset_updated_at"],
        "conditions": {"ref_name": {
            "exclude": [], "include": ["refs/heads/hamster/admitted/*"]}},
        "rules": [
            {"type": "creation"}, {"type": "update"},
            {"type": "deletion"}, {"type": "non_fast_forward"}],
        "bypass_actors": [{"actor_id": PUBLISHER_APP_ID,
                           "actor_type": "Integration",
                           "bypass_mode": "always"}],
        "current_user_can_bypass": "never",
    }
    main = {"ref": "refs/heads/main",
            "object": {"type": "commit", "sha": HEAD}}
    return dict(
        ruleset=rule, admitted_refs=[],
        before=main, after=copy.deepcopy(main),
        worker=worker, lanes=lanes, publisher=publisher,
        expected_sha=HEAD, nonce=NONCE)


class W3ReadinessTests(unittest.TestCase):
    def test_happy_path_is_proposal_not_w3_commissioning(self):
        r = plan(**fixture())
        self.assertEqual(r["decision"],
                         "SOURCE_READINESS_CONFIRMED_REVIEW_REQUIRED")
        self.assertFalse(r["execution_authorized"])
        self.assertFalse(r["credential_access_performed"])
        self.assertFalse(r["api_writes_performed"])
        self.assertEqual(r["admitted_refs_at_snapshot"], 0)
        self.assertEqual(r["publisher_app_id"], PUBLISHER_APP_ID)
        self.assertEqual(r["worker_app_id"], WORKER_APP_ID)
        self.assertTrue(r["disposable_create_ref"].endswith("-create"))
        self.assertTrue(r["publisher_seed_ref"].endswith("-seed"))
        self.assertEqual(len(r["planned_sequence"]), 6)
        self.assertNotIn("PRIVATE_KEY", json.dumps(r))
        self.assertNotIn("ghp_", json.dumps(r))

    def test_only_publisher_in_ruleset_bypass(self):
        cases = [
            lambda d: d["ruleset"]["bypass_actors"].append({
                "actor_id": WORKER_APP_ID, "actor_type": "Integration",
                "bypass_mode": "always"}),
            lambda d: d["ruleset"].update(bypass_actors=None),
            lambda d: d["ruleset"].update(bypass_actors=[]),
            lambda d: d["ruleset"].update(current_user_can_bypass="always"),
            lambda d: d["ruleset"]["bypass_actors"][0].update(
                actor_id=WORKER_APP_ID),
        ]
        for i, mutation in enumerate(cases):
            v = fixture();mutation(v)
            with self.subTest(i=i), self.assertRaises(ValueError):
                plan(**v)

    def test_all_protected_rule_kinds_mandatory(self):
        for typ in ("creation", "update", "deletion", "non_fast_forward"):
            v = fixture()
            v["ruleset"]["rules"] = [
                r for r in v["ruleset"]["rules"] if r["type"] != typ]
            with self.subTest(missing=typ), self.assertRaises(ValueError):
                plan(**v)
        for extra in ({"type": "unknown"}, {"type": "creation", "parameters": {}}):
            v = fixture()
            v["ruleset"]["rules"].append(extra)
            with self.subTest(extra=extra), self.assertRaises(ValueError):
                plan(**v)

    def test_ruleset_version_source_and_namespace_pin(self):
        cases = [
            lambda d: d["ruleset"].update(updated_at="2026-11-20T04:00:00Z"),
            lambda d: d["ruleset"].update(enforcement="evaluate"),
            lambda d: d["ruleset"].update(source="other/repo"),
            lambda d: d["ruleset"]["conditions"]["ref_name"].update(
                include=["refs/heads/*"]),
            lambda d: d["publisher"].update(ruleset_id=8),
            lambda d: d["publisher"].update(publisher_app_id=WORKER_APP_ID),
        ]
        for i, change in enumerate(cases):
            v = fixture();change(v)
            with self.subTest(i=i), self.assertRaises(ValueError):
                plan(**v)

    def test_admitted_ref_census_must_be_empty(self):
        for refs in (
            [{"ref": "refs/heads/hamster/admitted/active",
              "object": {"sha": HEAD, "type": "commit"}}],
            [{"ref": "refs/heads/hamster/staged/foreign",
              "object": {"sha": HEAD, "type": "commit"}}],
            [{"ref": "refs/heads/hamster/admitted/bad",
              "object": {"sha": "invalid", "type": "commit"}}],
            "not an array",
            [{}],
            [{"ref": "refs/heads/hamster/admitted/active",
              "object": {"sha": HEAD, "type": "commit"}}] * 101,
        ):
            v = fixture();v["admitted_refs"] = refs
            with self.subTest(refs=str(refs)[:60]), self.assertRaises(ValueError):
                plan(**v)

    def test_disabled_worker_and_lane_registry_required(self):
        cases = [
            lambda d: d["worker"].update(broker_activation="enabled"),
            lambda d: d["worker"].update(worker_app_id=PUBLISHER_APP_ID),
            lambda d: d["worker"].update(direct_worker_installation_tokens=True),
            lambda d: d["worker"]["intended_permissions"].update(
                pull_requests="write"),
            lambda d: d["lanes"]["lanes"]["phase2-selfhost"].update(enabled=True),
            lambda d: d["lanes"]["lanes"]["phase2-embedded"].update(
                source_repository="attacker/phil"),
            lambda d: d["lanes"]["lanes"].update(extra={"enabled": False}),
        ]
        for i, change in enumerate(cases):
            v=fixture();change(v)
            with self.subTest(i=i), self.assertRaises(ValueError):
                plan(**v)

    def test_clean_main_and_nonce_mandatory(self):
        cases = [
            lambda d: d["after"]["object"].update(sha="b"*40),
            lambda d: d.update(expected_sha="b"*40),
            lambda d: d["before"].update(ref="refs/heads/wrong"),
            lambda d: d.update(nonce="../main"),
            lambda d: d.update(nonce="a"*13),
            lambda d: d.update(nonce="Z"*12),
        ]
        for i,change in enumerate(cases):
            v=fixture();change(v)
            with self.subTest(i=i), self.assertRaises(ValueError):
                plan(**v)

    def test_duplicate_or_oversized_snapshot_fails_closed(self):
        with tempfile.TemporaryDirectory() as d:
            path=Path(d)/"snap.json"
            path.write_text('{"id":1,"id":2}')
            with self.assertRaisesRegex(ValueError, "duplicate JSON"):
                load_json(path)
            path.write_text('"' + "x" * 4_000_001 + '"')
            with self.assertRaisesRegex(ValueError, "oversized"):
                load_json(path)

    def test_no_runtime_remote_execution_path_in_plan(self):
        source = (ROOT / "scripts/mhb_atc_w3_readiness.py").read_text()
        self.assertNotIn('["gh",', source)
        self.assertNotIn('["curl",', source)
        self.assertNotIn("create-github-app-token", source)
        self.assertNotIn("github.rest", source)
        self.assertNotIn("requests.post", source)
        self.assertIn('"execution_authorized": False', source)
        self.assertIn('"api_writes_performed": False', source)
        self.assertNotIn("git push", source)

    def test_collector_explicitly_refuses_github_actions(self):
        p = subprocess.run(
            [sys.executable, str(ROOT / "scripts/mhb_atc_w3_readiness.py")],
            cwd=ROOT, env={"GITHUB_ACTIONS": "true"},
            capture_output=True, text=True)
        self.assertEqual(p.returncode, 2)
        self.assertIn("must not run inside Actions", p.stderr)


if __name__ == "__main__":
    unittest.main()
