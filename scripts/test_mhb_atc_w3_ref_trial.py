#!/usr/bin/env python3
"""Fake-transport W3 executable trial and publisher cleanup regression suite.

No network, App key, installation token or repository write can occur here.
"""
from __future__ import annotations

import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
import yaml

from test_mhb_atc_staged_push_ci import StrictWorkflowLoader
import mhb_atc_w3_ref_trial as module

from mhb_atc_w3_ref_trial import (
    REPO, PUBLISHER_ID, WORKER_ID, RULESET_ID,
    Client, _NoRedirect, Reply, StopTrial, Trial, names, policy_check, sha,
    attest_live_worker_identity,
)

ROOT = Path(__file__).resolve().parents[1]
MAIN = "a" * 40
PARENT = "b" * 40
GRANDPARENT = "c" * 40
NONCE = "d1e2f3a4b5c6"


def reviewed_attestation():
    return json.loads((ROOT / ".github/atc-publisher-policy.json").read_text())


def ruleset(policy):
    return {
        "id": RULESET_ID, "target": "branch", "enforcement": "active",
        "source_type": "Repository", "source": REPO,
        "created_at": policy["ruleset_created_at"],
        "updated_at": policy["ruleset_updated_at"],
        "conditions": {"ref_name": {
            "include": ["refs/heads/hamster/admitted/*"], "exclude": []}},
        "rules": [{"type": t} for t in (
            "creation", "update", "deletion", "non_fast_forward")],
        "bypass_actors": [{"actor_id": PUBLISHER_ID,
                           "actor_type": "Integration",
                           "bypass_mode": "always"}],
    }


class FakeAPI:
    def __init__(self, role, nonce=NONCE, *, rule_denial=True):
        self.role = role
        self.nonce = nonce
        self.rule_denial = rule_denial
        self.refs = {}
        self.requests = []
        self.policy = reviewed_attestation()
        self.rule = ruleset(self.policy)
        self.main = MAIN
        self.failures = {}
        self.extra_ref = None

    def write_result(self, endpoint, status=422):
        if not self.rule_denial:
            return Reply(status, {"message": "Validation Failed"})
        return Reply(status, {"message":
            "GH013: Repository rule violations found for refs/heads/" +
            endpoint.removeprefix("/git/refs/heads/"),
            "errors": [{"message": "Repository rule violations found for " +
                        endpoint.removeprefix("/git/refs/heads/")}]})

    def request(self, method, endpoint, data=None):
        self.requests.append((method, endpoint, copy.deepcopy(data)))
        if (method, endpoint) in self.failures:
            return self.failures[(method, endpoint)]
        if method == "GET" and endpoint == "/rulesets/27365284":
            return Reply(200, copy.deepcopy(self.rule))
        if method == "GET" and endpoint == "/git/ref/heads/main":
            return Reply(200, {"ref": "refs/heads/main",
                                "object": {"type": "commit", "sha": self.main}})
        if method == "GET" and endpoint == "/installation/repositories":
            return Reply(200, {"total_count": 1,
                               "repositories": [{"full_name": REPO}]})
        if method == "GET" and endpoint == "/git/matching-refs/heads/hamster/admitted/":
            return Reply(200, [
                {"ref": "refs/heads/" + k,
                 "object": {"sha": v, "type": "commit"}}
                for k, v in self.refs.items()])
        if (endpoint.startswith("/git/ref/heads/") or
                endpoint.startswith("/git/refs/heads/")):
            if method == "GET":
                require_prefix = "/git/ref/heads/"
            else:
                require_prefix = "/git/refs/heads/"
            if not endpoint.startswith(require_prefix):
                raise AssertionError("wrong read/write Git refs API route")
            name = endpoint[len(require_prefix):]
            if method == "GET":
                return (Reply(200, {"ref": "refs/heads/" + name,
                                    "object": {"sha": self.refs[name],
                                               "type": "commit"}})
                        if name in self.refs else
                        Reply(404, {"message": "Not Found"}))
            if self.role == "worker":
                if method == "DELETE":
                    return self.write_result(endpoint)
                return self.write_result(endpoint)
            if method == "DELETE":
                if name not in self.refs:
                    return Reply(404, {"message": "Not Found"})
                del self.refs[name]
                return Reply(204, {})
            if method == "PATCH":
                if name not in self.refs:
                    return Reply(404, {"message": "Not Found"})
                self.refs[name] = data["sha"]
                return Reply(200, {})
        if method == "POST" and endpoint == "/git/refs":
            name = data["ref"].removeprefix("refs/heads/")
            if self.role == "worker":
                return self.write_result("/git/refs/heads/" + name)
            if name in self.refs:
                return Reply(422, {"message": "Reference already exists"})
            self.refs[name] = data["sha"]
            return Reply(201, {"ref": data["ref"]})
        raise AssertionError("Unexpected simulated GitHub API route " +
                             method + " " + endpoint)


def make(role="publisher", nonce=NONCE, *, api=None):
    api = FakeAPI(role, nonce) if api is None else api
    trial = Trial(api, nonce, MAIN, PARENT, GRANDPARENT, api.policy)
    return api, trial


class W3RefTrialTests(unittest.TestCase):
    def test_source_policy_is_dormant_and_cannot_authorize_live_execution(self):
        snapshot = policy_check(live=False)
        self.assertEqual(snapshot["publisher_app_id"], PUBLISHER_ID)
        self.assertFalse(json.loads(
            (ROOT / ".github/atc-w3-ref-trial.json").read_text()
        )["live_authorized"])
        with self.assertRaisesRegex(StopTrial, "DISABLED"):
            policy_check(live=True)

    def test_live_authority_requires_reviewed_nonce_quarantine_var_and_owner(self):
        real_read = module.read
        changed = json.loads((ROOT / ".github/atc-w3-ref-trial.json").read_text())
        changed.update(live_authorized=True, approved_nonce=NONCE,
                       push_ci_quarantine_verified=True)
        def read_for_test(path):
            return changed if path == ".github/atc-w3-ref-trial.json" else real_read(path)

        authorized = dict(os.environ,
                          GITHUB_ACTIONS="true",
                          GITHUB_EVENT_NAME="workflow_dispatch",
                          GITHUB_ACTOR="abiggerhammer",
                          GITHUB_TRIGGERING_ACTOR="abiggerhammer",
                          GITHUB_RUN_ATTEMPT="1",
                          GITHUB_REPOSITORY=REPO,
                          GITHUB_REF="refs/heads/main",
                          W3_CONFIRM="AUTHORIZE_W3_PROTECTED_REFS_ONLY",
                          MHB_ATC_W3_REF_TRIAL_ENABLED="true",
                          MHB_ATC_AUTO_ADMIT_ENABLED="false",
                          MHB_ATC_IMMUTABLE_HEADS_ENABLED="false",
                          MHB_ATC_PHASE2_STAGE_BRIDGE_ENABLED="false",
                          MHB_ATC_WORKER_BROKER_ENABLED="false")
        with patch.object(module, "read", side_effect=read_for_test), \
             patch.dict(os.environ, authorized, clear=True):
            self.assertEqual(policy_check(live=True, nonce=NONCE)["publisher_app_id"],
                             PUBLISHER_ID)
            for key, value in [
                ("GITHUB_REF", "refs/heads/hamster/staged/attacker"),
                ("GITHUB_ACTOR", "unexpected-user"),
                ("GITHUB_TRIGGERING_ACTOR", "unexpected-user"),
                ("GITHUB_RUN_ATTEMPT", "2"),
                ("MHB_ATC_W3_REF_TRIAL_ENABLED", "false"),
                ("W3_CONFIRM", "PLAN_ONLY"),
                ("MHB_ATC_AUTO_ADMIT_ENABLED", "true"),
            ]:
                with self.subTest(key=key), \
                     patch.dict(os.environ, {key: value}), \
                     self.assertRaises(StopTrial):
                    policy_check(live=True, nonce=NONCE)
            with self.assertRaisesRegex(StopTrial, "source-pinned"):
                policy_check(live=True, nonce="e"*12)
            # Recovery MUST still be available if the operator turns OFF
            # the runtime switch immediately after a seed attempt.
            with patch.dict(os.environ, {
                    "MHB_ATC_W3_REF_TRIAL_ENABLED": "false",
                    "MHB_ATC_AUTO_ADMIT_ENABLED": "true",
                    "W3_CONFIRM": "RECOVER_W3_EXACT_REFS_ONLY"}):
                self.assertEqual(
                    policy_check(live=True, nonce=NONCE, recovery=True)[
                        "publisher_app_id"], PUBLISHER_ID)
                with self.assertRaises(StopTrial):
                    policy_check(live=True, nonce=NONCE, recovery=False)
            changed["push_ci_quarantine_verified"] = False
            with self.assertRaisesRegex(StopTrial, "quarantine NOT reviewed"):
                policy_check(live=True, nonce=NONCE)
            changed["push_ci_quarantine_verified"] = True
            changed["live_authorized"] = False
            with self.assertRaisesRegex(StopTrial, "DISABLED"):
                policy_check(live=True, nonce=NONCE)

    def test_worker_token_id_must_match_authenticated_JWT_receipt(self):
        receipt = {
            "decision": "authenticated-worker-app-and-installation",
            "app_id": WORKER_ID, "app_slug": "phil-atc-worker",
            "permissions": {"contents": "write", "metadata": "read"},
            "repository_selection": "selected",
            "installation_id": 987654,
        }
        attest_live_worker_identity(receipt, "987654")
        for key, wrong in [
            ("app_id", PUBLISHER_ID),
            ("app_slug", "phil-atc-publisher"),
            ("permissions", {"contents": "write", "pull_requests": "write"}),
            ("repository_selection", "all"),
            ("installation_id", 0),
        ]:
            bad = dict(receipt)
            bad[key] = wrong
            with self.subTest(key=key), self.assertRaises(StopTrial):
                attest_live_worker_identity(bad, "987654")
        with self.assertRaises(StopTrial):
            attest_live_worker_identity(receipt, "987655")

    def test_real_worker_job_reuses_accepted_W1_JWT_step_byte_for_byte(self):
        original = (ROOT / ".github/workflows/mhb-atc-worker-token-preflight.yml").read_text()
        trial = (ROOT / ".github/workflows/mhb-atc-w3-ref-commissioning.yml").read_text()
        start = "      - name: Authenticate worker App numeric ID and full installed grants (JWT GET only)\n"
        after = "      - name: Mint repository-scoped worker App token for read-only verification\n"
        first = original.split(start, 1)[1].split(after, 1)[0]
        copied = trial.split(start, 1)[1].split(
            "      - name: Mint worker App token only inside protected broker environment\n", 1)[0]
        self.assertEqual(copied, first)
        self.assertIn("attest_live_worker_identity(", (ROOT / "scripts/mhb_atc_w3_ref_trial.py").read_text())

    def test_real_transport_uses_only_exact_https_github_urls_and_denies_redirect(self):
        class Response:
            status = 200
            def __enter__(self): return self
            def __exit__(self, *args): pass
            def read(self, amount): return b'{"total_count":1,"repositories":[{"full_name":"abiggerhammer/phil"}]}'
        observed = []
        class Opener:
            def open(self, req, timeout):
                observed.append((req.full_url, req.get_method(), req.data))
                return Response()
        with patch.object(module.request, "build_opener",
                          side_effect=lambda handler: Opener()):
            r = Client("nonsecret-fixture-token").request(
                "GET", "/installation/repositories")
            self.assertEqual(r.status, 200)
            Client("nonsecret-fixture-token").request(
                "POST", "/git/refs",
                {"ref": "refs/heads/hamster/admitted/w3-" + NONCE + "-seed",
                 "sha": PARENT})
        self.assertEqual(observed[0][:2],
                         ("https://api.github.com/installation/repositories", "GET"))
        self.assertEqual(observed[1][:2],
                         ("https://api.github.com/repos/abiggerhammer/phil/git/refs",
                          "POST"))
        self.assertTrue(isinstance(observed[1][2], bytes))
        self.assertIsNone(_NoRedirect().redirect_request(
            None, None, 302, "test", {}, "https://example.invalid/"))
        with self.assertRaises(StopTrial):
            Client(None).request("PATCH", "/git/refs/heads/main", {"sha": MAIN})
        with self.assertRaises(StopTrial):
            Client(None).request("GET", "/../foreign")

    def test_names_are_distinct_single_leaf_protected_refs(self):
        n = names(NONCE)
        self.assertEqual(set(n), {"canary", "create", "seed"})
        self.assertEqual(len(set(n.values())), 3)
        self.assertTrue(all(x.startswith("hamster/admitted/w3-") and
                            x.count("/") == 2 for x in n.values()))
        for bad in ("../main", "ABC123ABC123", "a"*13, "a"*11, "a"*12 + "/"):
            with self.subTest(bad=bad), self.assertRaises(StopTrial):
                names(bad)

    def test_publisher_canary_proves_cleanup_before_seed(self):
        api, trial = make()
        receipt = trial.publisher_seed()
        self.assertEqual(receipt["decision"], "PUBLISHER_CLEANUP_CANARY_PASSED")
        self.assertEqual(api.refs, {names(NONCE)["seed"]: PARENT})
        methods = [x[0] for x in api.requests if x[0] != "GET"]
        self.assertEqual(methods, ["POST", "DELETE", "POST"])
        self.assertNotIn(names(NONCE)["canary"], api.refs)

    def test_four_real_shaped_denials_are_serial_and_do_not_mutate_refs(self):
        api, p = make()
        p.publisher_seed()
        api.role = "worker"
        api.requests.clear()
        receipt = p.worker_probe()
        self.assertEqual(receipt["decision"], "FOUR_REF_RULE_DENIALS_OBSERVED")
        self.assertEqual([e["operation"] for e in receipt["events"]], [
            "publisher_create_delete_canary", "publisher_seed_at_first_parent",
            "deny-create", "deny-update", "deny-force-update", "deny-delete"])
        self.assertEqual([x[0] for x in api.requests if x[0] != "GET"],
                         ["POST", "PATCH", "PATCH", "DELETE"])
        updates = [x[2] for x in api.requests if x[0] == "PATCH"]
        self.assertEqual(updates, [{"sha": MAIN, "force": False},
                                   {"sha": GRANDPARENT, "force": True}])
        self.assertEqual(api.refs, {names(NONCE)["seed"]: PARENT})

    def test_ambiguous_validation_422_is_not_permission_proof(self):
        api, trial = make()
        trial.publisher_seed()
        api.role = "worker"
        api.rule_denial = False
        with self.assertRaisesRegex(StopTrial, "not exact-ref ruleset denial"):
            trial.worker_probe()
        self.assertEqual(api.refs, {names(NONCE)["seed"]: PARENT})
        self.assertEqual(len([x for x in api.requests if x[0] == "POST"]), 3)

    def test_any_unexpected_2xx_stops_without_next_worker_request(self):
        api, trial = make()
        trial.publisher_seed()
        api.role = "worker"
        path = "/git/refs"
        api.failures[("POST", path)] = Reply(201, {"ref": "unexpected"})
        api.requests.clear()
        with self.assertRaisesRegex(StopTrial, "unexpected or ambiguous"):
            trial.worker_probe()
        self.assertEqual([x[0] for x in api.requests if x[0] != "GET"], ["POST"])

    def test_denial_must_name_exact_nonce_ref_not_just_any_rule(self):
        api, trial = make()
        trial.publisher_seed()
        api.role = "worker"
        api.failures[("POST", "/git/refs")] = Reply(
            422, {"message": "GH013 Repository rule violations found for refs/heads/hamster/admitted/w3-incorrect-create"})
        with self.assertRaisesRegex(StopTrial, "wrong or ambiguous ref"):
            trial.worker_probe()

    def test_preflight_detects_occupied_namespace_or_drift(self):
        api, trial = make()
        api.refs["hamster/admitted/other"] = MAIN
        with self.assertRaisesRegex(StopTrial, "occupancy"):
            trial.publisher_seed()
        api.refs.clear()
        api.main = "f" * 40
        with self.assertRaisesRegex(StopTrial, "main moved"):
            trial.publisher_seed()
        api.main = MAIN
        api.rule["updated_at"] = "2026-11-20T23:59:59Z"
        with self.assertRaises(ValueError):
            trial.publisher_seed()

    def test_separate_get_only_recovery_plan_for_abandoned_seed(self):
        api, trial = make()
        api.refs[names(NONCE)["seed"]] = PARENT
        api.main = "f" * 40
        receipt = trial.publisher_recovery_plan()
        self.assertEqual(receipt["decision"], "EXACT_KNOWN_REF_CLEANUP_ELIGIBLE")
        self.assertFalse(receipt["execution_authorized"])
        self.assertEqual(receipt["refs"]["seed"], "KNOWN_DISPOSABLE")
        self.assertTrue(all(method == "GET" for method, _, _ in api.requests))
        self.assertEqual(api.refs[names(NONCE)["seed"]], PARENT)
        api.refs[names(NONCE)["seed"]] = "e" * 40
        with self.assertRaisesRegex(StopTrial, "UNKNOWN SHA"):
            trial.publisher_recovery_plan()

    def test_cleanup_removes_owned_exact_shas_after_success_or_ambiguous_failure(self):
        for role in ("publisher", "worker"):
            api, trial = make(role="publisher")
            trial.publisher_seed()
            api.role = role
            api.refs[names(NONCE)["create"]] = MAIN
            api.refs[names(NONCE)["seed"]] = GRANDPARENT
            api.refs[names(NONCE)["canary"]] = PARENT
            api.role = "publisher"
            api.main = "f"*40  # Cleanup may recover after main advances.
            receipt = trial.publisher_cleanup()
            self.assertEqual(receipt["decision"], "OWNED_DISPOSABLE_REFS_ABSENT")
            self.assertEqual(api.refs, {})
            self.assertEqual(len([x for x in api.requests if x[0] == "DELETE"]), 4)

    def test_cleanup_refuses_unknown_sha_and_does_not_delete_foreign_ref(self):
        api, trial = make()
        api.refs[names(NONCE)["seed"]] = "e" * 40
        api.refs["hamster/admitted/other"] = MAIN
        with self.assertRaisesRegex(StopTrial, "UNKNOWN SHA"):
            trial.publisher_cleanup()
        self.assertEqual(api.refs[names(NONCE)["seed"]], "e"*40)
        self.assertEqual(api.refs["hamster/admitted/other"], MAIN)
        self.assertEqual(len([x for x in api.requests if x[0] == "DELETE"]), 0)

    def test_worker_did_not_gain_pr_operation_and_secrets_are_not_reported(self):
        api, trial = make()
        r = trial.public_receipt("plan", "SOURCE_ONLY_PLAN_NO_WRITES")
        self.assertTrue(r["no_pr_operations"])
        self.assertNotIn("Bearer", json.dumps(r))
        self.assertNotIn("private-key", json.dumps(r))
        source = (ROOT / "scripts/mhb_atc_w3_ref_trial.py").read_text()
        self.assertNotIn('"/pulls"', source)
        self.assertNotIn("gh pr create", source)
        self.assertNotIn("subprocess.run(['gh'", source)

    def test_workflow_is_manual_env_separated_and_source_disabled(self):
        source = (ROOT / ".github/workflows/mhb-atc-w3-ref-commissioning.yml").read_text()
        self.assertIn("  workflow_dispatch:", source)
        self.assertNotIn("\n  pull_request:", source)
        self.assertNotIn("\n  push:", source)
        self.assertNotIn("\n  schedule:", source)
        self.assertIn("github.actor == 'abiggerhammer'", source)
        self.assertIn("github.triggering_actor == 'abiggerhammer'", source)
        self.assertIn("github.run_attempt == 1", source)
        self.assertIn("github.ref == 'refs/heads/main'", source)
        self.assertIn("vars.MHB_ATC_W3_REF_TRIAL_ENABLED == 'true'", source)
        self.assertIn("environment: atc-publisher", source)
        self.assertIn("environment: atc-worker-broker", source)
        self.assertIn("always()", source)
        self.assertIn("options: [plan, run, cleanup]", source)
        self.assertIn("recovery-plan --nonce", source)
        self.assertIn("RECOVER_W3_EXACT_REFS_ONLY", source)
        self.assertIn("persist-credentials: false", source)
        self.assertIn("MHB_ATC_W3_REF_TRIAL_ENABLED", source)
        self.assertIn("AUTH", source)
        self.assertIn("permission-contents: write", source)
        self.assertNotIn("permission-pull-requests: write", source)

    def test_cli_with_disabled_source_cannot_mint_or_write(self):
        env = dict(os.environ, GITHUB_ACTIONS="true",
                   GITHUB_ACTOR="abiggerhammer", GITHUB_REF="refs/heads/main",
                   GITHUB_REPOSITORY=REPO, GITHUB_EVENT_NAME="workflow_dispatch",
                   MHB_ATC_W3_REF_TRIAL_ENABLED="true",
                   W3_CONFIRM="AUTHORIZE_W3_PROTECTED_REFS_ONLY")
        p = subprocess.run(
            [sys.executable, str(ROOT / "scripts/mhb_atc_w3_ref_trial.py"),
             "publisher-seed", "--nonce", NONCE],
            cwd=ROOT, env=env, capture_output=True, text=True, timeout=15)
        self.assertEqual(p.returncode, 2)
        self.assertIn("DISABLED", p.stderr)
        self.assertNotIn("Token ", p.stderr)


if __name__ == "__main__":
    unittest.main()
