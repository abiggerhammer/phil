#!/usr/bin/env python3
"""Offline W3 publisher-only fanout canary, cleanup and STOP regressions."""
from __future__ import annotations

import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import yaml
from test_mhb_atc_staged_push_ci import StrictWorkflowLoader
from test_mhb_atc_w3_ref_trial import (
    FakeAPI, FakeDefaultWorkflowQuarantine, MAIN)
from mhb_atc_w3_ref_trial import Reply
from mhb_atc_w3_fanout_provenance import (
    TARGET, TREE, FanoutStop, make_binding,
    current_policy, policy_check, nonce_ref,
)
from mhb_atc_w3_fanout_evidence import FanoutLedger
from mhb_atc_w3_fanout_probe import (
    FanoutTrial, publisher_identity, ROOT,
)

NONCE = "f1e2d3c4b5a6"
REF = nonce_ref(NONCE)
BRANCH = REF.removeprefix("refs/heads/")
ORIGIN = make_binding(NONCE, MAIN, 12345678, "b"*40)


def make_trial(*, client=None, dispatch=MAIN):
    api = FakeAPI("publisher") if client is None else client
    validator = FakeDefaultWorkflowQuarantine(api)
    trial = FanoutTrial(api, nonce=NONCE, dispatch_sha=dispatch,
                        origin=ORIGIN, publisher_attestation=api.policy,
                        validator=validator)
    return api, trial, validator


def attach(trial, path, phase):
    trial.evidence = FanoutLedger(
        path / "w3-fanout-evidence.json", phase=phase, nonce=NONCE,
        run_id=12345678, original_run_id=12345678,
        dispatch_sha=trial.dispatch_sha, original_dispatch_sha=MAIN,
        target_sha=TARGET, workflow_tree_sha=TREE,
        installation_id="987654321")
    return trial.evidence


class PublisherCanaryTests(unittest.TestCase):
    def test_source_policy_activation_requires_exact_nonce(self):
        policy = current_policy(ROOT)
        # Main is dormant; a separately reviewed activation PR may be active.
        # Test both authorization states without requiring a particular
        # candidate nonce to appear in every checkout.
        self.assertIs(policy["source_authorized"],
                      policy["approved_nonce"] is not None)
        self.assertEqual(policy["frozen_target_sha"],TARGET)
        self.assertEqual(policy["reviewed_target_workflows_sha"],TREE)
        if policy["source_authorized"]:
            self.assertEqual(policy_check(policy,nonce=policy["approved_nonce"],
                                          require_active=True),policy)
        inactive=dict(policy,source_authorized=False,approved_nonce=None)
        with self.assertRaisesRegex(FanoutStop,"activation/nonce"):
            policy_check(inactive,nonce=NONCE,require_active=True)
        active=dict(policy,source_authorized=True,approved_nonce=NONCE)
        self.assertEqual(policy_check(active,nonce=NONCE,require_active=True),
                         active)
        with self.assertRaisesRegex(FanoutStop,"activation/nonce"):
            policy_check(active,nonce="000000000000",require_active=True)
        for bad in ("../main","A"*12,"f"*11,"g"*12):
            with self.assertRaises(FanoutStop):
                nonce_ref(bad)

    def test_workflow_manual_only_with_three_trusted_jobs(self):
        source=(ROOT/".github/workflows/mhb-atc-w3-publisher-fanout.yml"
                ).read_text()
        workflow=yaml.load(source,Loader=StrictWorkflowLoader)
        self.assertEqual(set(workflow["on"]),{"workflow_dispatch"})
        self.assertEqual(set(workflow["jobs"]),{
            "prepare","publisher_create","publisher_cleanup"})
        self.assertEqual(workflow["permissions"],
                         {"contents":"read","actions":"read"})
        self.assertEqual(workflow["concurrency"]["cancel-in-progress"],"false")
        self.assertEqual(workflow["concurrency"]["group"],
                         "mhb-atc-admission-global")
        self.assertIn("vars.MHB_ATC_W3_FANOUT_ENABLED == 'true'",
                      workflow["jobs"]["publisher_create"]["if"])
        cleanup_if=workflow["jobs"]["publisher_cleanup"]["if"]
        self.assertIn("always()",cleanup_if)
        self.assertIn("needs.prepare.result == 'success'",cleanup_if)
        self.assertIn("needs.publisher_create.result == 'failure'",cleanup_if)
        self.assertIn("needs.publisher_create.result == 'cancelled'",cleanup_if)
        self.assertIn("inputs.mode == 'cleanup'",cleanup_if)
        # Turning the runtime switch OFF after original CREATE must never
        # suppress the separately authorized original-run cleanup job.
        self.assertNotIn("vars.MHB_ATC_W3_FANOUT_ENABLED",cleanup_if)
        for job in workflow["jobs"].values():
            checkouts=[step for step in job["steps"]
                       if step.get("uses","").startswith("actions/checkout@")]
            self.assertEqual(len(checkouts),1)
            self.assertEqual(checkouts[0]["with"],{
                "ref":"${{ github.sha }}","fetch-depth":"0",
                "persist-credentials":"false"})
        for name in ("publisher_create","publisher_cleanup"):
            self.assertEqual(workflow["jobs"][name]["environment"],
                             "atc-publisher")
            steps=workflow["jobs"][name]["steps"]
            key_step=next(i for i,s in enumerate(steps)
                          if "create-github-app-token@" in s.get("uses",""))
            self.assertTrue(any("preflight" in s.get("name","").lower()
                                for s in steps[:key_step]))
            self.assertTrue(any("Install hash-pinned" in s.get("name","")
                                for s in steps[:key_step]))
            token=steps[key_step]
            self.assertEqual(token["with"]["permission-contents"],"write")
            self.assertEqual(token["with"]["skip-token-revoke"],"false")
            self.assertNotIn("permission-pull-requests",token["with"])
        self.assertEqual(source.count("actions/download-artifact@v4"),3)
        self.assertEqual(source.count("actions/create-github-app-token@"),2)
        self.assertIn("if: always()",source)
        self.assertNotIn("\n  push:",source)
        self.assertNotIn("\n  pull_request:",source)
        self.assertNotIn("\n  workflow_run:",source)

    def test_exact_one_create_and_delete_with_fsynced_evidence(self):
        with tempfile.TemporaryDirectory() as td,\
             patch.dict(os.environ,{"RUNNER_TEMP":td}):
            api,trial,validator=make_trial()
            ledger=attach(trial,Path(td),"publisher-create")
            original=api.request
            seen=[]
            def checked(method,route,data=None):
                if method!="GET":
                    doc=json.loads(ledger.path.read_text())
                    self.assertEqual(doc["events"][-1]["stage"],"INTENT")
                    self.assertEqual(doc["events"][-1]["ref"],REF)
                    self.assertTrue(doc["default_quarantine_checks"])
                    seen.append((method,route))
                return original(method,route,data)
            api.request=checked
            created=trial.create_once()
            ledger.decision("CREATE_VERIFIED")
            self.assertEqual(created["decision"],
                             "CREATE_CONFIRMED_CLEANUP_STILL_REQUIRED")
            self.assertEqual(api.refs,{BRANCH:TARGET})
            self.assertEqual(seen,[("POST","/git/refs")])
            self.assertEqual(ledger.path.stat().st_mode & 0o777,0o600)
            self.assertFalse(ledger.doc["quarantine_certified"])
            self.assertFalse(ledger.doc["w3_execution_authorized"])
            # Simulate a fresh runner's separate cleanup ledger.
            trial.evidence=None
            second=ledger_for_cleanup(Path(td),NONCE)
            trial.evidence=second
            deleted=trial.cleanup_once()
            second.decision("ABSENCE_VERIFIED")
            self.assertEqual(deleted["decision"],"EXACT_CANARY_ABSENT")
            self.assertEqual(api.refs,{})
            self.assertEqual(seen,[
                ("POST","/git/refs"),
                ("DELETE","/git/refs/heads/"+BRANCH)])
            self.assertEqual([x["operation"] for x in
                second.doc["default_quarantine_checks"]],
                ["publisher-delete-canary"])

    def test_recovery_when_main_moves_revalidates_actual_current_tree(self):
        with tempfile.TemporaryDirectory() as td,\
             patch.dict(os.environ,{"RUNNER_TEMP":td}):
            api,trial,validator=make_trial()
            api.refs[BRANCH]=TARGET
            api.main="e"*40
            attach(trial,Path(td),"publisher-cleanup")
            result=trial.cleanup_once()
            self.assertEqual(result["decision"],"EXACT_CANARY_ABSENT")
            self.assertEqual(validator.checked,["e"*40])
            self.assertEqual(trial.default_checks[0]["default_sha"],"e"*40)
            self.assertNotIn(BRANCH,api.refs)
            self.assertEqual([method for method,_,_ in api.requests
                              if method!="GET"],["DELETE"])

    def test_absence_is_idempotent_and_does_not_mint_or_delete(self):
        api,trial,_=make_trial()
        self.assertEqual(trial.gate(allow_drift=True,cleanup=True),None)
        self.assertIsNone(trial.ref_sha())
        self.assertTrue(all(m=="GET" for m,_,_ in api.requests))

    def test_unsafe_default_rejected_before_create_or_cleanup_delete(self):
        with tempfile.TemporaryDirectory() as td,\
             patch.dict(os.environ,{"RUNNER_TEMP":td}):
            api,trial,_=make_trial()
            api.default_workflows_unsafe=True
            attach(trial,Path(td),"publisher-create")
            with self.assertRaisesRegex(ValueError,"current default"):
                trial.create_once()
            self.assertEqual([m for m,_,_ in api.requests if m!="GET"],[])
            self.assertEqual(api.refs,{})
            api.default_workflows_unsafe=False
            api.refs[BRANCH]=TARGET
            trial.evidence=None
            # Reusing this runner temp is test-only; runner jobs are distinct.
            trial.evidence=ledger_for_cleanup(Path(td),NONCE)
            api.default_workflows_unsafe=True
            api.requests.clear()
            with self.assertRaisesRegex(ValueError,"current default"):
                trial.cleanup_once()
            self.assertEqual(api.refs,{BRANCH:TARGET})
            self.assertTrue(all(m=="GET" for m,_,_ in api.requests))

    def test_foreign_or_occupied_namespace_prevents_both_mutations(self):
        for occupied in (
                {"hamster/admitted/other":"a"*40},
                {BRANCH:"b"*40}):
            with self.subTest(occupied=occupied):
                api,trial,_=make_trial()
                api.refs.update(occupied)
                with self.assertRaises(ValueError):
                    trial.gate(cleanup=False)
                with self.assertRaises(ValueError):
                    trial.gate(allow_drift=True,cleanup=True)
                self.assertTrue(all(m=="GET" for m,_,_ in api.requests))

    def test_ambiguous_post_persists_intent_and_never_retries(self):
        with tempfile.TemporaryDirectory() as td,\
             patch.dict(os.environ,{"RUNNER_TEMP":td}):
            api,trial,_=make_trial()
            attach(trial,Path(td),"publisher-create")
            original=api.request
            writes=[]
            def interrupted(method,route,data=None):
                answer=original(method,route,data)
                if method=="POST":
                    writes.append(route)
                    raise OSError("sensitive injected remote error")
                return answer
            api.request=interrupted
            with self.assertRaises(OSError):
                trial.create_once()
            self.assertEqual(writes,["/git/refs"])
            self.assertEqual(api.refs,{BRANCH:TARGET})
            doc=json.loads(trial.evidence.path.read_text())
            self.assertEqual([x["stage"] for x in doc["events"]],
                             ["INTENT","STOP"])
            self.assertEqual(doc["events"][-1]["reason"],
                             "UNKNOWN_AFTER_REQUEST")
            self.assertNotIn("sensitive",str(doc).lower())

    def test_unexpected_delete_response_stops_without_false_absence(self):
        with tempfile.TemporaryDirectory() as td,\
             patch.dict(os.environ,{"RUNNER_TEMP":td}):
            api,trial,_=make_trial()
            api.refs[BRANCH]=TARGET
            attach(trial,Path(td),"publisher-cleanup")
            original=api.request
            def wrong(method,route,data=None):
                if method=="DELETE":
                    original(method,route,data)
                    return Reply(202,{"message":"unexpected completed"})
                return original(method,route,data)
            api.request=wrong
            with self.assertRaisesRegex(FanoutStop,"not independently proven"):
                trial.cleanup_once()
            self.assertEqual(api.refs,{})
            self.assertTrue(any(x["stage"]=="RESPONSE" and
                x["http_status"]==202 for x in trial.evidence.doc["events"]))
            self.assertEqual(trial.evidence.doc["decision"],
                             "INCOMPLETE_NOT_CERTIFIED")

    def test_publisher_token_must_have_correct_slug_and_one_repo(self):
        api,_,_=make_trial()
        with patch.dict(os.environ,{
                "W3_FANOUT_ACTION_APP_SLUG":"phil-atc-publisher",
                "W3_FANOUT_ACTION_INSTALLATION_ID":"987"}):
            self.assertEqual(publisher_identity(api),"987")
        with patch.dict(os.environ,{
                "W3_FANOUT_ACTION_APP_SLUG":"wrong-publisher",
                "W3_FANOUT_ACTION_INSTALLATION_ID":"987"}):
            with self.assertRaisesRegex(FanoutStop,"wrong App slug"):
                publisher_identity(api)
        api.failures[("GET","/installation/repositories")] = Reply(200,{
            "total_count":2,"repositories":[{"full_name":"abiggerhammer/phil"},
                                            {"full_name":"foreign/repo"}]})
        with patch.dict(os.environ,{
                "W3_FANOUT_ACTION_APP_SLUG":"phil-atc-publisher",
                "W3_FANOUT_ACTION_INSTALLATION_ID":"987"}):
            with self.assertRaisesRegex(FanoutStop,"Phil only"):
                publisher_identity(api)


def ledger_for_cleanup(path,nonce):
    # Use the same runner temp and fresh path only for fixture convenience.
    old=path/"w3-fanout-evidence.json"
    if old.exists():
        old.unlink()
    return FanoutLedger(old,phase="publisher-cleanup",nonce=nonce,
        run_id=12345678,original_run_id=12345678,
        dispatch_sha=MAIN,original_dispatch_sha=MAIN,
        target_sha=TARGET,workflow_tree_sha=TREE,installation_id="987654321")


if __name__=="__main__":
    unittest.main()
