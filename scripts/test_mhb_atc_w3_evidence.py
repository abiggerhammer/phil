#!/usr/bin/env python3
"""Fake-transport W3 durable sanitized intent/denial/cleanup receipts."""
from __future__ import annotations
from contextlib import ExitStack, redirect_stderr, redirect_stdout
import http.client
import io
import json
import os
import sys
from urllib import error
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import mhb_atc_w3_ref_trial as module
from mhb_atc_w3_evidence import EvidenceLedger, EvidenceError, SCHEMA
from mhb_atc_w3_ref_trial import Reply, StopTrial
from test_mhb_atc_w3_ref_trial import (
    make, names, NONCE, MAIN, PARENT, GRANDPARENT)

TREE="d"*40
RUN=987654

def ledger(root, phase):
    return EvidenceLedger(
        root/"w3-evidence.json",phase=phase,nonce=NONCE,run_id=RUN,
        source_sha=MAIN,parent_sha=PARENT,grandparent_sha=GRANDPARENT,
        dispatch_sha="f"*40,workflow_tree_sha=TREE,
        app_id=5836223 if phase=="worker-negative" else 5782193,
        installation_id="123456789")

class EvidenceTests(unittest.TestCase):
    def test_intent_is_fsynced_before_each_real_shaped_publisher_write(self):
        with tempfile.TemporaryDirectory() as td, \
             patch.dict(os.environ,{"RUNNER_TEMP":td}):
            path=Path(td)/"w3-evidence.json"; log=io.StringIO()
            with redirect_stdout(log):
                audit=ledger(Path(td),"publisher-seed")
                api,trial=make();trial.evidence=audit
                original=api.request
                witnessed=[]
                def checked(method,endpoint,data=None):
                    if method!="GET":
                        doc=json.loads(path.read_text())
                        self.assertEqual(doc["events"][-1]["stage"],"INTENT")
                        self.assertIn(doc["events"][-1]["operation"],(
                            "publisher-create-canary","publisher-delete-canary",
                            "publisher-create-seed"))
                        witnessed.append(method)
                    return original(method,endpoint,data)
                api.request=checked
                result=trial.publisher_seed()
                audit.decision("PUBLISHER_SEED_CONFIRMED")
            self.assertEqual(witnessed,["POST","DELETE","POST"])
            self.assertEqual(result["decision"],"PUBLISHER_CLEANUP_CANARY_PASSED")
            doc=json.loads(path.read_text())
            self.assertEqual(doc["decision"],"PUBLISHER_SEED_CONFIRMED")
            self.assertEqual(doc["dispatch_sha"],"f"*40)
            self.assertEqual(doc["source_sha"],MAIN)
            self.assertEqual(doc["schema"],SCHEMA)
            self.assertEqual(len(doc["default_quarantine_checks"]),3)
            self.assertEqual([x["operation"] for x in
                doc["default_quarantine_checks"]],[
                "publisher-create-canary","publisher-delete-canary",
                "publisher-create-seed"])
            self.assertEqual(doc["default_quarantine_checks"][0]["default_sha"],MAIN)
            self.assertEqual(doc["default_quarantine_checks"][0][
                "default_workflow_tree_sha"],"d"*40)
            self.assertEqual(doc["app_id"],5782193)
            self.assertEqual(doc["installation_id"],"123456789")
            self.assertEqual(path.stat().st_mode&0o777,0o600)
            self.assertIn("W3_EVIDENCE",log.getvalue())
            self.assertNotIn("Bearer",log.getvalue())

    def test_worker_denials_persist_exact_status_diagnostic_ref_and_post_sha(self):
        with tempfile.TemporaryDirectory() as td, \
             patch.dict(os.environ,{"RUNNER_TEMP":td}):
            api,trial=make()
            trial.publisher_seed()
            api.role="worker"
            log=io.StringIO()
            with redirect_stdout(log):
                audit=ledger(Path(td),"worker-negative")
                trial.evidence=audit
                receipt=trial.worker_probe()
                audit.decision("DENIALS_CONFIRMED")
            self.assertEqual(receipt["decision"],"FOUR_REF_RULE_DENIALS_OBSERVED")
            doc=json.loads((Path(td)/"w3-evidence.json").read_text())
            verified=[x for x in doc["events"] if x["stage"]=="VERIFIED"]
            self.assertEqual(len(verified),4)
            self.assertEqual([x["http_status"] for x in verified],[422]*4)
            self.assertTrue(all(x["denial"]=="RULESET_DENIED" for x in verified))
            self.assertEqual(verified[0]["pre_sha"],None)
            self.assertEqual(verified[0]["post_sha"],None)
            self.assertEqual(verified[1]["pre_sha"],PARENT)
            self.assertEqual(verified[1]["post_sha"],PARENT)
            self.assertEqual(verified[2]["target_sha"],GRANDPARENT)
            self.assertTrue(all(
                x["matched_diagnostic"].endswith(x["ref"]) for x in verified))
            self.assertEqual(doc["app_id"],5836223)
            self.assertNotIn("private",log.getvalue().lower())

    def test_unexpected_success_is_durable_partial_not_a_false_denial(self):
        with tempfile.TemporaryDirectory() as td, \
             patch.dict(os.environ,{"RUNNER_TEMP":td}):
            api,trial=make()
            trial.publisher_seed()
            api.role="worker"
            api.failures[("POST","/git/refs")]=Reply(201,{"message":"created"})
            log=io.StringIO()
            with redirect_stdout(log):
                audit=ledger(Path(td),"worker-negative")
                trial.evidence=audit
                with self.assertRaises(StopTrial):
                    trial.worker_probe()
                audit.decision("STOP_INCOMPLETE")
            events=json.loads((Path(td)/"w3-evidence.json").read_text())["events"]
            self.assertEqual(events[0]["stage"],"INTENT")
            self.assertEqual(events[1]["stage"],"RESPONSE")
            self.assertEqual(events[1]["http_status"],201)
            self.assertFalse(any(x["denial"]=="RULESET_DENIED" for x in events))
            self.assertIn('"http_status": 201',log.getvalue())

    def test_unexpected_allowed_worker_create_persists_new_sha_before_stop(self):
        """An unexpectedly permitted create must expose the orphan to recovery."""
        with tempfile.TemporaryDirectory() as td, \
             patch.dict(os.environ,{"RUNNER_TEMP":td}):
            api,trial=make()
            trial.publisher_seed()
            # Simulate a dangerous GitHub permission/ruleset failure: the
            # "worker" token can in fact CREATE, just like publisher.
            api.role="publisher"
            with redirect_stdout(io.StringIO()):
                trial.evidence=ledger(Path(td),"worker-negative")
                api.requests.clear()
                with self.assertRaisesRegex(StopTrial,"unexpected or ambiguous"):
                    trial.worker_probe()
                trial.evidence.decision("STOP_INCOMPLETE")
            receipt=json.loads((Path(td)/"w3-evidence.json").read_text())
            events=receipt["events"]
            self.assertEqual([x["stage"] for x in events],
                             ["INTENT","RESPONSE","READ"])
            self.assertEqual(events[-1]["http_status"],201)
            self.assertEqual(events[-1]["post_sha"],MAIN)
            self.assertEqual(events[-1]["ref"],
                             "refs/heads/"+names(NONCE)["create"])
            self.assertEqual(receipt["decision"],"STOP_INCOMPLETE")
            self.assertNotIn("RULESET_DENIED",json.dumps(receipt))
            self.assertEqual([m for m,_,_ in api.requests if m!="GET"],["POST"])
            self.assertEqual(api.refs[names(NONCE)["create"]],MAIN)

    def test_ambiguous_request_failure_remains_unknown_not_retried(self):
        with tempfile.TemporaryDirectory() as td, \
             patch.dict(os.environ,{"RUNNER_TEMP":td}):
            api,trial=make()
            trial.publisher_seed();api.role="worker"
            real=api.request
            def broken(method,endpoint,data=None):
                if method=="POST": raise OSError("fixture interrupted")
                return real(method,endpoint,data)
            api.request=broken
            with redirect_stdout(io.StringIO()):
                trial.evidence=ledger(Path(td),"worker-negative")
                with self.assertRaises(OSError):
                    trial.worker_probe()
            events=json.loads((Path(td)/"w3-evidence.json").read_text())["events"]
            self.assertEqual([x["stage"] for x in events],["INTENT","STOP"])
            self.assertEqual(events[-1]["reason"],"UNKNOWN_AFTER_REQUEST")
            self.assertIsNone(events[-1]["http_status"])

    def test_transport_failures_are_redacted_at_cli_and_main_boundary(self):
        """Real CLI, error boundary and HTTP parser; no live network or writes."""
        entrypoint=(Path(__file__).resolve().parent/
                    "mhb_atc_w3_ref_trial.py").read_text()
        self.assertEqual(entrypoint.splitlines()[-2:],[
            'if __name__ == "__main__":', '    sys.exit(main())'])
        for failure in ("urlerror", "bad-status-line"):
            with self.subTest(failure=failure), tempfile.TemporaryDirectory() as td:
                marker=("REMOTE_INJECTED_ERROR_SENTINEL" if failure=="urlerror"
                        else "REMOTE_INJECTED_STATUS_SENTINEL")
                requests=[]; protocol_errors=[]

                class OfflineSocket:
                    def makefile(self, mode):
                        return io.BytesIO(marker.encode("ascii")+bytes((13,10,13,10)))

                class OfflineOpener:
                    def open(self, req, timeout=20):
                        requests.append(req.get_method())
                        if failure=="urlerror":
                            raise error.URLError(marker)
                        # Exercise the actual HTTPResponse status-line parser,
                        # not just a fabricated BadStatusLine exception.
                        response=http.client.HTTPResponse(OfflineSocket())
                        try:
                            response.begin()
                        except http.client.BadStatusLine:
                            protocol_errors.append(True)
                            raise
                        raise AssertionError("malformed status line accepted")

                def single_mutation(trial):
                    trial._write_and_record(
                        "publisher-create-seed", "seed",
                        lambda: trial.create("seed", MAIN),
                        target_sha=MAIN)
                    raise AssertionError("a failed mutation must stop the phase")

                stdout=io.StringIO();stderr=io.StringIO()
                with ExitStack() as stack:
                    stack.enter_context(patch.dict(os.environ,{
                        "RUNNER_TEMP":td,
                        "GITHUB_RUN_ID":str(RUN),
                        "W3_APP_TOKEN":"OFFLINE_NOT_A_REAL_APP_TOKEN",
                        "W3_ACTION_APP_SLUG":"phil-atc-publisher",
                        "W3_ACTION_INSTALLATION_ID":"123456789",
                        "W3_ORIGIN_RUN_ID":""}))
                    stack.enter_context(patch.object(
                        module,"policy_check",return_value={}))
                    stack.enter_context(patch.object(
                        module,"local_commits",
                        return_value=(MAIN,PARENT,GRANDPARENT)))
                    stack.enter_context(patch.object(
                        module,"read",
                        return_value={
                            "reviewed_quarantine_tree_sha":TREE,
                            "frozen_target_commits":{
                                "source_sha":MAIN,"parent_sha":PARENT,
                                "grandparent_sha":GRANDPARENT}}))
                    stack.enter_context(patch.object(module,"snapshot_tree"))
                    stack.enter_context(patch.object(module.Trial,"token_audience"))
                    stack.enter_context(patch.object(
                        module.Trial,"publisher_seed",single_mutation))
                    # This test isolates POST transport stderr redaction. The
                    # current-default semantic verifier has separate real
                    # Git/CLI tests, so supply its already-verified result.
                    stack.enter_context(patch.object(
                        module.Trial,"default_quarantine",
                        return_value={"operation":"publisher-create-seed",
                                      "default_sha":MAIN,
                                      "default_workflow_tree_sha":TREE}))
                    stack.enter_context(patch.object(
                        module.Trial,"main",return_value=MAIN))
                    stack.enter_context(patch.object(
                        module.request,"build_opener",
                        return_value=OfflineOpener()))
                    stack.enter_context(patch.object(sys,"argv",[
                        "mhb_atc_w3_ref_trial.py","publisher-seed",
                        "--nonce",NONCE]))
                    stack.enter_context(redirect_stdout(stdout))
                    stack.enter_context(redirect_stderr(stderr))
                    exit_code=module.main()

                self.assertEqual(exit_code,2)
                self.assertEqual(requests,["POST"])
                self.assertEqual(protocol_errors,
                                 [True] if failure=="bad-status-line" else [])
                receipt=json.loads((Path(td)/"w3-evidence.json").read_text())
                self.assertEqual(receipt["decision"],"STOP_INCOMPLETE")
                self.assertEqual([e["stage"] for e in receipt["events"]],
                                 ["INTENT","STOP"])
                self.assertEqual(receipt["events"][-1]["reason"],
                                 "UNKNOWN_AFTER_REQUEST")
                self.assertEqual(receipt["events"][0]["operation"],
                                 "publisher-create-seed")
                for content in (json.dumps(receipt),
                                stdout.getvalue(),stderr.getvalue()):
                    self.assertNotIn(marker,content)
                self.assertIn("W3 STOP: sanitized failure",stderr.getvalue())
                self.assertNotIn("Traceback",stderr.getvalue())

    def test_evidence_default_quarantine_rejects_invalid_sha_and_operation(self):
        with tempfile.TemporaryDirectory() as td,\
             patch.dict(os.environ,{"RUNNER_TEMP":td}):
            with redirect_stdout(io.StringIO()):
                audit=ledger(Path(td),"publisher-seed")
                for item in (("bad","a"*40,"b"*40),
                             ("publisher-delete-canary","invalid","b"*40),
                             ("publisher-delete-canary","a"*40,"invalid")):
                    with self.assertRaises(EvidenceError):
                        audit.default_quarantine_check(
                            operation=item[0],default_sha=item[1],
                            default_workflow_tree_sha=item[2])
                audit.default_quarantine_check(
                    operation="publisher-delete-canary",default_sha=MAIN,
                    default_workflow_tree_sha="d"*40)
            doc=json.loads((Path(td)/"w3-evidence.json").read_text())
            self.assertEqual(len(doc["default_quarantine_checks"]),1)
            self.assertEqual(doc["workflow_tree_sha"],TREE)

    def test_unknown_sha_cleanup_does_not_emit_delete_or_mutate_ref(self):
        with tempfile.TemporaryDirectory() as td,\
             patch.dict(os.environ,{"RUNNER_TEMP":td}):
            api,trial=make()
            api.refs[names(NONCE)["seed"]]="e"*40
            with redirect_stdout(io.StringIO()):
                trial.evidence=ledger(Path(td),"publisher-cleanup")
                with self.assertRaises(StopTrial):
                    trial.publisher_cleanup()
            doc=json.loads((Path(td)/"w3-evidence.json").read_text())
            stop=doc["events"][-1]
            self.assertEqual(stop["stage"],"STOP")
            self.assertEqual(stop["pre_sha"],"e"*40)
            self.assertTrue(all(m=="GET" for m,_,_ in api.requests))

    def test_evidence_never_serializes_untrusted_remote_text_or_tokens(self):
        with tempfile.TemporaryDirectory() as td,\
             patch.dict(os.environ,{"RUNNER_TEMP":td}):
            with redirect_stdout(io.StringIO()):
                audit=ledger(Path(td),"worker-negative")
                for invalid in ({"operation":"any","stage":"INTENT"},
                                {"operation":"worker-create","stage":"RESPONSE",
                                 "http_status":"422"},
                                {"operation":"worker-create","stage":"RESPONSE",
                                 "matched_diagnostic":"SECRET ghp_12345",
                                 "ref":"refs/heads/"+names(NONCE)["create"]}):
                    with self.assertRaises(EvidenceError):
                        audit.event(**invalid)
                audit.event("worker-create","INTENT",
                            ref="refs/heads/"+names(NONCE)["create"],
                            target_sha=MAIN)
            self.assertNotIn("ghp_", (Path(td)/"w3-evidence.json").read_text())

    def test_evidence_requires_owned_nonce_and_authenticated_principal(self):
        with tempfile.TemporaryDirectory() as td,\
             patch.dict(os.environ,{"RUNNER_TEMP":td}):
            with self.assertRaises(EvidenceError):
                EvidenceLedger(Path(td)/"outside.json",phase="worker-negative",
                    nonce=NONCE,run_id=RUN,source_sha=MAIN,parent_sha=PARENT,
                    grandparent_sha=GRANDPARENT,workflow_tree_sha=TREE,
                    app_id=5836223,installation_id="123")
            with self.assertRaises(EvidenceError):
                ledger(Path(td),"invalid-phase")

    def test_durable_workflow_uploads_even_after_steps_fail(self):
        wf=(Path(__file__).resolve().parents[1]/
            ".github/workflows/mhb-atc-w3-ref-commissioning.yml").read_text()
        self.assertEqual(wf.count("w3-evidence.json"),3)
        self.assertEqual(wf.count("if: always()"),3)
        self.assertEqual(wf.count("actions/upload-artifact@v4"),4)
        self.assertNotIn("permission-pull-requests: write",wf)
        self.assertNotIn("\n  push:",wf)

if __name__=="__main__":
    unittest.main()
