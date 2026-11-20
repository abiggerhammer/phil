#!/usr/bin/env python3
"""Fake-transport W3 durable sanitized intent/denial/cleanup receipts."""
from __future__ import annotations
from contextlib import redirect_stdout
import io
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

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
        workflow_tree_sha=TREE,
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
