#!/usr/bin/env python3
"""Offline classifier controls; no network or GitHub ref writes."""
import argparse
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
import probe

REF = "refs/heads/hamster/admitted/w3-a1b2c3d4e5f6-canary"
REPO = "owner/w3-delete-selector-probe-example"

def witness(run_id, kind, *, created=False, deleted=False, ref=REF):
    return {"id":run_id, "event":"push",
            "path":".github/workflows/w3-"+probe.VARIANTS[kind]+".yml",
            "created_at":"2026-11-21T11:12:00Z",
            "head_sha":"a"*40,"head_branch":"main","actor":"owner",
            "status":"completed","conclusion":"success",
            "witness":{"schema":"PHIL-W3-SELECTOR-WITNESS-V1",
                       "variant":kind,"source_marker":"DEFAULT_V1",
                       "event_name":"push","event_ref":ref,
                       "event_created":created,"event_deleted":deleted,
                       "github_ref":"refs/heads/main","github_sha":"a"*40,
                       "run_id":str(run_id),"actor":"owner",
                       "workflow_ref":"owner/test/.github/workflows/example.yml@refs/heads/main"}}

def snapshot(runs, observed):
    return {"schema":"W3-SELECTOR-CENSUS-V1",
            "repository":REPO,"repository_id":1234,
            "ref":REF,"nonce":"a1b2c3d4e5f6",
            "window_start":"2026-11-21T11:00:00Z",
            "window_end":"2026-11-21T11:30:00Z",
            "observed_at":observed,"runs":runs,
            "decision":"READ_ONLY_NOT_CERTIFIED"}

class OfflineTests(unittest.TestCase):
    def classify(self, phase, runs, after_time="2026-11-21T12:05:00Z"):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/"before.json";q=Path(d)/"after.json"
            p.write_text(json.dumps(snapshot([],"2026-11-21T11:05:00Z")))
            q.write_text(json.dumps(snapshot(runs,after_time)))
            buf=io.StringIO()
            with contextlib.redirect_stdout(buf):
                probe.classify(argparse.Namespace(phase=phase,before=p,after=q))
            return json.loads(buf.getvalue())["decision"]

    def test_production_target_denied(self):
        for repo in ("abiggerhammer/phil","owner/production","wrong-format"):
            with self.assertRaises(probe.Stop):
                probe.verify_repo_name(repo)

    def test_spent_nonce_denied(self):
        with self.assertRaises(probe.Stop):
            probe.ref_for("d948536ad68f")

    def test_deletion_genuine_controls(self):
        self.assertEqual(self.classify("delete", [
            witness(1,"UNFILTERED",deleted=True),
            witness(2,"W3_ONLY",deleted=True)]),
            "SUPPORTS_MODEL_BOUNDED_NOT_CERTIFIED")

    def test_default_substitution_is_counterexample(self):
        self.assertEqual(self.classify("delete", [
            witness(1,"UNFILTERED",deleted=True),
            witness(2,"W3_ONLY",deleted=True),
            witness(3,"MAIN_ONLY",deleted=True)]),
            "COUNTEREXAMPLE_STOP")

    def test_ignore_pair_violation_is_counterexample(self):
        self.assertEqual(self.classify("delete", [
            witness(1,"UNFILTERED",deleted=True),
            witness(2,"W3_ONLY",deleted=True),
            witness(3,"IGNORE_PAIR",deleted=True)]),
            "COUNTEREXAMPLE_STOP")

    def test_delayed_create_cannot_count_as_delete(self):
        self.assertTrue(self.classify("delete", [
            witness(1,"UNFILTERED",deleted=True),
            witness(2,"W3_ONLY",created=True)]).startswith("INCONCLUSIVE"))

    def test_string_false_not_boolean(self):
        x=witness(2,"W3_ONLY",deleted=True)
        x["witness"]["event_deleted"]="false"
        self.assertTrue(self.classify("delete", [
            witness(1,"UNFILTERED",deleted=True),x]).startswith("INCONCLUSIVE"))

    def test_main_control(self):
        self.assertEqual(self.classify("main",[
            witness(1,"UNFILTERED",ref="refs/heads/main"),
            witness(2,"MAIN_ONLY",ref="refs/heads/main"),
            witness(3,"IGNORE_PAIR",ref="refs/heads/main")]),
            "SUPPORTS_MODEL_BOUNDED_NOT_CERTIFIED")

    def test_create_control(self):
        self.assertEqual(self.classify("create",[
            witness(1,"UNFILTERED",created=True),
            witness(2,"W3_ONLY",created=True)]),
            "SUPPORTS_MODEL_BOUNDED_NOT_CERTIFIED")

    def test_early_after_is_stop(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/"before.json";q=Path(d)/"after.json"
            p.write_text(json.dumps(snapshot([],"2026-11-21T11:05:00Z")))
            q.write_text(json.dumps(snapshot([],"2026-11-21T11:31:00Z")))
            with self.assertRaises(probe.Stop):
                probe.classify(argparse.Namespace(phase="delete",before=p,after=q))

if __name__=="__main__":
    unittest.main()
