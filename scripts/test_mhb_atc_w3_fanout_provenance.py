#!/usr/bin/env python3
"""W3 fanout origin, historical source activation and cleanup provenance tests."""
from __future__ import annotations

import copy
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from mhb_atc_w3_ref_trial import Reply
from mhb_atc_w3_fanout_provenance import (
    REPO, WORKFLOW, POLICY_PATH, TARGET, TREE,
    FanoutStop, current_policy, policy_check, nonce_ref, make_binding,
    valid_binding, read_binding, write_binding, verify_original,
    policy_blob, git, trusted_checkout, json_doc,
)

ROOT=Path(__file__).resolve().parents[1]
NONCE="f1e2d3c4b5a6"
RUN=123456789
MAIN="a"*40
BLOB="b"*40


class FakeActions:
    def __init__(self, head):
        self.doc={
            "id":RUN, "event":"workflow_dispatch", "path":WORKFLOW,
            "head_branch":"main", "head_sha":head,
            "run_attempt":1,
            "actor":{"login":"abiggerhammer"},
            "triggering_actor":{"login":"abiggerhammer"},
            "repository":{"full_name":REPO},
        }
        self.calls=[]

    def request(self,method,route,data=None):
        self.calls.append((method,route))
        if method!="GET" or route!="/actions/runs/"+str(RUN):
            raise AssertionError("origin verifier must perform fixed GET only")
        return Reply(200,copy.deepcopy(self.doc))


def initialized_repo(root):
    def cmd(*args):
        result=subprocess.run(["git",*args],cwd=root,capture_output=True,
                              text=True,timeout=25)
        if result.returncode!=0:
            raise AssertionError(result.stderr)
        return result.stdout.strip()
    cmd("init","-b","main")
    cmd("config","user.name","fanout fixture")
    cmd("config","user.email","fanout@example.invalid")
    path=root/POLICY_PATH
    path.parent.mkdir(parents=True)
    # Always construct an explicit OFF-after-original fixture, even when
    # the source checkout itself is an active activation candidate.
    original=dict(current_policy(ROOT),source_authorized=False,
                  approved_nonce=None)
    active=dict(original,source_authorized=True,approved_nonce=NONCE)
    policy_check(active,nonce=NONCE,require_active=True)
    path.write_text(json.dumps(active))
    cmd("add","-A");cmd("commit","-m","original approved fanout")
    origin=cmd("rev-parse","HEAD")
    orig_blob=policy_blob(root,origin)
    path.write_text(json.dumps(original))
    cmd("add","-A");cmd("commit","-m","later disabled policy")
    return origin,orig_blob


class FanoutProvenanceTests(unittest.TestCase):
    def test_original_run_binding_exact_canonical_and_nonsecret(self):
        original=make_binding(NONCE,MAIN,RUN,BLOB)
        self.assertEqual(valid_binding(original,nonce=NONCE,
                                       expected_run_id=RUN),original)
        self.assertEqual(original["target_sha"],TARGET)
        self.assertEqual(original["workflow_tree_sha"],TREE)
        self.assertEqual(original["run_attempt"],1)
        self.assertEqual(original["mode"],"run")
        self.assertNotIn("token",str(original).lower())
        for key,value in (
            ("nonce","0"*12),("run_id",RUN+1),
            ("target_sha","f"*40),("dispatch_sha","wrong"),
            ("policy_blob_sha","invalid"),("workflow_tree_sha","f"*40),
            ("repository","foreign/repo"),("run_attempt",2),
            ("run_attempt",True),("mode","cleanup"),
            ("added","untrusted")):
            copy_doc=dict(original);copy_doc[key]=value
            with self.subTest(key=key),self.assertRaises(FanoutStop):
                valid_binding(copy_doc,nonce=NONCE,expected_run_id=RUN)

    def test_binding_file_fsync_0600_and_reject_occupied_or_bogus(self):
        with tempfile.TemporaryDirectory() as td,\
             patch.dict(os.environ,{"RUNNER_TEMP":td}):
            doc=make_binding(NONCE,MAIN,RUN,BLOB)
            path=write_binding(Path(td),doc)
            self.assertEqual(path.name,"w3-fanout-origin.json")
            self.assertEqual(path.stat().st_mode & 0o777,0o600)
            self.assertEqual(read_binding(path,nonce=NONCE,
                                          expected_run_id=RUN),doc)
            with self.assertRaises(FanoutStop):
                write_binding(Path(td),doc)
            link=Path(td)/"different.json"
            link.symlink_to(path)
            with self.assertRaises(FanoutStop):
                read_binding(link,nonce=NONCE,expected_run_id=RUN)
            path.write_text('{"run_id":1,"run_id":2}')
            with self.assertRaises(FanoutStop):
                read_binding(path,nonce=NONCE,expected_run_id=RUN)
            path.write_bytes(b"!"*5000)
            with self.assertRaises(FanoutStop):
                read_binding(path,nonce=NONCE,expected_run_id=RUN)

    def test_historical_original_active_source_survives_later_off_switch(self):
        with tempfile.TemporaryDirectory() as td:
            root=Path(td);original,blob=initialized_repo(root)
            doc=make_binding(NONCE,original,RUN,blob)
            with patch.dict(os.environ,{"GITHUB_SHA":git(root,"rev-parse","HEAD")}):
                self.assertEqual(trusted_checkout(root),git(root,"rev-parse","HEAD"))
            fake=FakeActions(original)
            current=dict(current_policy(ROOT),source_authorized=False,
                         approved_nonce=None)
            self.assertFalse(current["source_authorized"])
            self.assertEqual(verify_original(fake,root,doc,current),doc)
            self.assertEqual(fake.calls,[("GET","/actions/runs/"+str(RUN))])
            with self.assertRaisesRegex(FanoutStop,"activation/nonce"):
                verify_original(fake,root,doc,current,
                                require_current_activation=True)

    def test_authenticated_run_identity_and_original_policy_are_strict(self):
        with tempfile.TemporaryDirectory() as td:
            root=Path(td);origin,blob=initialized_repo(root)
            doc=make_binding(NONCE,origin,RUN,blob)
            current=current_policy(ROOT)
            for name,value in (
                ("event","schedule"),("path","other.yml"),
                ("head_sha","e"*40),("head_branch","other"),
                ("run_attempt",2),("run_attempt",True),
                ("actor",{"login":"attacker"}),
                ("triggering_actor",{"login":"attacker"}),
                ("repository",{"full_name":"other/repo"})):
                fake=FakeActions(origin);fake.doc[name]=value
                with self.subTest(field=name),self.assertRaises(FanoutStop):
                    verify_original(fake,root,doc,current)
            fake=FakeActions(origin)
            wrong=dict(doc,policy_blob_sha="c"*40)
            with self.assertRaisesRegex(FanoutStop,"Git blob differs"):
                verify_original(fake,root,wrong,current)
            wrong=dict(doc,dispatch_sha="f"*40)
            with self.assertRaises(FanoutStop):
                verify_original(fake,root,wrong,current)

    def test_original_source_disabled_cannot_authorize_recovery(self):
        with tempfile.TemporaryDirectory() as td:
            root=Path(td);origin,_blob=initialized_repo(root)
            # The later HEAD policy is source-disabled. An impostor
            # "original" run bound to that SHA must NOT authorize cleanup.
            disabled=git(root,"rev-parse","HEAD")
            doc=make_binding(NONCE,disabled,RUN,policy_blob(root,disabled))
            fake=FakeActions(disabled)
            with self.assertRaisesRegex(FanoutStop,"activation/nonce"):
                verify_original(fake,root,doc,
                                dict(current_policy(ROOT),
                                     source_authorized=False,
                                     approved_nonce=None))


if __name__=="__main__":
    unittest.main()
