#!/usr/bin/env python3
"""Offline origin-artifact, authenticated original-run and historical tree tests."""
from __future__ import annotations
import copy
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch
import mhb_atc_w3_ref_trial as trial_source
from mhb_atc_w3_ref_trial import Reply, StopTrial
from mhb_atc_w3_provenance import (
    REPO, WORKFLOW_PATH, ProvenanceError, make_binding, validate_binding,
    read_binding, verify_origin, snapshot_tree)

NONCE="f1e2d3c4b5a6"; H="a"*40; P="b"*40; G="c"*40; TREE="d"*40; RUN=987654321
DISPATCH="f"*40
FROZEN={"source_sha":H,"parent_sha":P,"grandparent_sha":G}

def origin():
    return make_binding(NONCE,DISPATCH,H,P,G,TREE,RUN)

class GitHub:
    def __init__(self):
        self.records={
            "/actions/runs/"+str(RUN): {
                "id":RUN,"event":"workflow_dispatch","path":WORKFLOW_PATH,
                "head_branch":"main","head_sha":DISPATCH,"run_attempt":1,
                "actor":{"login":"abiggerhammer"},
                "triggering_actor":{"login":"abiggerhammer"},
                "repository":{"full_name":REPO}},
            "/git/commits/"+H:{"sha":H,"tree":{"sha":"1"*40},"parents":[{"sha":P}]},
            "/git/commits/"+P:{"sha":P,"tree":{"sha":"2"*40},"parents":[{"sha":G}]},
            "/git/commits/"+G:{"sha":G,"tree":{"sha":"3"*40},"parents":[{"sha":"e"*40}]},
            "/git/trees/"+"1"*40:{"sha":"1"*40,"truncated":False,
                "tree":[{"path":".github","type":"tree","sha":"4"*40}]},
            "/git/trees/"+"2"*40:{"sha":"2"*40,"truncated":False,
                "tree":[{"path":".github","type":"tree","sha":"4"*40}]},
            "/git/trees/"+"3"*40:{"sha":"3"*40,"truncated":False,
                "tree":[{"path":".github","type":"tree","sha":"4"*40}]},
            "/git/trees/"+"4"*40:{"sha":"4"*40,"truncated":False,
                "tree":[{"path":"workflows","type":"tree","sha":TREE}]}}
        self.calls=[]
    def request(self,method,path,data=None):
        self.calls.append((method,path))
        if method!="GET": raise AssertionError("origin tried a write")
        if path not in self.records: return Reply(404,{"message":"Not Found"})
        return Reply(200,copy.deepcopy(self.records[path]))

class ProvenanceTests(unittest.TestCase):
    def test_binding_canonical_and_nonsecret(self):
        doc=origin()
        self.assertEqual(validate_binding(doc,nonce=NONCE,
            original_run_id=RUN,reviewed_tree=TREE,
            frozen_targets=FROZEN),doc)
        self.assertEqual(doc["parent_sha"],P)
        self.assertEqual(doc["dispatch_sha"],DISPATCH)
        self.assertNotEqual(doc["dispatch_sha"],doc["source_sha"])
        self.assertEqual(doc["schema"],"MHB-ATC-W3-ORIGIN-V2")
        for word in ("token","private_key","jwt","secret"):
            self.assertNotIn(word,json.dumps(doc).lower())

    def test_binding_rejects_wrong_nonce_run_lineage_tree_and_shape(self):
        for field,value in (("nonce","e"*12),("run_id",RUN+1),
                            ("source_sha","invalid-sha"),("dispatch_sha","invalid-sha"),
                            ("workflow_tree_sha","f"*40),
                            ("run_attempt",2),("run_attempt",True),
                            ("repository","attacker/phil"),("mode","cleanup"),
                            ("added","injection")):
            doc=origin();doc[field]=value
            with self.subTest(field=field),self.assertRaises(ProvenanceError):
                validate_binding(doc,nonce=NONCE,original_run_id=RUN,
                    reviewed_tree=TREE,frozen_targets=FROZEN)

    def test_binding_rejects_foreign_valid_frozen_tuple(self):
        altered=origin()
        altered["source_sha"]="e"*40
        with self.assertRaisesRegex(ProvenanceError,"frozen targets"):
            validate_binding(altered,nonce=NONCE,original_run_id=RUN,
                             reviewed_tree=TREE,frozen_targets=FROZEN)
        with self.assertRaisesRegex(ProvenanceError,"frozen targets"):
            validate_binding(origin(),nonce=NONCE,original_run_id=RUN,
                reviewed_tree=TREE,
                frozen_targets={"source_sha":"e"*40,"parent_sha":P,
                                "grandparent_sha":G})

    def test_loader_rejects_duplicates_oversize_and_symlinks(self):
        with tempfile.TemporaryDirectory() as d:
            file=Path(d)/"w3-origin.json";file.write_text(json.dumps(origin()))
            self.assertEqual(read_binding(file,nonce=NONCE,
                original_run_id=RUN,reviewed_tree=TREE,
                frozen_targets=FROZEN),origin())
            link=Path(d)/"symlink.json";link.symlink_to(file)
            with self.assertRaises(ProvenanceError):
                read_binding(link,nonce=NONCE,original_run_id=RUN,
                             reviewed_tree=TREE,frozen_targets=FROZEN)
            for malformed in ('{"schema":"x","schema":"y"}',"x"*4097):
                file.write_text(malformed)
                with self.assertRaises(ProvenanceError):
                    read_binding(file,nonce=NONCE,original_run_id=RUN,
                                 reviewed_tree=TREE,frozen_targets=FROZEN)

    def test_authenticated_run_and_entire_commit_graph(self):
        gh=GitHub()
        self.assertEqual(verify_origin(gh,origin()),origin())
        self.assertEqual(len(gh.calls),10)
        self.assertTrue(all(x[0]=="GET" for x in gh.calls))
        self.assertIn(("GET","/git/commits/"+G),gh.calls)

    def test_original_run_identity_and_all_three_trees_fail_closed(self):
        cases=[
            ("/actions/runs/"+str(RUN),lambda x:x["actor"].update(login="other")),
            ("/actions/runs/"+str(RUN),lambda x:x.update(run_attempt=2)),
            ("/actions/runs/"+str(RUN),lambda x:x.update(path="other.yml")),
            ("/actions/runs/"+str(RUN),lambda x:x.update(event="schedule")),
            ("/actions/runs/"+str(RUN),lambda x:x.update(head_sha="e"*40)),
            ("/git/commits/"+H,lambda x:x["parents"][0].update(sha="f"*40)),
            ("/git/commits/"+P,lambda x:x["tree"].update(sha="f"*40)),
            ("/git/commits/"+G,lambda x:x["tree"].update(sha="f"*40)),
            ("/git/trees/"+"4"*40,
             lambda x:x["tree"][0].update(sha="f"*40)),
            ("/git/trees/"+"4"*40,
             lambda x:x.update(truncated=True))]
        for path,change in cases:
            gh=GitHub();change(gh.records[path])
            with self.subTest(path=path),self.assertRaises(ProvenanceError):
                verify_origin(gh,origin())

    def test_all_selectable_target_workflow_trees_equal_pinned_digest(self):
        def git(repo,*args):
            p=subprocess.run(["git",*args],cwd=repo,text=True,
                capture_output=True,timeout=20)
            self.assertEqual(p.returncode,0,p.stderr)
            return p.stdout.strip()
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);git(root,"init","-b","main")
            git(root,"config","user.name","fixture")
            git(root,"config","user.email","fixture@example.invalid")
            path=root/".github"/"workflows";path.mkdir(parents=True)
            (path/"x.yml").write_text("on:\n  push:\n    branches: [main]\n")
            commits=[]
            for i in range(3):
                (root/"code").write_text(str(i))
                git(root,"add","-A");git(root,"commit","-m",f"source-{i}")
                commits.append(git(root,"rev-parse","HEAD"))
            tree=git(root,"rev-parse","HEAD:.github/workflows")
            self.assertEqual(snapshot_tree(root,*commits[::-1],tree),tree)
            (path/"x.yml").write_text("on:\n  push:\n    branches-ignore: ['hamster/staged/**']\n")
            git(root,"add","-A");git(root,"commit","-m","workflow-change")
            new=git(root,"rev-parse","HEAD")
            with self.assertRaisesRegex(ProvenanceError,"workflow tree differs"):
                snapshot_tree(root,new,commits[2],commits[1],
                    git(root,"rev-parse","HEAD:.github/workflows"))

    def test_frozen_targets_survive_unrelated_new_main_workflow_changes(self):
        def git(repo,*args):
            run=subprocess.run(["git",*args],cwd=repo,
                               text=True,capture_output=True,timeout=20)
            self.assertEqual(run.returncode,0,run.stderr)
            return run.stdout.strip()
        with tempfile.TemporaryDirectory() as d:
            root=Path(d)
            git(root,"init","-b","main")
            git(root,"config","user.name","fixture")
            git(root,"config","user.email","fixture@example.invalid")
            flows=root/".github"/"workflows"
            flows.mkdir(parents=True)
            (flows/"safe.yml").write_text(
                "on:\\n  push:\\n    branches: [main]\\n")
            targets=[]
            for i in range(3):
                (root/"code").write_text(f"trusted-{i}")
                git(root,"add","-A")
                git(root,"commit","-m",f"trusted {i}")
                targets.append(git(root,"rev-parse","HEAD"))
            selected=targets[::-1]
            reviewed=git(root,"rev-parse","HEAD:.github/workflows")
            self.assertEqual(snapshot_tree(root,*selected,reviewed),reviewed)
            # Active main can have later, different workflow definitions;
            # existing frozen targets still select their own reviewed tree.
            (flows/"new.yml").write_text(
                "on:\\n  push:\\n    branches: [feature/other]\\n")
            git(root,"add","-A")
            git(root,"commit","-m","unrelated new main workflow")
            self.assertNotEqual(git(root,"rev-parse","HEAD:.github/workflows"),
                                reviewed)
            self.assertEqual(snapshot_tree(root,*selected,reviewed),reviewed)
            (root/"code").write_text("later non-workflow work")
            git(root,"add","-A")
            git(root,"commit","-m","main moves again")
            self.assertEqual(snapshot_tree(root,*selected,reviewed),reviewed)
            with self.assertRaisesRegex(ProvenanceError,"first-parent"):
                snapshot_tree(root,selected[0],selected[2],selected[1],
                              reviewed)
            # A valid-looking but unmerged side-branch trio is NOT a
            # trusted main ancestor, regardless of workflow-tree equality.
            git(root,"switch","-c","side",selected[0])
            (root/"code").write_text("unmerged")
            git(root,"add","-A")
            git(root,"commit","-m","unmerged side commit")
            outside=git(root,"rev-parse","HEAD")
            git(root,"switch","main")
            with self.assertRaisesRegex(ProvenanceError,"ancestry/tree"):
                snapshot_tree(root,outside,selected[0],selected[1],reviewed)

    def test_recovery_after_main_moves_twice_uses_original_seed_parent(self):
        # H's seed was P. A fresh K's latest ancestors no longer contain P.
        with tempfile.TemporaryDirectory() as d:
            file=Path(d)/"w3-origin.json";file.write_text(json.dumps(origin()))
            gh=GitHub()
            policy={"reviewed_quarantine_tree_sha":TREE}
            old_read=trial_source.read
            with patch.dict(os.environ,{
                    "W3_ORIGIN_RUN_ID":str(RUN),
                    "W3_ORIGIN_BINDING_FILE":str(file),
                    "GITHUB_TOKEN":"fixture-read-only-key",
                    "GITHUB_RUN_ID":str(RUN+100)},clear=True),\
                 patch.object(trial_source,"read",side_effect=lambda p:
                     policy if p==".github/atc-w3-ref-trial.json" else old_read(p)),\
                 patch.object(trial_source,"Client",side_effect=lambda _:gh):
                observed=trial_source._verified_recovery_origin(NONCE,TREE,
                                                                  (H,P,G))
                self.assertEqual(observed["parent_sha"],P)
                self.assertEqual(observed["dispatch_sha"],DISPATCH)
                self.assertNotIn(P,("f"*40,"e"*40,H))
                self.assertTrue(all(m=="GET" for m,_ in gh.calls))

    def test_recovered_original_seed_is_cleaned_after_two_new_main_commits(self):
        """A completely new cleanup Trial must retain original P, not K/J/H."""
        from test_mhb_atc_w3_ref_trial import FakeAPI
        from mhb_atc_w3_ref_trial import Trial
        fake=FakeAPI("publisher",nonce=NONCE)
        fake.main="f"*40  # Simulate newer main K. Its parents J/H exclude P.
        seed="hamster/admitted/w3-"+NONCE+"-seed"
        fake.refs[seed]=P
        policy=fake.policy
        verified=verify_origin(GitHub(),origin())
        recovered=Trial(fake,NONCE,verified["source_sha"],
                        verified["parent_sha"],verified["grandparent_sha"],
                        policy)
        preflight=recovered.publisher_recovery_plan()
        self.assertEqual(preflight["refs"]["seed"],"KNOWN_DISPOSABLE")
        result=recovered.publisher_cleanup()
        self.assertEqual(result["decision"],"OWNED_DISPOSABLE_REFS_ABSENT")
        self.assertEqual(fake.refs,{})
        writes=[method for method,_,_ in fake.requests if method!="GET"]
        self.assertEqual(writes,["DELETE"])
        self.assertNotIn(P,("f"*40,"e"*40,H))

    def test_wrong_new_run_ancestry_would_refuse_original_seed(self):
        from test_mhb_atc_w3_ref_trial import FakeAPI
        from mhb_atc_w3_ref_trial import Trial
        fake=FakeAPI("publisher",nonce=NONCE)
        seed="hamster/admitted/w3-"+NONCE+"-seed"
        fake.refs[seed]=P
        fake.main="f"*40
        # The NEW run sees K, J and H: P was lost from its three-sha set.
        wrong=Trial(fake,NONCE,"f"*40,"e"*40,H,fake.policy)
        with self.assertRaisesRegex(StopTrial,"UNKNOWN SHA"):
            wrong.publisher_recovery_plan()
        self.assertEqual(fake.refs[seed],P)
        self.assertEqual([m for m,_,_ in fake.requests if m!="GET"],[])

    def test_origin_file_created_only_once_in_runner_temp(self):
        with tempfile.TemporaryDirectory() as d,\
             patch.dict(os.environ,{"RUNNER_TEMP":d}):
            path=trial_source._write_origin_artifact(origin())
            self.assertEqual(json.loads(path.read_text()),origin())
            self.assertEqual(path.stat().st_mode&0o777,0o600)
            with self.assertRaises(StopTrial):
                trial_source._write_origin_artifact(origin())

    def test_origin_upload_before_publisher_and_cleanup_download(self):
        wf=(Path(__file__).resolve().parents[1]/
            ".github/workflows/mhb-atc-w3-ref-commissioning.yml").read_text()
        self.assertIn("actions: read",wf)
        self.assertLess(wf.index("prepare-origin"),
                        wf.index("Upload verified nonsecret original lineage"))
        self.assertLess(wf.index("Upload verified nonsecret original lineage"),
                        wf.index("  publisher_seed:"))
        self.assertEqual(wf.count("actions/download-artifact@v4"),2)
        self.assertIn("run-id: "+"$"+"{{ inputs.original_run_id }}",wf)

if __name__=="__main__":
    unittest.main()
