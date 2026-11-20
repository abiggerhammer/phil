#!/usr/bin/env python3
"""Offline hostile tests for read-only W3 fanout event observation."""
import copy
from pathlib import Path
import tempfile
import unittest
from urllib.parse import urlsplit, parse_qs

import mhb_atc_w3_fanout_observer as mod
from mhb_atc_w3_ref_trial import Reply

START="2026-11-20T15:00:00Z"
END="2026-11-20T15:20:00Z"
NONCE="d1e2f3a4b5c6"
TARGET="e38814a2e916252a8a7f3dd438943e8f4a21664a"
BOT="phil-atc-publisher[bot]"


def run(i,event="push",branch="main",sha="a"*40,actor="ordinary-user"):
    return {"id":i,"event":event,"head_branch":branch,"head_sha":sha,
            "created_at":"2026-11-20T15:05:00Z",
            "actor":{"login":actor},"repository":{"full_name":mod.REPO},
            "path":".github/workflows/safe.yml",
            "status":"completed","conclusion":"success"}


class Fake:
    def __init__(self,records=None,total_override=None):
        self.records=records or {}
        self.total_override=total_override
        self.calls=[]

    def request(self,method,endpoint,data=None):
        self.calls.append((method,endpoint))
        if method!="GET":
            raise AssertionError("observer attempted mutation")
        parsed=urlsplit(endpoint)
        query=parse_qs(parsed.query)
        if parsed.path!="/actions/runs" or set(query)!={
                "event","created","per_page","page"}:
            raise AssertionError("unexpected GET route")
        if query["created"] != [START+".."+END] or query["per_page"] != ["4"]:
            raise AssertionError("unapproved observation window")
        event=query["event"][0];page=int(query["page"][0])
        if event not in mod.EVENTS:raise AssertionError("unknown event")
        records=self.records.get(event,[])
        total=len(records) if self.total_override is None else self.total_override
        return Reply(200,{"total_count":total,"workflow_runs":copy.deepcopy(
            records[(page-1)*mod.PAGE_SIZE:page*mod.PAGE_SIZE])})


def capture(fake,role="before",observed="2026-11-20T15:02:00Z"):
    return mod.collect(fake,role=role,nonce=NONCE,
        window_start=START,window_end=END,observed_at=observed)


class FanoutObserverTests(unittest.TestCase):
    def test_policy_disabled_and_exact_canary_shape(self):
        p=mod.reviewed_policy()
        self.assertIs(p["source_authorized"],False)
        self.assertIsNone(p["approved_nonce"])
        self.assertEqual(p["publisher_app_id"],5782193)
        self.assertEqual(p["frozen_target_sha"],TARGET)
        self.assertEqual(p["max_authorized_ref_mutations"],2)
        self.assertEqual(mod.nonce_ref(NONCE),
            "refs/heads/hamster/admitted/w3-fanout-"+NONCE+"-canary")
        for bad in ("../main","D"*12,"a"*11,"a"*13):
            with self.subTest(bad=bad),self.assertRaises(mod.CensusStop):
                mod.nonce_ref(bad)

    def test_zero_new_runs_never_claims_quarantine_verified(self):
        fake=Fake()
        pre=capture(fake)
        post=capture(fake,"after","2026-11-20T15:40:00Z")
        result=mod.compare(pre,post,target_sha=TARGET,publisher_actor=BOT)
        self.assertEqual(result["decision"],"NO_CANDIDATE_RUNS_REVIEW_REQUIRED")
        self.assertFalse(result["quarantine_certified"])
        self.assertFalse(result["execution_authorized"])
        self.assertEqual(result["new_total"],0)
        self.assertEqual(len(fake.calls),6)
        self.assertTrue(all(method=="GET" for method,_ in fake.calls))

    def test_before_window_end_is_incomplete_even_when_empty(self):
        result=mod.compare(capture(Fake()),
            capture(Fake(),"after","2026-11-20T15:30:00Z"),
            target_sha=TARGET,publisher_actor=BOT)
        self.assertEqual(result["decision"],"INCOMPLETE_OBSERVATION_RECHECK")
        self.assertFalse(result["quarantine_certified"])

    def test_app_push_create_delete_are_flagged(self):
        ref=mod.nonce_ref(NONCE).removeprefix("refs/heads/")
        runs={
            "push":[run(777,branch=ref,sha=TARGET),
                    run(778,actor=BOT,branch="main",sha="b"*40)],
            "delete":[run(779,event="delete",actor=BOT,sha="b"*40)],
            "create":[run(780,event="create",actor=BOT,branch=ref,sha=TARGET)]}
        post=capture(Fake(runs),"after","2026-11-20T15:40:00Z")
        result=mod.compare(capture(Fake()),post,
                           target_sha=TARGET,publisher_actor=BOT)
        self.assertEqual(result["potential_fanout_run_ids"],
                         [777,778,779,780])
        self.assertEqual(result["decision"],"POTENTIAL_FANOUT_STOP_REVIEW")

    def test_unrelated_main_traffic_is_not_attributed(self):
        post=capture(Fake({"push":[run(800),run(801,branch="formal-semantics/x",
                                         actor="fsem-hamster")]}),
                     "after","2026-11-20T15:40:00Z")
        result=mod.compare(capture(Fake()),post,
                           target_sha=TARGET,publisher_actor=BOT)
        self.assertEqual(result["new_total"],2)
        self.assertEqual(result["potential_fanout_run_ids"],[])
        self.assertEqual(result["other_new_run_count"],2)

    def test_multi_page_complete_census(self):
        r=capture(Fake({"push":[run(1000+i) for i in range(124)]}))
        self.assertEqual(r["event_totals"]["push"],124)
        self.assertEqual(len(r["runs"]),124)

    def test_incomplete_oversized_or_duplicate_pagination_rejected(self):
        for total in (199,200,201):
            with self.subTest(total=total),self.assertRaises(mod.CensusStop):
                capture(Fake({"push":[run(1)]},total_override=total))
        with self.assertRaisesRegex(mod.CensusStop,"duplicate"):
            capture(Fake({"push":[run(1),run(1)]}))

    def test_foreign_events_and_malformed_utc_fail_closed(self):
        edits=[
            lambda x:x["repository"].update(full_name="foreign/repo"),
            lambda x:x.update(event="workflow_dispatch"),
            lambda x:x.update(created_at="2026-11-21T15:05:00Z"),
            lambda x:x.update(head_sha="invalid"),
            lambda x:x.update(actor={"login":""})]
        for edit in edits:
            x=run(7);edit(x)
            with self.subTest(x=x),self.assertRaises(mod.CensusStop):
                capture(Fake({"push":[x]}))
        for window_end in ("2026-11-20T15:00:00Z",
                           "2026-11-20T18:30:00Z",
                           "2026-11-20 15:20:00Z"):
            with self.subTest(end=window_end),self.assertRaises(mod.CensusStop):
                mod.collect(Fake(),role="before",nonce=NONCE,
                            window_start=START,window_end=window_end,
                            observed_at="2026-11-20T15:02:00Z")

    def test_census_run_disappearing_or_window_mismatch_stops(self):
        before=capture(Fake({"push":[run(111)]}))
        after=capture(Fake(),"after","2026-11-20T15:40:00Z")
        with self.assertRaises(mod.CensusStop):
            mod.compare(before,after,target_sha=TARGET,publisher_actor=BOT)
        after=capture(Fake({"push":[run(111)]}),"after",
                      "2026-11-20T15:40:00Z")
        after["window_end"]="2026-11-20T15:22:00Z"
        with self.assertRaises(mod.CensusStop):
            mod.compare(before,after,target_sha=TARGET,publisher_actor=BOT)

    def test_atomic_snapshot_no_overwrite_or_duplicate_keys(self):
        with tempfile.TemporaryDirectory() as td:
            path=Path(td)/"before.json"
            data=capture(Fake())
            mod.save(path,data)
            self.assertEqual(mod.read(path),data)
            self.assertEqual(path.stat().st_mode & 0o777,0o600)
            with self.assertRaises(mod.CensusStop):
                mod.save(path,data)
            path.write_text('{"nonce":"x","nonce":"y"}')
            with self.assertRaisesRegex(mod.CensusStop,"duplicate key"):
                mod.read(path)
            path.write_text("x"*(mod.MAX_FILE_BYTES+10))
            with self.assertRaises(mod.CensusStop):
                mod.read(path)


if __name__=="__main__":
    unittest.main()
