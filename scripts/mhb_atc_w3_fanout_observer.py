#!/usr/bin/env python3
"""Read-only bounded W3 publisher App fanout event census.

This NEVER writes a GitHub ref, creates a PR, mints an App token, or certifies
W3 push quarantine. It helps independently compare all observed workflow runs
for push/create/delete across a fixed narrow UTC window. An absence in a
single census is not evidence of event-delivery completeness.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone, timedelta
import json
import os
from pathlib import Path
import re
import sys
import tempfile
from urllib.parse import quote

from mhb_atc_w3_ref_trial import Client

REPO = "abiggerhammer/phil"
SCHEMA = "MHB-ATC-W3-PUBLISHER-FANOUT-CENSUS-V1"
NONCE = re.compile(r"[0-9a-f]{12}\Z")
SHA = re.compile(r"[0-9a-f]{40}\Z")
TIMESTAMP = re.compile(r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z\Z")
EVENTS = ("push", "create", "delete")
MAX_PER_EVENT = 200
PAGE_SIZE = 4
MAX_WINDOW = timedelta(minutes=120)
MAX_FILE_BYTES = 300000
RUN_FIELDS = ("id", "event", "head_branch", "head_sha", "created_at", "actor",
              "path", "status", "conclusion")
ROOT = Path(__file__).resolve().parents[1]
POLICY = ".github/atc-w3-fanout.json"


class CensusStop(ValueError):
    pass


def check(predicate, reason):
    if not predicate:
        raise CensusStop(reason)


def iso(value):
    check(isinstance(value, str) and TIMESTAMP.fullmatch(value),
          "noncanonical census timestamp")
    parsed = datetime.strptime(value, "%Y-%m-%dT%H:%M:%SZ").replace(
        tzinfo=timezone.utc)
    check(parsed.strftime("%Y-%m-%dT%H:%M:%SZ") == value,
          "noncanonical census timestamp")
    return parsed


def nonce_ref(nonce):
    check(isinstance(nonce, str) and NONCE.fullmatch(nonce),
          "invalid fanout nonce")
    return "refs/heads/hamster/admitted/w3-fanout-" + nonce + "-canary"


def reviewed_policy():
    raw = (ROOT / POLICY).read_bytes()
    check(len(raw) < 4096, "oversized fanout observation policy")
    p = json.loads(raw)
    check(isinstance(p, dict) and
          p.get("schema") == "MHB-ATC-W3-PUBLISHER-FANOUT-V1" and
          p.get("repository") == REPO and
          type(p.get("source_authorized")) is bool and
          (p.get("approved_nonce") is None or
           (isinstance(p["approved_nonce"], str) and
            NONCE.fullmatch(p["approved_nonce"]))) and
          p.get("publisher_app_id") == 5782193 and
          p.get("ruleset_id") == 27365284 and
          p.get("ref_template") ==
          "refs/heads/hamster/admitted/w3-fanout-<nonce>-canary" and
          p.get("max_authorized_ref_mutations") == 2 and
          p.get("observation_events") == list(EVENTS) and
          p.get("observation_window_minutes_limit") == 120,
          "unreviewed fanout observer source policy")
    return p


def run_record(item, expected_event, window_start, window_end):
    check(isinstance(item, dict) and type(item.get("id")) is int
          and 0 < item["id"] < 10**16 and
          item.get("event") == expected_event and
          isinstance(item.get("head_sha"), str) and
          SHA.fullmatch(item["head_sha"]) and
          (item.get("head_branch") is None or
           (isinstance(item["head_branch"], str) and
            len(item["head_branch"]) < 256)) and
          isinstance(item.get("actor"), dict) and
          isinstance(item["actor"].get("login"), str) and
          0 < len(item["actor"]["login"]) < 128 and
          isinstance(item.get("path"), str) and
          0 < len(item["path"]) < 256 and
          isinstance(item.get("status"), str) and
          len(item["status"]) < 64 and
          (item.get("conclusion") is None or
           (isinstance(item["conclusion"], str) and
            len(item["conclusion"]) < 64)),
          "untrusted or malformed workflow-run census entry")
    date = iso(item.get("created_at"))
    check(window_start <= date <= window_end,
          "workflow-run census exceeded fixed UTC window")
    repository = item.get("repository")
    check(isinstance(repository, dict) and
          repository.get("full_name") == REPO,
          "workflow-run census contains a foreign repository")
    return {
        "id": item["id"], "event": item["event"],
        "head_sha": item["head_sha"],
        "head_branch": item["head_branch"], "created_at": item["created_at"],
        "actor": item["actor"]["login"],
        "path": item["path"], "status": item["status"],
        "conclusion": item["conclusion"],
    }


def collect(client, *, role, nonce, window_start, window_end, observed_at=None):
    check(role in ("before", "after"), "invalid census role")
    ref = nonce_ref(nonce)
    start, end = iso(window_start), iso(window_end)
    check(start < end and end - start <= MAX_WINDOW,
          "event census window is empty or too wide")
    if observed_at is None:
        observed_at = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    measured = iso(observed_at)
    check(measured >= start - timedelta(minutes=1),
          "census observation precedes its window")
    all_runs = {}
    counts = {}
    for event in EVENTS:
        reported_total = None
        event_runs = {}
        for page in range(1, MAX_PER_EVENT // PAGE_SIZE + 2):
            window = quote(window_start + ".." + window_end, safe="")
            endpoint = ("/actions/runs?event=" + event +
                        "&created=" + window +
                        "&per_page=" + str(PAGE_SIZE) + "&page=" + str(page))
            response = client.request("GET", endpoint)
            check(response.status == 200 and
                  isinstance(response.data, dict),
                  "GitHub Actions census GET unavailable")
            doc = response.data
            total = doc.get("total_count")
            batch = doc.get("workflow_runs")
            check(type(total) is int and 0 <= total < MAX_PER_EVENT and
                  isinstance(batch, list) and len(batch) <= PAGE_SIZE,
                  "Actions census may be truncated or malformed")
            if reported_total is None:
                reported_total = total
            check(reported_total == total,
                  "Actions census changed during pagination")
            for item in batch:
                record = run_record(item, event, start, end)
                check(record["id"] not in event_runs and
                      record["id"] not in all_runs,
                      "duplicate Actions run across event pages")
                event_runs[record["id"]] = record
            check(len(event_runs) <= total,
                  "Actions census returned more records than count")
            if len(event_runs) == total:
                break
            check(len(batch) == PAGE_SIZE,
                  "Actions census pagination incomplete")
        else:
            raise CensusStop("Actions census exceeded page bound")
        counts[event] = reported_total
        all_runs.update(event_runs)
    runs = sorted(all_runs.values(), key=lambda x: x["id"])
    check(len(runs) <= MAX_PER_EVENT * len(EVENTS),
          "Actions census inventory oversized")
    return {
        "schema": SCHEMA, "repository": REPO, "role": role, "nonce": nonce,
        "ref": ref, "window_start": window_start, "window_end": window_end,
        "observed_at": observed_at, "event_totals": counts, "runs": runs,
        "decision": "READ_ONLY_CENSUS_NOT_CERTIFIED",
    }


def check_snapshot(doc):
    check(isinstance(doc, dict) and
          set(doc) == {"schema", "repository", "role", "nonce", "ref",
                       "window_start", "window_end", "observed_at",
                       "event_totals", "runs", "decision"} and
          doc["schema"] == SCHEMA and doc["repository"] == REPO and
          doc["role"] in ("before", "after") and
          doc["ref"] == nonce_ref(doc["nonce"]) and
          doc["decision"] == "READ_ONLY_CENSUS_NOT_CERTIFIED" and
          isinstance(doc["runs"], list) and
          isinstance(doc["event_totals"], dict) and
          set(doc["event_totals"]) == set(EVENTS),
          "noncanonical fanout census artifact")
    start, end = iso(doc["window_start"]), iso(doc["window_end"])
    check(start < end and end-start <= MAX_WINDOW,
          "invalid census time bounds")
    iso(doc["observed_at"])
    validated = {}
    for record in doc["runs"]:
        check(isinstance(record, dict) and
              set(record) == set(RUN_FIELDS) and
              type(record.get("id")) is int and
              0 < record["id"] < 10**16 and
              record.get("event") in EVENTS and
              isinstance(record.get("head_sha"), str) and
              SHA.fullmatch(record["head_sha"]) and
              (record.get("head_branch") is None or
               isinstance(record.get("head_branch"), str)) and
              isinstance(record.get("actor"), str) and
              isinstance(record.get("path"), str) and
              isinstance(record.get("status"), str) and
              (record.get("conclusion") is None or
               isinstance(record.get("conclusion"), str)) and
              start <= iso(record["created_at"]) <= end and
              record["id"] not in validated,
              "malformed/duplicated curated census run")
        validated[record["id"]] = record
    for event in EVENTS:
        expected = doc["event_totals"][event]
        check(type(expected) is int and expected >= 0 and
              expected == sum(r["event"] == event for r in validated.values()),
              "fanout census does not match complete event counts")
    return validated


def compare(before, after, *, target_sha, publisher_actor):
    pre, post = check_snapshot(before), check_snapshot(after)
    check(before["role"] == "before" and after["role"] == "after" and
          all(before[k] == after[k] for k in (
              "nonce", "ref", "window_start", "window_end")),
          "census windows/ref differ")
    check(isinstance(target_sha, str) and SHA.fullmatch(target_sha),
          "invalid frozen canary SHA")
    check(isinstance(publisher_actor, str) and
          0 < len(publisher_actor) < 128,
          "invalid publisher actor")
    check(iso(before["observed_at"]) < iso(after["observed_at"]),
          "census observation times were not ordered")
    check(set(pre) <= set(post),
          "a previously observed Actions run disappeared")
    new = [post[k] for k in sorted(set(post) - set(pre))]
    branch = before["ref"].removeprefix("refs/heads/")
    suspects = [x for x in new if (
        x["head_branch"] == branch or
        x["actor"] == publisher_actor or
        (x["event"] in ("push", "create") and x["head_sha"] == target_sha))]
    elapsed = iso(after["observed_at"]) - iso(after["window_end"])
    result = {
        "schema": "MHB-ATC-W3-PUBLISHER-FANOUT-COMPARISON-V1",
        "nonce": before["nonce"], "ref": before["ref"],
        "target_sha": target_sha, "publisher_actor": publisher_actor,
        "before_count": len(pre), "after_count": len(post),
        "new_total": len(new), "potential_fanout_run_ids": [x["id"] for x in suspects],
        "other_new_run_count": len(new) - len(suspects),
        "observation_lag_seconds": int(elapsed.total_seconds()),
        "decision": ("INCOMPLETE_OBSERVATION_RECHECK" if elapsed < timedelta(minutes=15)
                     else "POTENTIAL_FANOUT_STOP_REVIEW" if suspects
                     else "NO_CANDIDATE_RUNS_REVIEW_REQUIRED"),
        "execution_authorized": False,
        "quarantine_certified": False,
    }
    return result


def save(path, document):
    path = Path(path)
    check(path.parent.is_dir() and not path.exists() and
          not path.is_symlink(), "refuse occupied fanout evidence path")
    data = (json.dumps(document, sort_keys=True, separators=(",", ":")) +
            "\n").encode("utf-8")
    check(len(data) < MAX_FILE_BYTES, "fanout census evidence oversized")
    fd, tmp = tempfile.mkstemp(prefix=".w3-fanout-", dir=path.parent)
    try:
        os.fchmod(fd, 0o600)
        with os.fdopen(fd, "wb") as f:
            f.write(data)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, path)
        directory = os.open(path.parent, os.O_RDONLY)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    finally:
        if os.path.exists(tmp):
            os.unlink(tmp)


def read(path):
    path = Path(path)
    check(path.is_file() and not path.is_symlink(),
          "fanout census evidence absent or symlinked")
    with path.open("rb") as f:
        raw = f.read(MAX_FILE_BYTES + 1)
    check(len(raw) <= MAX_FILE_BYTES, "oversized fanout census evidence")
    def distinct(pairs):
        doc = {}
        for k, v in pairs:
            check(k not in doc, "duplicate key in fanout evidence")
            doc[k] = v
        return doc
    return json.loads(raw.decode("utf-8"), object_pairs_hook=distinct)


def cli():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("collect", "compare"))
    parser.add_argument("--nonce")
    parser.add_argument("--role", choices=("before", "after"))
    parser.add_argument("--window-start")
    parser.add_argument("--window-end")
    parser.add_argument("--out")
    parser.add_argument("--before-file")
    parser.add_argument("--after-file")
    parser.add_argument("--target-sha")
    parser.add_argument("--publisher-actor")
    args = parser.parse_args()
    policy = reviewed_policy()
    if args.mode == "collect":
        check(args.nonce and args.role and args.window_start and
              args.window_end and args.out, "missing census parameters")
        if policy["approved_nonce"] is not None:
            check(args.nonce == policy["approved_nonce"],
                  "census nonce differs from source-approved experiment")
        token = os.getenv("GH_TOKEN") or os.getenv("GITHUB_TOKEN")
        check(isinstance(token, str) and len(token) >= 9,
              "read-only GitHub token required")
        doc = collect(Client(token), role=args.role, nonce=args.nonce,
                      window_start=args.window_start, window_end=args.window_end)
        save(args.out, doc)
        print(json.dumps({"decision":doc["decision"],"nonce":doc["nonce"],
                          "role":doc["role"],"runs":len(doc["runs"])}))
    else:
        check(args.before_file and args.after_file and args.target_sha and
              args.publisher_actor, "missing fanout comparison parameters")
        before, after = read(args.before_file), read(args.after_file)
        if policy["approved_nonce"] is not None:
            check(before.get("nonce") == policy["approved_nonce"] and
                  after.get("nonce") == policy["approved_nonce"],
                  "census uses a nonapproved experiment nonce")
        check(args.target_sha == policy["frozen_target_sha"],
              "census comparison target differs from source pin")
        print(json.dumps(compare(before,after,
                                 target_sha=args.target_sha,
                                 publisher_actor=args.publisher_actor),
                         sort_keys=True))


def main():
    try:
        cli()
        return 0
    except Exception:
        print("W3 FANOUT STOP: sanitized read-only census failure",
              file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
