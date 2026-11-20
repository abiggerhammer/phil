#!/usr/bin/env python3
"""W3 owner-local, offline-only source/ruleset/namespace commissioning planner.

This file deliberately contains NO API write function, token mint, or GH
command. Its PASS-like decision is a *review-ready design*, NEVER a permit
to execute a credential-bearing negative test.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys

from mhb_atc_immutable import check_ruleset

ROOT = Path(__file__).resolve().parents[1]
REPO = "abiggerhammer/phil"
WORKER_APP_ID = 5836223
PUBLISHER_APP_ID = 5782193
RULESET_ID = 27365284
REQUIRED_RULES = frozenset({"creation", "update", "deletion", "non_fast_forward"})
NONCE = re.compile(r"[0-9a-f]{12}\Z")
SHA = re.compile(r"[0-9a-f]{40}\Z")
MAX_JSON = 4_000_000


def insist(ok, reason):
    if not ok:
        raise ValueError(reason)


def unique_keys(items):
    result = {}
    for k, v in items:
        insist(k not in result, "ambiguous duplicate JSON key")
        result[k] = v
    return result


def load_json(path):
    with Path(path).open("rb") as stream:
        raw = stream.read(MAX_JSON + 1)
    insist(len(raw) <= MAX_JSON, "oversized untrusted snapshot")
    return json.loads(raw.decode("utf-8"), object_pairs_hook=unique_keys)


def refs_from_api(raw):
    """Exact Git matching-refs response, not a synthetic count or partial list."""
    insist(isinstance(raw, list), "invalid Git ref census")
    insist(len(raw) < 100, "cannot attest potentially truncated ref census")
    refs = set()
    for item in raw:
        insist(isinstance(item, dict), "invalid reference entry")
        ref, obj = item.get("ref"), item.get("object")
        insist(isinstance(ref, str) and
               ref.startswith("refs/heads/hamster/admitted/") and
               len(ref) < 200, "foreign or malformed admitted ref")
        insist(isinstance(obj, dict) and
               obj.get("type") == "commit" and
               isinstance(obj.get("sha"), str) and
               SHA.fullmatch(obj["sha"]), "invalid admitted object SHA")
        insist(ref not in refs, "duplicate ref in census")
        refs.add(ref)
    return refs


def live_main_sha(doc):
    insist(isinstance(doc, dict) and doc.get("ref") == "refs/heads/main"
           and isinstance(doc.get("object"), dict)
           and doc["object"].get("type") == "commit"
           and isinstance(doc["object"].get("sha"), str)
           and SHA.fullmatch(doc["object"]["sha"]),
           "missing exact GitHub main ref")
    return doc["object"]["sha"]


def plan(*, ruleset, admitted_refs, before, after, worker, lanes,
         publisher, expected_sha, nonce):
    """Pure fail-closed protocol; no network, no credential, no writes."""
    insist(isinstance(expected_sha, str) and SHA.fullmatch(expected_sha),
           "invalid locally reviewed SHA")
    insist(isinstance(nonce, str) and NONCE.fullmatch(nonce),
           "nonce must be 12 lower-case hex digits")
    current = live_main_sha(before)
    insist(live_main_sha(after) == current == expected_sha,
           "remote main changed or local checkout is not exact main")

    insist(isinstance(worker, dict)
           and worker.get("schema") == "MHB-ATC-WORKER-POLICY-V1"
           and worker.get("repository") == REPO
           and worker.get("worker_app_id") == WORKER_APP_ID
           and worker.get("worker_app_slug") == "phil-atc-worker"
           and worker.get("credential_holder") == "trusted-main-broker-only"
           and worker.get("direct_worker_installation_tokens") is False
           and worker.get("intended_permissions") ==
               {"contents": "write", "metadata": "read", "pull_requests": "none"}
           and worker.get("broker_activation") == "disabled",
           "worker broker source policy is not dormant and exact")
    insist(isinstance(lanes, dict)
           and lanes.get("repository") == REPO
           and lanes.get("pilot_only") is True
           and isinstance(lanes.get("lanes"), dict)
           and set(lanes["lanes"]) == {"phase2-selfhost", "phase2-embedded"}
           and all(isinstance(cfg, dict)
                   and cfg.get("enabled") is False
                   and all(cfg.get(field) is None for field in (
                       "source_repository", "source_owner",
                       "source_repository_id", "source_owner_id"))
                   for cfg in lanes["lanes"].values()),
           "W2 lane source registry not disabled/unconfigured")

    insist(isinstance(publisher, dict)
           and publisher.get("format") == "MHB-ATC-OWNER-RULESET-ATTESTATION-V1"
           and publisher.get("repository") == REPO
           and publisher.get("ruleset_id") == RULESET_ID
           and publisher.get("publisher_app_id") == PUBLISHER_APP_ID
           and publisher.get("publisher_app_slug") == "phil-atc-publisher",
           "publisher source attestation not exact")
    check_ruleset(ruleset, REPO, PUBLISHER_APP_ID, RULESET_ID,
                  attestation=publisher)
    insist(isinstance(ruleset.get("bypass_actors"), list)
           and ruleset["bypass_actors"] ==
           [{"actor_id": PUBLISHER_APP_ID, "actor_type": "Integration",
             "bypass_mode": "always"}],
           "owner-visible bypass must be publisher App only")
    insist(ruleset.get("current_user_can_bypass") == "never",
           "owner bypass changed, or cannot attest owner visibility")
    rules = ruleset.get("rules")
    insist(isinstance(rules, list) and
           {x.get("type") for x in rules} == REQUIRED_RULES
           and len(rules) == 4 and all(set(x) == {"type"} for x in rules),
           "unreviewed admitted-ref ruleset change")

    existing = refs_from_api(admitted_refs)
    insist(not existing,
           "admitted namespace occupied; identify active/orphan refs before testing")
    # Both probes are *absent* immutable refs, single path component under '*'.
    create_ref = f"hamster/admitted/w3-{nonce}-create"
    seed_ref = f"hamster/admitted/w3-{nonce}-seed"
    insist(create_ref != seed_ref and
           all(ref.startswith("hamster/admitted/w3-") and
               ref.count("/") == 2 for ref in (create_ref, seed_ref)),
           "unexpected ref namespace")
    return {
        "schema": "MHB-ATC-W3-READINESS-PROPOSAL-V1",
        "decision": "SOURCE_READINESS_CONFIRMED_REVIEW_REQUIRED",
        "execution_authorized": False,
        "credential_access_performed": False,
        "api_writes_performed": False,
        "repo": REPO,
        "main_sha": current,
        "ruleset_id": RULESET_ID,
        "worker_app_id": WORKER_APP_ID,
        "publisher_app_id": PUBLISHER_APP_ID,
        "admitted_refs_at_snapshot": 0,
        "disposable_create_ref": create_ref,
        "publisher_seed_ref": seed_ref,
        "planned_sequence": [
            "Review W3 risk, app installation-wide repository selection, and cleanup authority",
            "Separately authorize one publisher-created disposable seed and verified publisher deletion",
            "Separately authorize real worker-token denied creates/updates/deletes on only the disposable refs",
            "Separately authorize a direct PR creation/reopen test against a valid disposable head",
            "STOP immediately on any unexpectedly permitted write or ambiguous denial",
            "Collect exact principals, HTTP status, rule-suite evidence, SHAs, run IDs and cleanup receipts",
        ],
        "scope": "Read-only snapshot and reviewed protocol proposal ONLY; no live W3 negative proof",
    }


def git(*args):
    p = subprocess.run(["git", *args], cwd=ROOT,
                       capture_output=True, text=True, timeout=15, check=False)
    return p.stdout.strip() if p.returncode == 0 else None


def main():
    if __import__("os").environ.get("GITHUB_ACTIONS") == "true":
        raise ValueError("owner-local W3 read-only snapshot must not run inside Actions")
    if git("branch", "--show-current") != "main":
        raise ValueError("owner-local W3 plan requires current main")
    if git("status", "--porcelain", "--untracked-files=all") != "":
        raise ValueError("owner-local W3 plan requires a CLEAN checkout")
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--ruleset-json", required=True)
    p.add_argument("--admitted-refs-json", required=True)
    p.add_argument("--main-before-json", required=True)
    p.add_argument("--main-after-json", required=True)
    p.add_argument("--nonce", required=True)
    args = p.parse_args()
    result = plan(
        ruleset=load_json(args.ruleset_json),
        admitted_refs=load_json(args.admitted_refs_json),
        before=load_json(args.main_before_json),
        after=load_json(args.main_after_json),
        worker=load_json(ROOT / ".github/atc-worker-policy.json"),
        lanes=load_json(ROOT / ".github/atc-worker-lanes.json"),
        publisher=load_json(ROOT / ".github/atc-publisher-policy.json"),
        expected_sha=git("rev-parse", "HEAD"), nonce=args.nonce)
    print(json.dumps(result, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, OSError, TypeError, KeyError, json.JSONDecodeError) as exc:
        print("W3 read-only readiness BLOCKED: " + str(exc), file=sys.stderr)
        sys.exit(2)
