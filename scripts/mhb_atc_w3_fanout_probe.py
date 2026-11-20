#!/usr/bin/env python3
"""Dormant publisher-App W3 fanout canary: one CREATE, one DELETE, exact recovery.

Does not authorize execution. Source activation, repo variable, owner/main
first-attempt dispatch, separately protected App token and nonce must ALL
be approved in a later PR. No PR writes, worker App, update, force, retry,
or generic branch mutator. Fixed, sanitized stderr boundary.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import sys

from mhb_atc_immutable import check_ruleset
from mhb_atc_w3_default_quarantine import DefaultWorkflowQuarantine
from mhb_atc_w3_readiness import refs_from_api
from mhb_atc_w3_ref_trial import Client
from mhb_atc_w3_fanout_evidence import FanoutLedger
from mhb_atc_w3_fanout_provenance import (
    REPO, RULESET_ID, PUBLISHER_ID, TARGET, TREE,
    FanoutStop, check, sha, nonce_ref, run_id, json_doc,
    policy_check, current_policy, trusted_checkout,
    verify_target, policy_blob, make_binding, write_binding,
    read_binding, verify_original,
)

ROOT = Path(__file__).resolve().parents[1]
APP_SLUG = "phil-atc-publisher"
EVIDENCE_NAME = "w3-fanout-evidence.json"
OTHER_AUTOMATION_VARIABLES = (
    "MHB_ATC_W3_REF_TRIAL_ENABLED", "MHB_ATC_WORKER_BROKER_ENABLED",
    "MHB_ATC_IMMUTABLE_HEADS_ENABLED", "MHB_ATC_AUTO_ADMIT_ENABLED",
    "MHB_ATC_PHASE2_STAGE_BRIDGE_ENABLED",
)
PUBLISHER_OPERATION = {
    "publisher-create": "publisher-create-canary",
    "publisher-cleanup": "publisher-delete-canary",
}


def read_source_json(path):
    p = ROOT / path
    check(p.is_file() and not p.is_symlink(),
          "reviewed source policy missing")
    with p.open("rb") as stream:
        return json_doc(stream.read(4097))


def trusted_action_context():
    env = os.environ
    check(env.get("GITHUB_ACTIONS") == "true" and
          env.get("GITHUB_EVENT_NAME") == "workflow_dispatch" and
          env.get("GITHUB_REPOSITORY") == REPO and
          env.get("GITHUB_REF") == "refs/heads/main" and
          env.get("GITHUB_ACTOR") == "abiggerhammer" and
          env.get("GITHUB_TRIGGERING_ACTOR") == "abiggerhammer" and
          env.get("GITHUB_RUN_ATTEMPT") == "1",
          "fanout requires owner/main manual first attempt")
    return trusted_checkout(ROOT)


def source_gate(nonce, *, mode):
    p = current_policy(ROOT)
    if mode in ("prepare-origin", "create-preflight", "publisher-create"):
        policy_check(p, nonce=nonce, require_active=True)
        check(os.getenv("MHB_ATC_W3_FANOUT_ENABLED") == "true",
              "fanout runtime variable not separately enabled")
    for name in OTHER_AUTOMATION_VARIABLES:
        check(os.getenv(name, "").lower() != "true",
              "other ATC runtime activation must remain OFF")
    w3 = read_source_json(".github/atc-w3-ref-trial.json")
    verify_target(ROOT, p, w3)
    return p


def load_origin(nonce, *, independent):
    raw = os.getenv("W3_FANOUT_ORIGIN_RUN_ID", "")
    check(isinstance(raw, str) and re.fullmatch(r"[1-9][0-9]{0,15}", raw),
          "fanout original run ID missing")
    original_id = int(raw)
    current_id = int(os.getenv("GITHUB_RUN_ID", "0"))
    run_id(current_id)
    if independent:
        check(original_id != current_id,
              "independent recovery requires a different original run")
    else:
        check(original_id == current_id,
              "publisher original-run binding is not this run")
    path = Path(os.getenv("W3_FANOUT_BINDING_FILE", "/nonexistent"))
    return read_binding(path, nonce=nonce, expected_run_id=original_id)


def publisher_identity(token_client):
    check(os.getenv("W3_FANOUT_ACTION_APP_SLUG") == APP_SLUG,
          "publisher token action authenticated wrong App slug")
    installation = os.getenv("W3_FANOUT_ACTION_INSTALLATION_ID")
    check(isinstance(installation, str) and
          re.fullmatch(r"[1-9][0-9]*", installation),
          "publisher App installation identity absent")
    reply = token_client.request("GET", "/installation/repositories")
    check(reply.status == 200 and isinstance(reply.data, dict) and
          reply.data.get("total_count") == 1 and
          isinstance(reply.data.get("repositories"), list) and
          len(reply.data["repositories"]) == 1 and
          reply.data["repositories"][0].get("full_name") == REPO,
          "publisher token audience must be Phil only")
    return installation


class FanoutTrial:
    def __init__(self, client, *, nonce, dispatch_sha, origin,
                 publisher_attestation, validator=None, evidence=None):
        self.client = client
        self.ref = nonce_ref(nonce)
        self.branch = self.ref.removeprefix("refs/heads/")
        self.nonce = nonce
        self.dispatch_sha = sha(dispatch_sha)
        self.origin = origin
        self.attestation = publisher_attestation
        self.validator = (validator if validator is not None
                          else DefaultWorkflowQuarantine(ROOT))
        self.evidence = evidence
        self.default_checks = []

    def get(self, route):
        response = self.client.request("GET", route)
        check(response.status == 200, "authenticated fanout GitHub GET failed")
        return response.data

    def repository(self):
        doc = self.get("/repository")
        check(isinstance(doc, dict) and doc.get("full_name") == REPO and
              doc.get("default_branch") == "main",
              "fanout repository default branch or identity changed")

    def main(self, *, allow_drift=False):
        doc = self.get("/git/ref/heads/main")
        check(isinstance(doc, dict) and
              doc.get("ref") == "refs/heads/main" and
              isinstance(doc.get("object"), dict) and
              doc["object"].get("type") == "commit",
              "untrusted fanout main Git ref")
        current = sha(doc["object"].get("sha"))
        if not allow_drift:
            check(current == self.dispatch_sha,
                  "fanout main moved from trusted dispatch")
        return current

    def rules(self):
        data = self.get("/rulesets/" + str(RULESET_ID))
        check_ruleset(data, REPO, PUBLISHER_ID, RULESET_ID,
                      attestation=self.attestation)
        check(isinstance(data.get("rules"), list) and
              len(data["rules"]) == 4 and
              {x.get("type") for x in data["rules"]} ==
              {"creation", "deletion", "update", "non_fast_forward"} and
              (data.get("bypass_actors") is None or
               data["bypass_actors"] == [{
                   "actor_id": PUBLISHER_ID, "actor_type": "Integration",
                   "bypass_mode": "always"}]),
              "fanout ruleset changed or lacks sole publisher bypass")

    def census(self, *, canary_expected):
        refs = refs_from_api(self.get(
            "/git/matching-refs/heads/hamster/admitted/"))
        expected = {self.ref} if canary_expected else set()
        check(refs == expected,
              "fanout admitted namespace occupied or changed")
        return refs

    def ref_sha(self):
        reply = self.client.request("GET",
                                   "/git/ref/heads/" + self.branch)
        if reply.status == 404:
            return None
        doc = reply.data
        check(reply.status == 200 and isinstance(doc, dict) and
              doc.get("ref") == self.ref and
              isinstance(doc.get("object"), dict) and
              doc["object"].get("type") == "commit",
              "fanout exact canary ref response invalid")
        return sha(doc["object"].get("sha"))

    def gate(self, *, allow_drift=False, cleanup=False):
        self.repository()
        self.main(allow_drift=allow_drift)
        self.rules()
        existing = self.ref_sha()
        if cleanup:
            check(existing in (None, TARGET),
                  "fanout cleanup ref has foreign SHA")
            # Recovery is idempotent only for the exact known canary SHA
            # or a completely absent admitted namespace.
            self.census(canary_expected=existing is not None)
        else:
            self.census(canary_expected=False)
            check(existing is None,
                  "fanout proposed canary ref already exists")
        return existing

    def default_quarantine(self, operation, *, allow_drift):
        """Always use the live DEFAULT tree, not the frozen ref target."""
        self.repository()
        selected = self.main(allow_drift=allow_drift)
        selected_tree = self.validator.validate(selected)
        check(isinstance(selected_tree, str) and
              re.fullmatch(r"[0-9a-f]{40}", selected_tree),
              "invalid current-default quarantine tree")
        check(self.main(allow_drift=allow_drift) == selected,
              "default main changed during semantic quarantine")
        if self.evidence is not None:
            self.evidence.default_check(operation, selected, selected_tree)
        item = {"operation": operation, "default_sha": selected,
                "default_tree_sha": selected_tree}
        self.default_checks.append(item)
        return item

    def create_once(self):
        operation = "publisher-create-canary"
        self.gate(cleanup=False)
        checked = self.default_quarantine(operation, allow_drift=False)
        before = self.ref_sha()
        check(before is None, "fanout canary occupied before CREATE")
        self.census(canary_expected=False)
        self.evidence.record(operation, "INTENT", target_sha=TARGET)
        try:
            check(self.main() == checked["default_sha"],
                  "main changed before fanout CREATE")
            reply = self.client.request("POST", "/git/refs",
                                        {"ref": self.ref, "sha": TARGET})
        except Exception:
            self.evidence.record(operation, "STOP",
                                 target_sha=TARGET,
                                 reason="UNKNOWN_AFTER_REQUEST")
            raise
        self.evidence.record(operation, "RESPONSE",
                             target_sha=TARGET, http_status=reply.status)
        # Read post-state regardless of HTTP status; ambiguous response STOP.
        after = self.ref_sha()
        self.evidence.record(operation, "READ",
                             target_sha=TARGET, post_sha=after,
                             http_status=reply.status)
        check(reply.status == 201 and after == TARGET,
              "fanout CREATE did not establish exact reviewed canary")
        self.census(canary_expected=True)
        self.evidence.record(operation, "VERIFIED",
                             target_sha=TARGET, post_sha=after,
                             http_status=201, reason="SUCCESS")
        return {"decision": "CREATE_CONFIRMED_CLEANUP_STILL_REQUIRED",
                "ref": self.ref, "target_sha": TARGET,
                "quarantine_certified": False,
                "w3_execution_authorized": False}

    def cleanup_once(self):
        operation = "publisher-delete-canary"
        self.gate(allow_drift=True, cleanup=True)
        existing = self.ref_sha()
        if existing is None:
            self.census(canary_expected=False)
            return {"decision": "EXACT_CANARY_ABSENT",
                    "ref": self.ref, "quarantine_certified": False,
                    "w3_execution_authorized": False}
        check(existing == TARGET, "foreign canary cannot be deleted")
        self.census(canary_expected=True)
        checked = self.default_quarantine(operation, allow_drift=True)
        check(self.ref_sha() == TARGET, "fanout canary moved before DELETE")
        self.census(canary_expected=True)
        self.evidence.record(operation, "INTENT", pre_sha=TARGET)
        try:
            check(self.main(allow_drift=True) == checked["default_sha"],
                  "default main changed before fanout DELETE")
            reply = self.client.request(
                "DELETE", "/git/refs/heads/" + self.branch)
        except Exception:
            self.evidence.record(operation, "STOP", pre_sha=TARGET,
                                 reason="UNKNOWN_AFTER_REQUEST")
            raise
        self.evidence.record(operation, "RESPONSE",
                             pre_sha=TARGET, http_status=reply.status)
        after = self.ref_sha()
        self.evidence.record(operation, "READ",
                             pre_sha=TARGET, post_sha=after,
                             http_status=reply.status)
        check(reply.status == 204 and after is None,
              "fanout publisher DELETE not independently proven")
        self.census(canary_expected=False)
        self.evidence.record(operation, "VERIFIED", pre_sha=TARGET,
                             http_status=204, reason="SUCCESS")
        return {"decision": "EXACT_CANARY_ABSENT",
                "ref": self.ref, "quarantine_certified": False,
                "w3_execution_authorized": False}


def cli():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=(
        "plan", "prepare-origin", "create-preflight", "publisher-create",
        "recovery-plan", "publisher-cleanup"))
    parser.add_argument("--nonce", required=True)
    args = parser.parse_args()
    nonce_ref(args.nonce)
    dispatch_sha = trusted_action_context()
    independent = os.getenv("W3_FANOUT_MODE") == "cleanup"
    required_confirm = (
        "PLAN_ONLY" if args.phase == "plan" else
        "RECOVER_W3_FANOUT_CANARY_ONLY" if independent else
        "AUTHORIZE_W3_FANOUT_CANARY_ONLY")
    check(os.getenv("W3_FANOUT_CONFIRM") == required_confirm,
          "fanout owner acknowledgment absent or inconsistent")
    if independent:
        check(args.phase in ("recovery-plan", "publisher-cleanup"),
              "independent recovery cannot invoke CREATE")
    policy = source_gate(args.nonce, mode=args.phase)
    publisher = read_source_json(".github/atc-publisher-policy.json")

    # Read-only GitHub Actions token: independent of the publisher App.
    default_token = os.getenv("GITHUB_TOKEN")
    check(isinstance(default_token, str) and len(default_token) > 8,
          "fanout authenticated read-only Actions token absent")
    reader = Client(default_token)
    run = FanoutTrial(reader, nonce=args.nonce, dispatch_sha=dispatch_sha,
                      origin=None, publisher_attestation=publisher)

    if args.phase == "plan":
        # Plan remains GET-only with source inactive.
        existing = run.gate(cleanup=False)
        check(existing is None, "fanout plan cannot observe occupied namespace")
        check(os.getenv("W3_FANOUT_ORIGIN_RUN_ID", "") == "",
              "plan must not select historical origin")
        print(json.dumps({"decision": "SOURCE_ONLY_PLAN_NO_WRITES",
                          "execution_authorized": False, "ref": run.ref}))
        return 0

    if args.phase == "prepare-origin":
        check(os.getenv("W3_FANOUT_ORIGIN_RUN_ID", "") == "",
              "run mode must not accept a foreign original run")
        run.gate(cleanup=False)
        run.default_quarantine("publisher-create-canary",
                               allow_drift=False)
        current_id = run_id(int(os.getenv("GITHUB_RUN_ID", "0")))
        binding = make_binding(args.nonce, dispatch_sha, current_id,
                               policy_blob(ROOT, dispatch_sha))
        verify_original(reader, ROOT, binding, policy,
                        require_current_activation=True)
        write_binding(ROOT, binding)
        print(json.dumps({"decision": "ORIGINAL_FANOUT_BINDING_READY_NO_WRITES",
                          "execution_authorized": False,
                          "run_id": current_id, "ref": run.ref}))
        return 0

    origin = load_origin(args.nonce, independent=independent)
    verify_original(reader, ROOT, origin, policy,
                    require_current_activation=(
                        args.phase in ("create-preflight", "publisher-create")))
    run.origin = origin
    if args.phase in ("create-preflight", "recovery-plan"):
        current = run.gate(allow_drift=args.phase == "recovery-plan",
                           cleanup=args.phase == "recovery-plan")
        if args.phase == "create-preflight":
            run.default_quarantine("publisher-create-canary",
                                   allow_drift=False)
        elif current is not None:
            run.default_quarantine("publisher-delete-canary",
                                   allow_drift=True)
        print(json.dumps({"decision": "READ_ONLY_PREFLIGHT_NO_WRITES",
                          "execution_authorized": False,
                          "cleanup_required": current is not None,
                          "ref": run.ref}))
        return 0

    protected_token = os.getenv("W3_FANOUT_APP_TOKEN")
    check(isinstance(protected_token, str) and len(protected_token) > 8,
          "publisher App protected token missing")
    publisher_client = Client(protected_token)
    installation_id = publisher_identity(publisher_client)
    run.client = publisher_client
    ledger = FanoutLedger(
        Path(os.getenv("RUNNER_TEMP", "/nonexistent")) / EVIDENCE_NAME,
        phase=args.phase, nonce=args.nonce,
        run_id=run_id(int(os.getenv("GITHUB_RUN_ID", "0"))),
        original_run_id=origin["run_id"],
        dispatch_sha=dispatch_sha,
        original_dispatch_sha=origin["dispatch_sha"],
        target_sha=TARGET, workflow_tree_sha=TREE,
        installation_id=installation_id)
    run.evidence = ledger
    try:
        if args.phase == "publisher-create":
            result = run.create_once()
            ledger.decision("CREATE_VERIFIED")
        else:
            result = run.cleanup_once()
            ledger.decision("ABSENCE_VERIFIED")
    except Exception:
        ledger.decision("STOP_INCOMPLETE")
        raise
    print(json.dumps(result, sort_keys=True))
    return 0


def main():
    try:
        return cli()
    except Exception:
        print("W3 FANOUT STOP: sanitized failure; inspect W3_FANOUT_EVIDENCE",
              file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
