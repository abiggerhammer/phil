#!/usr/bin/env python3
"""W3 fanout publisher-only, fsynced INTENT and exact-ref result receipts.

Never stores a token, GitHub response body, private key or raw exception text.
Per-job receipts are retained even if the next step fails.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import re
import tempfile

SCHEMA = "MHB-ATC-W3-FANOUT-EVIDENCE-V1"
SHA = re.compile(r"[0-9a-f]{40}\Z")
NONCE = re.compile(r"[0-9a-f]{12}\Z")
REF = re.compile(r"refs/heads/hamster/admitted/w3-fanout-([0-9a-f]{12})-canary\Z")
PHASES = {"publisher-create", "publisher-cleanup"}
STAGES = {"INTENT", "RESPONSE", "READ", "VERIFIED", "STOP"}
OPERATIONS = {"publisher-create-canary", "publisher-delete-canary"}
REASONS = {"SUCCESS", "UNKNOWN_AFTER_REQUEST", "UNEXPECTED_RESPONSE",
           "PRECONDITION_FAILED", "POST_STATE_CHANGED"}
MAX_BYTES = 32768
MAX_EVENTS = 32


class FanoutEvidenceError(ValueError):
    pass


def check(condition, message):
    if not condition:
        raise FanoutEvidenceError(message)


def bounded_sha(value):
    check(value is None or
          (isinstance(value, str) and SHA.fullmatch(value)),
          "invalid fanout evidence SHA")
    return value


class FanoutLedger:
    def __init__(self, path, *, phase, nonce, run_id, original_run_id,
                 dispatch_sha, original_dispatch_sha, target_sha,
                 workflow_tree_sha, installation_id):
        path = Path(path)
        temp = Path(os.environ.get("RUNNER_TEMP", "/nonexistent"))
        check(path.name == "w3-fanout-evidence.json" and
              path.parent == temp and temp.is_dir() and
              not path.exists() and not path.is_symlink(),
              "fanout evidence needs fresh exact runner-temporary path")
        check(phase in PHASES and
              isinstance(nonce, str) and NONCE.fullmatch(nonce) and
              type(run_id) is int and 0 < run_id < 10**16 and
              type(original_run_id) is int and 0 < original_run_id < 10**16,
              "invalid fanout evidence run/nonce")
        check(isinstance(installation_id, str) and
              re.fullmatch(r"[1-9][0-9]*", installation_id),
              "invalid publisher installation ID evidence")
        bounded_sha(dispatch_sha)
        bounded_sha(original_dispatch_sha)
        bounded_sha(target_sha)
        bounded_sha(workflow_tree_sha)
        self.path = path
        self.nonce = nonce
        self.ref = "refs/heads/hamster/admitted/w3-fanout-" + nonce + "-canary"
        self.doc = {
            "schema": SCHEMA, "phase": phase,
            "decision": "INCOMPLETE_NOT_CERTIFIED",
            "run_id": run_id, "original_run_id": original_run_id,
            "nonce": nonce, "ref": self.ref,
            "controller_dispatch_sha": dispatch_sha,
            "original_dispatch_sha": original_dispatch_sha,
            "target_sha": target_sha,
            "target_workflow_tree_sha": workflow_tree_sha,
            "publisher_app_id": 5782193,
            "installation_id": installation_id,
            "default_quarantine_checks": [],
            "events": [],
            "quarantine_certified": False,
            "w3_execution_authorized": False,
        }
        self._flush()

    def _flush(self):
        raw = (json.dumps(self.doc, sort_keys=True, separators=(",", ":")) +
               "\n").encode("utf-8")
        check(len(raw) <= MAX_BYTES, "fanout evidence volume exceeded")
        fd, temporary = tempfile.mkstemp(prefix=".fanout-evidence-",
                                        dir=self.path.parent)
        try:
            os.fchmod(fd, 0o600)
            with os.fdopen(fd, "wb") as out:
                out.write(raw)
                out.flush()
                os.fsync(out.fileno())
            os.replace(temporary, self.path)
            dfd = os.open(self.path.parent, os.O_RDONLY)
            try:
                os.fsync(dfd)
            finally:
                os.close(dfd)
        finally:
            if os.path.exists(temporary):
                os.unlink(temporary)

    def default_check(self, operation, selected_sha, tree_sha):
        check(operation in OPERATIONS and
              isinstance(selected_sha, str) and SHA.fullmatch(selected_sha) and
              isinstance(tree_sha, str) and SHA.fullmatch(tree_sha),
              "invalid default-branch semantic quarantine receipt")
        record = {"operation": operation, "default_sha": selected_sha,
                  "default_workflow_tree_sha": tree_sha}
        check(len(self.doc["default_quarantine_checks"]) < 8,
              "fanout default-check volume exceeded")
        self.doc["default_quarantine_checks"].append(record)
        self._flush()
        print("W3_FANOUT_DEFAULT " + json.dumps(record, sort_keys=True),
              flush=True)

    def record(self, operation, stage, *, pre_sha=None, target_sha=None,
               post_sha=None, http_status=None, reason=None):
        check(operation in OPERATIONS and stage in STAGES and
              reason in (REASONS | {None}) and
              (http_status is None or
               (type(http_status) is int and 100 <= http_status <= 599)),
              "unreviewed fanout evidence operation/response")
        for value in (pre_sha, target_sha, post_sha):
            bounded_sha(value)
        check(len(self.doc["events"]) < MAX_EVENTS,
              "fanout event volume exceeded")
        entry = {
            "operation": operation, "stage": stage,
            "ref": self.ref, "pre_sha": pre_sha,
            "target_sha": target_sha, "post_sha": post_sha,
            "http_status": http_status, "reason": reason,
        }
        self.doc["events"].append(entry)
        self._flush()
        print("W3_FANOUT_EVIDENCE " + json.dumps(entry, sort_keys=True),
              flush=True)

    def decision(self, value):
        check(value in {"STOP_INCOMPLETE", "CREATE_VERIFIED", "ABSENCE_VERIFIED"},
              "invalid fanout evidence final decision")
        self.doc["decision"] = value
        self._flush()
        print("W3_FANOUT_DECISION " + value, flush=True)
