#!/usr/bin/env python3
"""Strict, durable, sanitized W3 evidence. Never serializes API bodies or keys.

Each intent is committed to a 0600 JSON file AND emitted as a bounded,
curated line in the GitHub Actions log *before* an API write. After a failed
step upload-artifact can preserve the file; a canceled worker may not upload,
so logs and live ref reconciliation remain independently necessary.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import re
import tempfile

SCHEMA = "MHB-ATC-W3-PARTIAL-EVIDENCE-V1"
SHA = re.compile(r"[0-9a-f]{40}\Z")
NONCE = re.compile(r"[0-9a-f]{12}\Z")
REF = re.compile(r"refs/heads/hamster/admitted/w3-([0-9a-f]{12})-(canary|create|seed)\Z")
PHASES = frozenset({"publisher-seed", "worker-negative", "publisher-cleanup"})
STAGES = frozenset({"INTENT", "RESPONSE", "VERIFIED", "STOP", "READ", "CLEANUP"})
OPERATIONS = frozenset({
    "publisher-create-canary", "publisher-delete-canary",
    "publisher-create-seed", "worker-create", "worker-update",
    "worker-force-update", "worker-delete", "publisher-cleanup-canary",
    "publisher-cleanup-create", "publisher-cleanup-seed", "stage",
})
MAX_EVENTS = 120
MAX_BYTES = 65536


class EvidenceError(ValueError):
    pass


def check(value, message):
    if not value:
        raise EvidenceError(message)


def bounded_sha(value):
    check(value is None or
          (isinstance(value, str) and SHA.fullmatch(value)),
          "unsanitized W3 evidence SHA")
    return value


class EvidenceLedger:
    def __init__(self, path, *, phase, nonce, run_id, source_sha,
                 parent_sha, grandparent_sha, workflow_tree_sha,
                 app_id, installation_id):
        path = Path(path)
        temp = Path(os.environ.get("RUNNER_TEMP", "/nonexistent"))
        check(path.name == "w3-evidence.json" and path.parent == temp and
              temp.is_dir() and not path.is_symlink(),
              "W3 evidence path must be exact trusted runner temporary path")
        check(phase in PHASES and
              isinstance(nonce, str) and NONCE.fullmatch(nonce),
              "W3 evidence requires known phase/nonce")
        check(type(run_id) is int and run_id > 0,
              "W3 evidence missing run ID")
        check(type(app_id) is int and app_id in (5782193, 5836223) and
              isinstance(installation_id, str) and
              installation_id.isdecimal() and
              int(installation_id) > 0,
              "W3 evidence principal/installation is not authenticated")
        check((phase == "worker-negative") == (app_id == 5836223),
              "W3 evidence phase and App principal mismatch")
        self.path = path
        self.nonce = nonce
        self.doc = {
            "schema": SCHEMA,
            "phase": phase,
            "decision": "INCOMPLETE_NOT_COMMISSIONED",
            "run_id": run_id,
            "nonce": nonce,
            "source_sha": bounded_sha(source_sha),
            "parent_sha": bounded_sha(parent_sha),
            "grandparent_sha": bounded_sha(grandparent_sha),
            "workflow_tree_sha": bounded_sha(workflow_tree_sha),
            "app_id": app_id,
            "installation_id": installation_id,
            "events": [],
        }
        self._flush()

    def _flush(self):
        """Atomic file replacement, written and fsynced before the operation."""
        data = (json.dumps(self.doc, sort_keys=True, separators=(",", ":")) +
                "\n").encode("utf-8")
        check(len(data) <= MAX_BYTES, "W3 evidence reached size limit")
        fd, tmp = tempfile.mkstemp(prefix=".w3-evidence-", dir=self.path.parent)
        try:
            os.fchmod(fd, 0o600)
            with os.fdopen(fd, "wb") as fp:
                fp.write(data)
                fp.flush()
                os.fsync(fp.fileno())
            os.replace(tmp, self.path)
            # The local artifact is always best effort under runner loss; the
            # log line below additionally permits remote forensic recovery.
            directory_fd = os.open(self.path.parent, os.O_RDONLY)
            try:
                os.fsync(directory_fd)
            finally:
                os.close(directory_fd)
        finally:
            if os.path.exists(tmp):
                os.unlink(tmp)

    def event(self, operation, stage, *, ref=None, pre_sha=None,
              target_sha=None, post_sha=None, http_status=None,
              denial=None, matched_diagnostic=None, reason=None):
        check(operation in OPERATIONS and stage in STAGES,
              "unrecognized W3 operation/stage")
        if ref is not None:
            check(isinstance(ref, str) and
                  (m := REF.fullmatch(ref)) and m.group(1) == self.nonce,
                  "W3 evidence references foreign ref")
        for value in (pre_sha, target_sha, post_sha):
            bounded_sha(value)
        check(http_status is None or
              (type(http_status) is int and 100 <= http_status <= 599),
              "W3 evidence HTTP code invalid")
        check(denial in (None, "RULESET_DENIED", "UNEXPECTED_SUCCESS",
                         "AMBIGUOUS_RESPONSE"),
              "W3 evidence denial class invalid")
        valid_diagnostic = None
        if matched_diagnostic is not None:
            check(isinstance(matched_diagnostic, str) and ref is not None and
                  matched_diagnostic in (
                      "GH013: Repository rule violations found for " + ref,
                      "Repository rule violations found for " + ref),
                  "W3 evidence cannot retain untrusted API diagnostic")
            valid_diagnostic = matched_diagnostic
        check(reason in (None, "INCOMPLETE", "UNEXPECTED_RESPONSE",
                         "WRONG_REF", "POST_STATE_CHANGED",
                         "PRECONDITION_FAILED", "CLEANUP_FAILED",
                         "SUCCESS", "UNKNOWN_AFTER_REQUEST"),
              "W3 evidence abort reason must be enumerated")
        record = {
            "operation": operation, "stage": stage, "ref": ref,
            "pre_sha": pre_sha, "target_sha": target_sha,
            "post_sha": post_sha, "http_status": http_status,
            "denial": denial, "matched_diagnostic": valid_diagnostic,
            "reason": reason,
        }
        check(len(self.doc["events"]) < MAX_EVENTS, "W3 evidence event limit reached")
        self.doc["events"].append(record)
        self._flush()
        # Only curatable source-defined fields are emitted; no API text or
        # exception object is printed. Flush BEFORE any remote write.
        print("W3_EVIDENCE " + json.dumps({
            "schema": SCHEMA, "run_id": self.doc["run_id"],
            "phase": self.doc["phase"], "nonce": self.nonce,
            "app_id": self.doc["app_id"],
            "installation_id": self.doc["installation_id"],
            **record}, sort_keys=True), flush=True)
        return record

    def decision(self, value):
        check(value in ("STOP_INCOMPLETE", "DENIALS_CONFIRMED",
                        "PUBLISHER_SEED_CONFIRMED", "CLEANUP_ABSENCE_CONFIRMED"),
              "invalid W3 evidence decision")
        self.doc["decision"] = value
        self._flush()
        print("W3_EVIDENCE_DECISION " + value, flush=True)
