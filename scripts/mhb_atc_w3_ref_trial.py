#!/usr/bin/env python3
"""Dormant, exact-ref W3 live trial controller. NEVER execute without reviewed activation.

Four protected-ref negative cases, NOT PR create/reopen. Each credential-bearing
job gets one App's token only; actual runs require independent source and repo
switches plus owner/main manual dispatch. Tests use a fake GitHub transport.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import http.client
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from urllib import error, request

from mhb_atc_immutable import check_ruleset
from mhb_atc_w3_readiness import refs_from_api
from mhb_atc_w3_provenance import (
    commit_sha, make_binding, read_binding, snapshot_tree, verify_origin,
)
from mhb_atc_w3_evidence import EvidenceLedger

ROOT = Path(__file__).resolve().parents[1]
REPO = "abiggerhammer/phil"
API_ROOT = "https://api.github.com/repos/" + REPO
PUBLISHER_ID = 5782193
WORKER_ID = 5836223
RULESET_ID = 27365284
NONCE = re.compile(r"[0-9a-f]{12}\Z")
SHA = re.compile(r"[0-9a-f]{40}\Z")
MAX_RESPONSE = 65536


class StopTrial(ValueError):
    """A failure/ambiguity demands STOP, never automatic retry."""


@dataclass(frozen=True)
class Reply:
    status: int
    data: object


def require(value, why):
    if not value:
        raise StopTrial(why)


def sha(value):
    require(isinstance(value, str) and SHA.fullmatch(value),
            "invalid exact commit SHA")
    return value


def names(nonce):
    require(isinstance(nonce, str) and NONCE.fullmatch(nonce),
            "invalid 12-lowercase-hex W3 nonce")
    return {
        which: f"hamster/admitted/w3-{nonce}-{which}"
        for which in ("canary", "create", "seed")
    }


def read(path):
    with (ROOT / path).open("rb") as f:
        data = f.read(150000)
    require(len(data) < 150000, "oversized reviewed source policy")
    return json.loads(data)


def policy_check(*, live: bool, nonce=None, recovery=False):
    trial = read(".github/atc-w3-ref-trial.json")
    worker = read(".github/atc-worker-policy.json")
    lanes = read(".github/atc-worker-lanes.json")
    publisher = read(".github/atc-publisher-policy.json")
    require(trial.get("schema") == "MHB-ATC-W3-REF-TRIAL-V1" and
            trial.get("repository") == REPO and
            trial.get("worker_app_id") == WORKER_ID and
            trial.get("publisher_app_id") == PUBLISHER_ID and
            trial.get("ruleset_id") == RULESET_ID and
            type(trial.get("live_authorized")) is bool and
            (trial.get("reviewed_quarantine_tree_sha") is None or
             (isinstance(trial["reviewed_quarantine_tree_sha"], str) and
              SHA.fullmatch(trial["reviewed_quarantine_tree_sha"]))) and
            trial.get("scope") ==
            "Four disposable protected-ref negative cases only; no PR tests" and
            (trial.get("approved_nonce") is None or
             (isinstance(trial.get("approved_nonce"), str) and
              NONCE.fullmatch(trial["approved_nonce"]))),
            "unreviewed W3 source-policy configuration")
    if live:
        # Never let a repository variable being switched OFF after seed
        # strand a protected ref: publisher cleanup remains authorized by
        # the exact reviewed source policy and the original manual run.
        if not recovery:
            for name in ("MHB_ATC_WORKER_BROKER_ENABLED",
                         "MHB_ATC_IMMUTABLE_HEADS_ENABLED",
                         "MHB_ATC_AUTO_ADMIT_ENABLED",
                         "MHB_ATC_PHASE2_STAGE_BRIDGE_ENABLED"):
                require(os.getenv(name, "").lower() != "true",
                        "other ATC activation switches must remain OFF")
        require(trial["live_authorized"] is True,
                "W3 live trials explicitly DISABLED in reviewed source")
        require(trial.get("push_ci_quarantine_verified") is True,
                "W3 publisher-created ref push CI quarantine NOT reviewed")
        require(isinstance(trial.get("reviewed_quarantine_tree_sha"), str) and
                SHA.fullmatch(trial["reviewed_quarantine_tree_sha"]),
                "no source-reviewed quarantine workflow tree SHA")
        require(isinstance(nonce, str) and
                trial.get("approved_nonce") == nonce and
                NONCE.fullmatch(nonce),
                "current nonce is not source-pinned for single reviewed trial")
        if not recovery:
            require(os.getenv("MHB_ATC_W3_REF_TRIAL_ENABLED") == "true",
                    "W3 live trials require separately enabled exact repo switch")
        if recovery:
            require(os.getenv("W3_CONFIRM") in (
                        "AUTHORIZE_W3_PROTECTED_REFS_ONLY",
                        "RECOVER_W3_EXACT_REFS_ONLY"),
                    "publisher recovery owner confirmation missing")
        else:
            require(os.getenv("W3_CONFIRM") == "AUTHORIZE_W3_PROTECTED_REFS_ONLY",
                    "explicit bounded owner confirmation missing")
        require(os.getenv("GITHUB_ACTIONS") == "true" and
                os.getenv("GITHUB_EVENT_NAME") == "workflow_dispatch" and
                os.getenv("GITHUB_ACTOR") == "abiggerhammer" and
                os.getenv("GITHUB_TRIGGERING_ACTOR") == "abiggerhammer" and
                os.getenv("GITHUB_RUN_ATTEMPT") == "1" and
                os.getenv("GITHUB_REPOSITORY") == REPO and
                os.getenv("GITHUB_REF") == "refs/heads/main",
                "not the trusted owner/main manual Actions context")
    else:
        require(trial["live_authorized"] is False,
                "read-only plan must not be used as evidence of active W3 mode")
    require(worker.get("schema") == "MHB-ATC-WORKER-POLICY-V1" and
            worker.get("worker_app_id") == WORKER_ID and
            worker.get("worker_app_slug") == "phil-atc-worker" and
            worker.get("broker_activation") == "disabled" and
            worker.get("direct_worker_installation_tokens") is False and
            worker.get("credential_holder") == "trusted-main-broker-only" and
            worker.get("intended_permissions") ==
            {"contents": "write", "metadata": "read", "pull_requests": "none"},
            "worker credential or activation source contract changed")
    require(lanes.get("schema") == "MHB-ATC-W2-LANES-V1" and
            isinstance(lanes.get("lanes"), dict) and
            set(lanes["lanes"]) == {"phase2-selfhost", "phase2-embedded"} and
            all(isinstance(x, dict) and x.get("enabled") is False and
                all(x.get(k) is None for k in (
                    "source_repository", "source_owner",
                    "source_repository_id", "source_owner_id"))
                for x in lanes["lanes"].values()),
            "worker lanes must be dormant and without fork identity")
    require(publisher.get("ruleset_id") == RULESET_ID and
            publisher.get("publisher_app_id") == PUBLISHER_ID and
            publisher.get("publisher_app_slug") == "phil-atc-publisher",
            "publisher App attestation changed")
    return publisher


def attest_live_worker_identity(receipt, installation_id):
    """Bind W1 JWT-authenticated App/installation metadata to this token."""
    require(isinstance(receipt, dict) and
            receipt.get("decision") == "authenticated-worker-app-and-installation"
            and receipt.get("app_id") == WORKER_ID
            and receipt.get("app_slug") == "phil-atc-worker"
            and receipt.get("permissions") ==
                {"contents": "write", "metadata": "read"}
            and receipt.get("repository_selection") == "selected"
            and type(receipt.get("installation_id")) is int
            and receipt["installation_id"] > 0
            and str(receipt["installation_id"]) == installation_id,
            "worker token installation not bound to protected JWT App metadata")


def local_commits():
    def run(*args):
        p = subprocess.run(["git", *args], cwd=ROOT, capture_output=True,
                           text=True, timeout=20, check=False)
        require(p.returncode == 0, "local trusted Git query failed")
        return p.stdout.strip()
    require(run("branch", "--show-current") == "main",
            "must check out trusted main (not a PR or fork)")
    require(run("status", "--porcelain", "--untracked-files=all") == "",
            "trusted main checkout must be completely clean")
    current = sha(run("rev-parse", "HEAD"))
    parent = sha(run("rev-parse", "HEAD^1"))
    grandparent = sha(run("rev-parse", "HEAD^1^1"))
    require(len({current, parent, grandparent}) == 3,
            "exact tested source commit lineage is ambiguous")
    require(os.getenv("GITHUB_SHA", current) == current,
            "workflow dispatch SHA does not equal checked-out source")
    return current, parent, grandparent


class _NoRedirect(request.HTTPRedirectHandler):
    """Never forward an App bearer token to a redirect destination."""

    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


class Client:
    """Only fixed-repository routes, bounded JSON, no redirects or retry."""

    def __init__(self, token):
        self.token = token

    def request(self, method, endpoint, data=None):
        require(method in {"GET", "POST", "PATCH", "DELETE"},
                "unsupported method")
        require(isinstance(endpoint, str) and
                endpoint.startswith("/") and
                ".." not in endpoint and
                "?" not in endpoint and
                not endpoint.startswith("//"),
                "unreviewed API endpoint")
        if method != "GET":
            require(isinstance(self.token, str) and len(self.token) > 8,
                    "write token missing")
        full = ("https://api.github.com" + endpoint
                if endpoint == "/installation/repositories"
                else API_ROOT + endpoint)
        payload = None if data is None else json.dumps(
            data, separators=(",", ":"), sort_keys=True).encode("utf-8")
        headers = {"Accept": "application/vnd.github+json",
                   "X-GitHub-Api-Version": "2022-11-28"}
        if self.token:
            headers["Authorization"] = "Bearer " + self.token
        if payload is not None:
            headers["Content-Type"] = "application/json"
        req = request.Request(full, data=payload, headers=headers, method=method)
        try:
            try:
                with request.build_opener(_NoRedirect).open(req, timeout=20) as response:
                    status = response.status
                    raw = response.read(MAX_RESPONSE + 1)
            except error.HTTPError as exc:
                status = exc.code
                raw = exc.read(MAX_RESPONSE + 1)
        except (OSError, http.client.HTTPException, ValueError):
            # Includes URLError, malformed status lines and response-read
            # failures. Their exception text may contain remote-controlled
            # bytes or secrets; do not propagate it to any output boundary.
            raise StopTrial("GitHub transport or protocol failure") from None
        # No exception text or raw remote response is ever logged: it may
        # carry unexpectedly sensitive data or an injected instruction.
        require(len(raw) <= MAX_RESPONSE, "oversized GitHub response")
        if not raw:
            return Reply(status, {})
        try:
            body = json.loads(raw.decode("utf-8"))
        except (UnicodeError, ValueError):
            raise StopTrial("non-JSON GitHub response")
        return Reply(status, body)


class Trial:
    def __init__(self, client, nonce, current, parent, grandparent,
                 publisher, evidence=None):
        self.client = client
        self.refs = names(nonce)
        self.current, self.parent, self.grandparent = (
            sha(current), sha(parent), sha(grandparent))
        self.publisher = publisher
        self.receipts = []
        self.evidence = evidence
        self.last_denial_diagnostic = None

    def audit(self, operation, stage, **fields):
        if self.evidence is not None:
            return self.evidence.event(operation, stage, **fields)
        return None

    def get(self, endpoint):
        answer = self.client.request("GET", endpoint)
        require(answer.status == 200, "live GitHub GET failed (not trusted)")
        return answer.data

    def rules(self):
        result = self.get("/rulesets/" + str(RULESET_ID))
        check_ruleset(result, REPO, PUBLISHER_ID, RULESET_ID,
                      attestation=self.publisher)
        # Lower-privileged App tokens may see redacted bypass actors. This
        # version pin uses the owner-reviewed, unredacted source attestation.
        if result.get("bypass_actors") is not None:
            require(result["bypass_actors"] ==
                    [{"actor_id": PUBLISHER_ID, "actor_type": "Integration",
                      "bypass_mode": "always"}],
                    "live bypass actors differ from reviewed publisher")
        require({x.get("type") for x in result.get("rules", [])} ==
                {"creation", "update", "deletion", "non_fast_forward"} and
                len(result.get("rules", [])) == 4,
                "changed ruleset must be reviewed before live writes")

    def main(self, *, allow_drift=False):
        doc = self.get("/git/ref/heads/main")
        live = doc.get("object", {}).get("sha")
        sha(live)
        if not allow_drift:
            require(live == self.current,
                    "main moved since trusted workflow dispatch")
        return live

    def census(self, wanted):
        """Read entire admitted prefix, never use a partial list as absence."""
        doc = self.get("/git/matching-refs/heads/hamster/admitted/")
        actual = refs_from_api(doc)
        require(actual == {"refs/heads/" + x for x in wanted},
                "unreviewed admitted-ref occupancy or race")
        return actual

    def ref(self, kind):
        name = self.refs[kind]
        answer = self.client.request("GET", "/git/ref/heads/" + name)
        if answer.status == 404:
            return None
        require(answer.status == 200 and
                isinstance(answer.data, dict) and
                answer.data.get("ref") == "refs/heads/" + name and
                isinstance(answer.data.get("object"), dict) and
                answer.data["object"].get("type") == "commit",
                "unexpected GitHub ref/authorization response")
        return sha(answer.data["object"].get("sha"))

    def gate(self, kinds, *, cleanup=False):
        self.rules()
        self.main(allow_drift=cleanup)
        self.census([self.refs[k] for k in kinds])

    def token_audience(self):
        # Installation token, not the runner default token.
        response = self.client.request(
            "GET", "/installation/repositories")
        require(response.status == 200 and
                isinstance(response.data, dict) and
                response.data.get("total_count") == 1 and
                isinstance(response.data.get("repositories"), list) and
                len(response.data["repositories"]) == 1 and
                response.data["repositories"][0].get("full_name") == REPO,
                "App token audience not exactly Phil")

    def create(self, kind, commit):
        return self.client.request(
            "POST", "/git/refs",
            {"ref": "refs/heads/" + self.refs[kind], "sha": sha(commit)})

    def patch(self, kind, commit, force):
        return self.client.request(
            "PATCH", "/git/refs/heads/" + self.refs[kind],
            {"sha": sha(commit), "force": force})

    def delete(self, kind):
        return self.client.request(
            "DELETE", "/git/refs/heads/" + self.refs[kind])

    def _write_and_record(self, operation, kind, method, *, target_sha=None,
                          pre_sha=None):
        """Durably persist intent BEFORE any potential ref mutation.

        If the request fails ambiguously, the log and artifact say ATTEMPTED;
        no fabricated denial/success is recorded. No automatic retry exists.
        """
        ref = "refs/heads/" + self.refs[kind]
        self.audit(operation, "INTENT", ref=ref, pre_sha=pre_sha,
                   target_sha=target_sha)
        try:
            reply = method()
        except Exception:
            self.audit(operation, "STOP", ref=ref, pre_sha=pre_sha,
                       target_sha=target_sha, reason="UNKNOWN_AFTER_REQUEST")
            raise
        self.audit(operation, "RESPONSE", ref=ref, pre_sha=pre_sha,
                   target_sha=target_sha, http_status=reply.status)
        return reply

    def public_receipt(self, phase, decision):
        return {
            "schema": "MHB-ATC-W3-REF-TRIAL-RECEIPT-V1",
            "phase": phase, "decision": decision,
            "run_id": os.getenv("GITHUB_RUN_ID", "offline-fixture"),
            "trusted_sha": self.current,
            "nonce": self.refs["create"].split("-")[-2],
            "source_live_activation_required": True,
            "worker_app_id": WORKER_ID, "publisher_app_id": PUBLISHER_ID,
            "ruleset_id": RULESET_ID,
            "events": list(self.receipts),
            "no_pr_operations": True,
        }

    def record(self, op, result):
        self.receipts.append({"operation": op, "result": result})

    def forbidden(self, reply, kind, op):
        """Prove the SAME diagnostic names one COMPLETE, case-exact ref.

        No substring matching, case folding of Git refs or concatenation of
        independent GitHub error fields. A malformed/ambiguous response STOPs.
        """
        if reply.status not in (403, 422) or not isinstance(reply.data, dict):
            raise StopTrial("unexpected or ambiguous negative write response")
        expected = "refs/heads/" + self.refs[kind]
        message = reply.data.get("message")
        errors = reply.data.get("errors", [])
        if message is not None and not isinstance(message, str):
            raise StopTrial("malformed GitHub denial message")
        if not isinstance(errors, list) or any(
                not isinstance(item, dict) or
                not isinstance(item.get("message"), str) for item in errors):
            raise StopTrial("malformed GitHub denial errors")
        diagnostics = ([message] if isinstance(message, str) else [])
        diagnostics.extend(item["message"] for item in errors)
        # Supported diagnostics put the full ref at the END of the message.
        # Do not tokenize on punctuation: commas, semicolons, parentheses,
        # braces, and quotes can all be legal Git ref-name characters.
        # Any trailing characters become part of the captured ref, which
        # must match the expected spelling byte-for-byte.
        prefixes = (
            "GH013: Repository rule violations found for ",
            "Repository rule violations found for ",
        )
        accepted = False
        self.last_denial_diagnostic = None
        for diagnostic in diagnostics:
            if diagnostic == "Validation Failed":
                # GitHub can wrap an exact per-error ruleset diagnostic in a
                # generic top-level validation message. Neither field alone
                # constitutes a valid denial.
                continue
            prefix = next((p for p in prefixes if diagnostic.startswith(p)), None)
            if prefix is None:
                # Unknown formats, including a GH013 report with an
                # unreviewed layout, are not evidence of an exact-ref denial.
                raise StopTrial("unsupported or ambiguous ruleset denial diagnostic")
            named_ref = diagnostic[len(prefix):]
            if named_ref != expected:
                raise StopTrial("ruleset diagnostic names wrong or ambiguous ref")
            accepted = True
            self.last_denial_diagnostic = diagnostic
        if not accepted:
            raise StopTrial("HTTP error was not exact-ref ruleset denial")
        return "RULESET_DENIED"

    def publisher_seed(self):
        self.gate([])
        for kind in ("canary", "create", "seed"):
            require(self.ref(kind) is None, "disposable ref already exists")
        answer = self._write_and_record(
            "publisher-create-canary", "canary",
            lambda: self.create("canary", self.parent), target_sha=self.parent)
        canary_after = self.ref("canary")
        self.audit("publisher-create-canary", "READ",
                   ref="refs/heads/" + self.refs["canary"],
                   target_sha=self.parent, post_sha=canary_after,
                   http_status=answer.status)
        require(answer.status == 201 and canary_after == self.parent,
                "publisher canary CREATE / SHA not confirmed")
        self.audit("publisher-create-canary", "VERIFIED",
                   ref="refs/heads/" + self.refs["canary"],
                   target_sha=self.parent, post_sha=self.parent,
                   http_status=201, reason="SUCCESS")
        answer = self._write_and_record(
            "publisher-delete-canary", "canary",
            lambda: self.delete("canary"), pre_sha=self.parent)
        canary_after = self.ref("canary")
        self.audit("publisher-delete-canary", "READ",
                   ref="refs/heads/" + self.refs["canary"],
                   pre_sha=self.parent, post_sha=canary_after,
                   http_status=answer.status)
        require(answer.status == 204 and canary_after is None,
                "publisher canary DELETE / cleanup not proven")
        self.audit("publisher-delete-canary", "VERIFIED",
                   ref="refs/heads/" + self.refs["canary"],
                   pre_sha=self.parent, http_status=204, reason="SUCCESS")
        self.record("publisher_create_delete_canary", "PASS")
        self.gate([])
        answer = self._write_and_record(
            "publisher-create-seed", "seed",
            lambda: self.create("seed", self.parent), target_sha=self.parent)
        seed_after = self.ref("seed")
        self.audit("publisher-create-seed", "READ",
                   ref="refs/heads/" + self.refs["seed"],
                   target_sha=self.parent, post_sha=seed_after,
                   http_status=answer.status)
        require(answer.status == 201 and seed_after == self.parent,
                "publisher seed creation not confirmed")
        self.audit("publisher-create-seed", "VERIFIED",
                   ref="refs/heads/" + self.refs["seed"],
                   target_sha=self.parent, post_sha=self.parent,
                   http_status=201, reason="SUCCESS")
        self.gate(["seed"])
        self.record("publisher_seed_at_first_parent", "PASS")
        return self.public_receipt("publisher-seed", "PUBLISHER_CLEANUP_CANARY_PASSED")

    def worker_probe(self):
        self.gate(["seed"])
        require(self.ref("seed") == self.parent and
                self.ref("create") is None and
                self.ref("canary") is None, "seed/preflight state changed")
        attempts = [
            ("deny-create", "create", lambda: self.create("create", self.current)),
            ("deny-update", "seed", lambda: self.patch("seed", self.current, False)),
            ("deny-force-update", "seed", lambda: self.patch("seed", self.grandparent, True)),
            ("deny-delete", "seed", lambda: self.delete("seed")),
        ]
        for op, kind, run in attempts:
            self.gate(["seed"])
            require(self.ref("seed") == self.parent and self.ref("create") is None,
                    "immutable seed changed before worker negative request")
            # Exactly ONE request; never retry after an ambiguous response.
            work = {
                "deny-create": ("worker-create", self.current),
                "deny-update": ("worker-update", self.current),
                "deny-force-update": ("worker-force-update", self.grandparent),
                "deny-delete": ("worker-delete", None),
            }
            operation, target_sha = work[op]
            before = self.ref(kind)
            answer = self._write_and_record(
                operation, kind, run, target_sha=target_sha, pre_sha=before)
            # Read the resulting state BEFORE interpreting the denial body.
            # In particular, a false-denial 201 must record the newly created
            # ref SHA in a durable partial receipt before we STOP.
            after = self.ref(kind)
            self.audit(operation, "READ",
                       ref="refs/heads/" + self.refs[kind],
                       pre_sha=before, target_sha=target_sha,
                       post_sha=after, http_status=answer.status)
            classification = self.forbidden(answer, kind, op)
            require(after == before and
                    self.ref("seed") == self.parent and
                    self.ref("create") is None,
                    "worker negative attempt altered a protected ref")
            self.audit(operation, "VERIFIED",
                       ref="refs/heads/" + self.refs[kind],
                       pre_sha=before, target_sha=target_sha,
                       post_sha=after, http_status=answer.status,
                       denial=classification,
                       matched_diagnostic=self.last_denial_diagnostic)
            self.record(op, classification)
        return self.public_receipt("worker-negative", "FOUR_REF_RULE_DENIALS_OBSERVED")

    def publisher_recovery_plan(self):
        """GET-only owned-ref inventory before any separately dispatched recovery."""
        self.rules()
        self.main(allow_drift=True)
        statuses = {}
        for kind in ("canary", "create", "seed"):
            found = self.ref(kind)
            require(found is None or
                    found in {self.current, self.parent, self.grandparent},
                    "UNKNOWN SHA: do not mint cleanup token for this ref")
            statuses[kind] = "ABSENT" if found is None else "KNOWN_DISPOSABLE"
        receipt = self.public_receipt(
            "recovery-plan", "EXACT_KNOWN_REF_CLEANUP_ELIGIBLE")
        receipt["refs"] = statuses
        receipt["execution_authorized"] = False
        return receipt

    def publisher_cleanup(self):
        """Idempotence is safe only for exact known SHA and exact nonce refs."""
        # The cleanup job runs after failed seed/probe as well. Main may move;
        # publisher may still clean only known disposable SHA values.
        self.rules()
        self.main(allow_drift=True)
        for kind in ("canary", "create", "seed"):
            found = self.ref(kind)
            operation = "publisher-cleanup-" + kind
            ref = "refs/heads/" + self.refs[kind]
            if found is None:
                self.audit(operation, "READ", ref=ref, reason="SUCCESS")
                self.record("publisher_cleanup_" + kind, "ALREADY_ABSENT")
                continue
            if found not in {self.current, self.parent, self.grandparent}:
                self.audit(operation, "STOP", ref=ref, pre_sha=found,
                           reason="PRECONDITION_FAILED")
                raise StopTrial("UNKNOWN SHA at disposable ref: manual publisher recovery required")
            answer = self._write_and_record(
                operation, kind, lambda: self.delete(kind), pre_sha=found)
            after = self.ref(kind)
            self.audit(operation, "READ", ref=ref, pre_sha=found,
                       post_sha=after, http_status=answer.status)
            require(answer.status == 204 and after is None,
                    "publisher cleanup incomplete; stop and escalate")
            self.audit(operation, "VERIFIED", ref=ref, pre_sha=found,
                       http_status=204, reason="SUCCESS")
            self.record("publisher_cleanup_" + kind, "DELETED_EXACT_DISPOSABLE")
        return self.public_receipt("publisher-cleanup", "OWNED_DISPOSABLE_REFS_ABSENT")


def _write_origin_artifact(binding):
    """Prepare nonsecret lineage before protected credentials can exist."""
    base = Path(os.environ.get("RUNNER_TEMP", "/nonexistent"))
    require(base.is_dir(), "trusted Actions temporary directory unavailable")
    path = base / "w3-origin.json"
    require(not path.exists() and not path.is_symlink(),
            "origin artifact path occupied")
    data = (json.dumps(binding, sort_keys=True, separators=(",", ":")) +
            "\n").encode("utf-8")
    require(len(data) < 4096, "origin artifact too large")
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    fd = os.open(path, flags, 0o600)
    with os.fdopen(fd, "wb") as fp:
        fp.write(data)
        fp.flush()
        os.fsync(fp.fileno())
    return path


def _verified_recovery_origin(nonce, reviewed_tree):
    """Owner default token, actions:read + contents:read; no App credentials."""
    source_id = os.environ.get("W3_ORIGIN_RUN_ID", "")
    require(isinstance(source_id, str) and
            re.fullmatch(r"[1-9][0-9]{0,15}", source_id),
            "independent recovery requires original Actions run ID")
    origin_run_id = int(source_id)
    require(str(origin_run_id) != os.environ.get("GITHUB_RUN_ID"),
            "cannot recover from the same run as its origin")
    path = Path(os.environ.get("W3_ORIGIN_BINDING_FILE", "/nonexistent"))
    require(path.name == "w3-origin.json" and path.is_file(),
            "downloaded original W3 binding is absent")
    original = read_binding(
        path, nonce=nonce, original_run_id=origin_run_id,
        reviewed_tree=reviewed_tree)
    reader = os.environ.get("GITHUB_TOKEN")
    require(isinstance(reader, str) and len(reader) > 8,
            "authenticated read-only GitHub Actions token required")
    return verify_origin(Client(reader), original)


def cli():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=(
        "plan", "prepare-origin", "recovery-plan",
        "publisher-seed", "worker-negative", "publisher-cleanup"))
    parser.add_argument("--nonce", required=True)
    parser.add_argument("--authorize-live", action="store_true",
                        help="legacy read-only plan gate (never performs writes)")
    args = parser.parse_args()
    names(args.nonce)
    require(not args.authorize_live or args.phase == "plan",
            "authorize-live only applies to read-only plan")

    live = args.phase not in ("plan",) or args.authorize_live
    recovery = args.phase in ("publisher-cleanup", "recovery-plan")
    publisher = policy_check(live=live, nonce=args.nonce, recovery=recovery)
    local_current, local_parent, local_grandparent = local_commits()
    trial_cfg = read(".github/atc-w3-ref-trial.json")
    reviewed_tree = trial_cfg.get("reviewed_quarantine_tree_sha")

    independent_recovery = bool(os.environ.get("W3_ORIGIN_RUN_ID"))
    if args.phase == "recovery-plan":
        require(independent_recovery,
                "recovery-plan must use authenticated original run artifact")
    if independent_recovery:
        require(args.phase in ("recovery-plan", "publisher-cleanup"),
                "original-run input only permitted for publisher recovery")
        binding = _verified_recovery_origin(args.nonce, reviewed_tree)
        current, parent, grandparent = (
            binding["source_sha"], binding["parent_sha"],
            binding["grandparent_sha"])
    else:
        current, parent, grandparent = (
            local_current, local_parent, local_grandparent)
        if live:
            snapshot_tree(ROOT, current, parent, grandparent, reviewed_tree)

    protected_token = args.phase in (
        "publisher-seed", "worker-negative", "publisher-cleanup")
    token = (os.environ.get("W3_APP_TOKEN") if protected_token else
             os.environ.get("GITHUB_TOKEN"))
    if protected_token:
        require(isinstance(token, str) and len(token) > 8,
                "protected installation token missing")
        expected_slug = ("phil-atc-worker" if args.phase == "worker-negative"
                         else "phil-atc-publisher")
        installation_id = os.environ.get("W3_ACTION_INSTALLATION_ID")
        require(os.environ.get("W3_ACTION_APP_SLUG") == expected_slug and
                isinstance(installation_id, str) and
                re.fullmatch(r"[1-9][0-9]*", installation_id),
                "actual token principal/installation not authenticated")
        if args.phase == "worker-negative":
            receipt_path = Path(os.environ.get("RUNNER_TEMP", "")) / "atc-w1id-receipt.json"
            require(receipt_path.is_file() and
                    receipt_path.stat().st_size <= 65536,
                    "worker JWT verification receipt missing")
            try:
                jwt_receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
            except (UnicodeError, ValueError, OSError):
                raise StopTrial("unreadable worker JWT identity receipt")
            attest_live_worker_identity(jwt_receipt, installation_id)

    client = Client(token)
    evidence = None
    if protected_token:
        run_id = os.environ.get("GITHUB_RUN_ID", "")
        require(isinstance(run_id, str) and
                re.fullmatch(r"[1-9][0-9]{0,15}", run_id),
                "W3 protected job run ID missing")
        evidence = EvidenceLedger(
            Path(os.environ.get("RUNNER_TEMP", "/nonexistent")) / "w3-evidence.json",
            phase=args.phase, nonce=args.nonce, run_id=int(run_id),
            source_sha=current, parent_sha=parent,
            grandparent_sha=grandparent,
            workflow_tree_sha=reviewed_tree,
            app_id=WORKER_ID if args.phase == "worker-negative" else PUBLISHER_ID,
            installation_id=installation_id)

    run = Trial(client, args.nonce, current, parent, grandparent,
                publisher, evidence=evidence)
    try:
        if protected_token:
            run.token_audience()
        if args.phase == "plan":
            run.gate([])
            result = run.public_receipt("plan", "SOURCE_ONLY_PLAN_NO_WRITES")
            result["execution_authorized"] = False
            result["execution_gates_satisfied"] = bool(args.authorize_live)
        elif args.phase == "prepare-origin":
            # The entire source/nonce quarantine plan and API read check MUST
            # complete before uploading the immutable nonsecret run binding.
            run.gate([])
            binding = make_binding(
                args.nonce, current, parent, grandparent,
                reviewed_tree, int(os.environ.get("GITHUB_RUN_ID", "0")))
            verify_origin(client, binding)
            _write_origin_artifact(binding)
            result = run.public_receipt(
                "prepare-origin", "ORIGINAL_LINEAGE_READY_NO_WRITES")
            result["execution_authorized"] = False
        elif args.phase == "recovery-plan":
            result = run.publisher_recovery_plan()
        elif args.phase == "publisher-seed":
            result = run.publisher_seed()
        elif args.phase == "worker-negative":
            result = run.worker_probe()
        else:
            result = run.publisher_cleanup()
        if evidence is not None:
            success = {
                "publisher-seed": "PUBLISHER_SEED_CONFIRMED",
                "worker-negative": "DENIALS_CONFIRMED",
                "publisher-cleanup": "CLEANUP_ABSENCE_CONFIRMED",
            }
            evidence.decision(success[args.phase])
        print(json.dumps(result, sort_keys=True), flush=True)
        return 0
    except Exception:
        if evidence is not None:
            evidence.decision("STOP_INCOMPLETE")
        raise

def main():
    """Exit via a fixed-text boundary, including unexpected exception types.

    Remote exception strings, parser traceback text, and chained exceptions
    must never reach the credential-bearing Actions job log.
    """
    try:
        return cli()
    except Exception:
        print("W3 STOP: sanitized failure; inspect W3_EVIDENCE", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
