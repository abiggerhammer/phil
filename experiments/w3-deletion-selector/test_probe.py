#!/usr/bin/env python3
"""SOURCE-ONLY deterministic W3 counterexamples; NEVER use live GitHub or tokens."""
import argparse
import base64
import contextlib
import copy
from email.message import Message
import hashlib
from http.client import HTTPResponse
import io
import json
import os
from pathlib import Path
import stat
import subprocess
import sys
import textwrap
import tempfile
import types
import unittest
from unittest import mock
import urllib.error
import urllib.parse

import probe

REF = "refs/heads/hamster/admitted/w3-a1b2c3d4e5f6-canary"
REPO = "owner/w3-delete-selector-probe-example"
TARGET, DEFAULT = "b"*40, "a"*40
SETUP = "c"*40
ACTOR, ID = "owner", 1234
WIN_START, WIN_END = "2026-11-21T11:00:00Z", "2026-11-21T11:30:00Z"


def witness(run_id, kind, *, event="push", created=False, deleted=False,
            ref=REF, source="DEFAULT_V1", ref_type="branch", started="2026-11-21T11:15:00Z"):
    path = ".github/workflows/w3-" + probe.VARIANTS[kind] + ".yml"
    branch_ref = "refs/heads/main" if source == "DEFAULT_V1" else REF
    head_sha = DEFAULT if source == "DEFAULT_V1" else TARGET
    event_ref = (ref.removeprefix("refs/heads/") if event in ("create", "delete")
                 else ref)
    if event in ("create", "delete"):
        created, deleted = None, None
    return {
        "id": run_id, "event": event, "path": path,
        "created_at": started, "head_sha": head_sha,
        "head_branch": branch_ref.removeprefix("refs/heads/"),
        "actor": ACTOR, "status": "completed", "conclusion": "success",
        "workflow_id": 91, "run_number": run_id, "run_attempt": 1,
        "repository_id": ID,
        "url": f"{probe.API_ORIGIN}/repos/{REPO}/actions/runs/{run_id}",
        "html_url": f"https://github.com/{REPO}/actions/runs/{run_id}",
        "log_provenance": {"transport": probe.LOG_TRANSPORT,
                           "status": "ONE_RECORD", "sha256": "0"*64},
        "witness": {
            "schema": "PHIL-W3-SELECTOR-WITNESS-V2",
            "variant": kind, "source_marker": source,
            "event_name": event, "event_ref": event_ref,
            "event_created": created, "event_deleted": deleted,
            "event_ref_type": ref_type if event in ("create", "delete") else None,
            "github_ref": branch_ref, "github_sha": head_sha,
            "run_id": str(run_id), "actor": ACTOR,
            "workflow_ref": f"{REPO}/{path}@{branch_ref}"}}


def snapshot(runs, observed):
    totals = {name: 0 for name in probe.EVENTS}
    for run in runs:
        totals[run["event"]] += 1
    return {
        "schema": "W3-SELECTOR-CENSUS-V3", "repository": REPO,
        "repository_id": ID, "ref": REF, "nonce": "a1b2c3d4e5f6",
        "api_origin": probe.API_ORIGIN, "log_transport": probe.LOG_TRANSPORT,
        "approved_actor": ACTOR, "target_sha": TARGET, "default_sha": DEFAULT,
        "main_before_sha": None, "window_start": WIN_START, "window_end": WIN_END,
        "observed_at": observed, "event_totals": totals, "runs": runs,
        "decision": "READ_ONLY_NOT_CERTIFIED"}


def receipt(phase):
    assert phase in ("create", "delete")
    return {
        "schema": "W3-SELECTOR-LOCAL-MUTATION-V1",
        "action": phase, "decision": "EXACT_STATE_VERIFIED",
        "repo": REPO, "repository_id": ID,
        "ref": REF, "target_sha": TARGET, "default_sha": DEFAULT,
        "api_origin": probe.API_ORIGIN, "approved_actor": ACTOR,
        "prepared_at": "2026-11-21T11:06:00Z",
        "request_started_at": "2026-11-21T11:07:00Z",
        "request_completed_at": "2026-11-21T11:08:00Z",
        "http_status": 201 if phase == "create" else 204,
        "observed_refs": {} if phase == "create" else {REF: TARGET},
        "observed_refs_after": {REF: TARGET} if phase == "create" else {}}


class OfflineTests(unittest.TestCase):
    def classify(self, phase, runs, *, after_time="2026-11-21T12:05:00Z",
                 alter_before=None, alter_after=None, alter_intent=None):
        with tempfile.TemporaryDirectory() as d:
            p, q, m = (Path(d)/x for x in ("before.json", "after.json",
                                          "intent.json"))
            before = snapshot([], "2026-11-21T11:05:00Z")
            after = snapshot(runs, after_time)
            if phase == "main":
                before["default_sha"] = SETUP
                after["main_before_sha"] = SETUP
            if alter_before:
                alter_before(before)
            if alter_after:
                alter_after(after)
            p.write_text(json.dumps(before))
            q.write_text(json.dumps(after))
            if phase != "main":
                intent = receipt(phase)
                if alter_intent:
                    alter_intent(intent)
                m.write_text(json.dumps(intent))
            buf = io.StringIO()
            with contextlib.redirect_stdout(buf):
                probe.classify(argparse.Namespace(
                    phase=phase, before=p, after=q,
                    intent=(m if phase != "main" else None)))
            return json.loads(buf.getvalue())["decision"]

    def test_repo_root_get_uses_exact_github_route_and_authenticated_user(self):
        observed = []
        class Response:
            status = 200
            def __init__(self, data):
                self.data = data
            def read(self, limit):
                return json.dumps(self.data).encode()
            def __enter__(self):
                return self
            def __exit__(self, *args):
                return False
        class Opener:
            def open(self, req, timeout):
                observed.append((req.full_url, req.get_method()))
                return Response(({"full_name": REPO, "default_branch": "main",
                                  "archived": False, "id": ID,
                                  "owner": {"login": ACTOR}}
                                 if req.full_url.endswith("/"+REPO)
                                 else {"login": ACTOR, "id": 34}))
        api = object.__new__(probe.GitHub)
        api.repo, api._token, api._opener = REPO, "offline-fixture", Opener()
        self.assertEqual(api.repo_metadata()["id"], ID)
        self.assertEqual(api.operator(ACTOR), ACTOR)
        self.assertEqual(observed, [
            ("https://api.github.com/repos/" + REPO, "GET"),
            ("https://api.github.com/user", "GET")])
        for method, route in (("POST", ""), ("DELETE", ""), ("POST", "@user"),
                              ("GET", "//attacker"), ("POST", "//attacker"),
                              ("DELETE", "/git/refs/heads/main"),
                              ("POST", "/../../production/git/refs"),
                              ("DELETE", "/git/refs/heads/hamster/staged/w3-a1b2c3d4e5f6-canary")):
            with self.subTest(method=method, route=route):
                with self.assertRaises(probe.Stop):
                    api.request(method, route)
        with self.assertRaises(probe.Stop):
            api.request("POST", "/git/refs", {"ref":"refs/heads/main",
                                              "sha": DEFAULT})

    def test_durable_intent_fsyncs_file_and_parent_directory(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d)/"nonce.create-intent.json"
            seen = []
            original = os.fsync
            def recording_fsync(fd):
                seen.append(stat.S_IFMT(os.fstat(fd).st_mode))
                return original(fd)
            with mock.patch.object(probe.os, "fsync", side_effect=recording_fsync):
                probe.durable_new(p, {"decision": "INTENT_UNKNOWN_AFTER_INTERRUPTION"})
            self.assertEqual(seen, [stat.S_IFREG, stat.S_IFDIR])
            with self.assertRaises(probe.Stop):
                probe.durable_new(p, {"decision": "INVALID_REUSE"})

    def test_directory_fsync_failure_is_fail_closed_and_spends_marker(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d)/"nonce.create-intent.json"
            original = os.fsync
            def fail_directory(fd):
                if stat.S_IFMT(os.fstat(fd).st_mode) == stat.S_IFDIR:
                    raise OSError("injected directory fsync failure")
                return original(fd)
            with mock.patch.object(probe.os, "fsync", side_effect=fail_directory):
                with self.assertRaises(OSError):
                    probe.durable_new(p, {"decision": "UNKNOWN"})
            self.assertTrue(p.exists())
            with self.assertRaises(probe.Stop):
                probe.durable_new(p, {"decision": "ILLEGAL_RETRY"})

    def test_mutation_only_after_durable_intent_in_fake_transport(self):
        with tempfile.TemporaryDirectory() as d:
            seen = []
            class Fake:
                repo = REPO
                def operator(self, expected):
                    return ACTOR
                def admitted(self):
                    return {REF: TARGET}
                def request(self, method, suffix, payload=None):
                    self.assert_marker()
                    seen.append((method, suffix))
                    return 201, {}
                def assert_marker(self):
                    marker = Path(d)/"a1b2c3d4e5f6.create-intent.json"
                    assert marker.exists()
                    assert json.loads(marker.read_text())["decision"] == \
                        "INTENT_UNKNOWN_AFTER_INTERRUPTION"
            fake = Fake()
            preflight = {"repo": REPO, "repository_id": ID,
                         "ref": REF, "target_sha": TARGET,
                         "default_sha": DEFAULT, "observed_refs": {}}
            args = argparse.Namespace(repo=REPO, repo_id=ID, actor=ACTOR,
                                      nonce="a1b2c3d4e5f6",
                                      target_sha=TARGET, default_sha=DEFAULT,
                                      action="create", confirm="CREATE_TEST_ONLY",
                                      state_dir=d)
            with mock.patch.object(probe, "GitHub", return_value=fake), \
                 mock.patch.object(probe, "preflight", return_value=preflight), \
                 contextlib.redirect_stdout(io.StringIO()):
                probe.execute(args)
            self.assertEqual(seen, [("POST", "/git/refs")])
            marker = json.loads((Path(d)/"a1b2c3d4e5f6.create-intent.json").read_text())
            self.assertEqual(marker["decision"], "EXACT_STATE_VERIFIED")
            self.assertEqual(marker["action"], "create")

    @staticmethod
    def http_response(body, framing, status=403):
        wire = (f"HTTP/1.1 {status} Synthetic\r\n".encode() + framing +
                b"\r\n" + body)
        sock = types.SimpleNamespace(makefile=lambda mode: io.BytesIO(wire))
        response = HTTPResponse(sock)
        response.begin()
        return response

    def http_error(self, body, framing=None, headers=None):
        response = None if body is None else self.http_response(
            body, framing if framing is not None else
            f"Content-Length: {len(body)}\r\n".encode())
        error = urllib.error.HTTPError(
            "https://example.invalid", 403, "refusal", headers or Message(), response)
        if response is None:
            error.fp = None  # HTTPError otherwise substitutes an empty BytesIO.
        return error

    def run_refusal(self, directory, outcome, fail_at=None, action="create",
                    poststate=None):
        api = object.__new__(probe.GitHub)
        api.repo, api._token = REPO, "offline-secret"
        api.operator = mock.Mock(return_value=ACTOR)
        api.admitted = (mock.Mock(side_effect=poststate) if isinstance(poststate, Exception)
                        else mock.Mock(return_value={} if poststate is None else poststate))
        api._opener = mock.Mock()
        suffix = "create" if action == "create" else "delete"
        prior = {} if action == "create" else {REF: TARGET}
        marker = Path(directory) / f"a1b2c3d4e5f6.{suffix}-intent.json"
        sidecar = marker.with_suffix(".http-diagnostic.json")

        def open_request(request, timeout):
            self.assertEqual(request.get_method(), "POST" if action == "create" else "DELETE")
            self.assertEqual(json.loads(marker.read_text())["decision"],
                             "INTENT_UNKNOWN_AFTER_INTERRUPTION")
            if isinstance(outcome, Exception):
                raise outcome
            return outcome

        api._opener.open.side_effect = open_request
        args = argparse.Namespace(repo=REPO, repo_id=ID, actor=ACTOR,
                                  nonce="a1b2c3d4e5f6", target_sha=TARGET,
                                  default_sha=DEFAULT, action=action,
                                  confirm=action.upper().replace("-", "_") + "_TEST_ONLY",
                                  state_dir=directory)
        pre = dict(repo=REPO, repository_id=ID, ref=REF, target_sha=TARGET,
                   default_sha=DEFAULT, observed_refs=prior)
        sync = os.fsync
        write_new = probe.durable_new
        injected = False

        def fail_diagnostic_sync(fd):
            nonlocal injected
            is_directory = stat.S_ISDIR(os.fstat(fd).st_mode)
            final = "STOP" in json.loads(marker.read_text())["decision"]
            if (not injected and sidecar.exists() and
                ((fail_at == "final-directory" and is_directory and final) or
                 (fail_at == "directory" and is_directory) or
                 (fail_at == "file" and not is_directory))):
                injected = True
                raise OSError("injected diagnostic sync failure")
            sync(fd)

        def fail_diagnostic_write(path, data):
            if path == sidecar:
                raise OSError("injected diagnostic write failure")
            return write_new(path, data)

        if fail_at == "write":
            context = mock.patch.object(probe, "durable_new", side_effect=fail_diagnostic_write)
        elif fail_at == "replace":
            context = mock.patch.object(probe.os, "replace", side_effect=OSError("offline-secret"))
        elif fail_at:
            context = mock.patch.object(probe.os, "fsync", side_effect=fail_diagnostic_sync)
        else:
            context = contextlib.nullcontext()
        argv = ["probe.py", action]
        for key, value in vars(args).items():
            if key != "action":
                argv.extend(["--" + key.replace("_", "-"), str(value)])
        with mock.patch.object(probe, "GitHub", return_value=api), \
             mock.patch.object(probe, "preflight", return_value=pre), \
             contextlib.redirect_stdout(io.StringIO()) as output, \
             contextlib.redirect_stderr(io.StringIO()) as errors:
            with context, mock.patch.object(sys, "argv", argv), self.assertRaises(SystemExit) as stop:
                probe.cli()
            self.assertEqual(stop.exception.code, 1)
            with self.assertRaisesRegex(probe.Stop, "evidence path occupied"):
                probe.execute(args)
        api._opener.open.assert_called_once()
        intent = json.loads(marker.read_text())
        if fail_at == "replace":
            self.assertEqual(intent["decision"], "INTENT_UNKNOWN_AFTER_INTERRUPTION")
        else:
            self.assertTrue(intent["decision"].startswith("STOP"))
        with self.assertRaisesRegex(probe.Stop, "requires its own successful receipt"):
            probe.load_intent(marker, {}, {}, suffix)
        self.assertTrue(errors.getvalue().startswith("W3 DISPOSABLE SELECTOR STOP: "))
        for field in ("offline-secret", "message_category", "example.invalid"):
            self.assertNotIn(field, output.getvalue() + errors.getvalue())
        return intent, sidecar

    def test_http_refusal_private_diagnostic_binding_and_sanitization(self):
        headers = Message()
        headers["X-GitHub-Request-Id"] = "F00D:AB:123"
        headers["X-RateLimit-Remaining"] = "0"
        headers["Retry-After"] = "offline-secret"
        headers["Authorization"] = "Bearer offline-secret"
        headers["Set-Cookie"] = "offline-secret"
        headers["X-RateLimit-Limit"] = "100"
        headers["X-RateLimit-Limit"] = "200"
        raw = b'{"message":"Forbidden","errors":[{"value":"offline-secret"}]}'
        for action in ("create", "delete", "abort-cleanup"):
            with self.subTest(action=action), tempfile.TemporaryDirectory() as directory:
                error = self.http_error(raw, headers=headers)
                intent, sidecar = self.run_refusal(directory, error, action=action)
                self.assertEqual(intent["http_status"], 403)
                self.assertEqual(intent["diagnostic_capture"], "complete")
                self.assertEqual(stat.S_IMODE(sidecar.stat().st_mode), 0o600)
                serialized = sidecar.read_text()
                self.assertNotIn("offline-secret", serialized)
                self.assertNotIn("example.invalid", serialized)
                record = json.loads(serialized)
                self.assertEqual(record["http_status"], 403)
                self.assertEqual(record["identity"], {
                    "action": action, "repo": REPO, "repository_id": ID, "ref": REF,
                    "target_sha": TARGET, "default_sha": DEFAULT, "api_origin": probe.API_ORIGIN,
                    "nonce": "a1b2c3d4e5f6", "approved_actor": ACTOR,
                    "prepared_at": intent["prepared_at"],
                    "probe_sha256": hashlib.sha256(Path(probe.__file__).read_bytes()).hexdigest(),
                })
                for key in ("request_started_at", "request_completed_at"):
                    self.assertEqual(record[key], intent[key])
                diagnostic = record["diagnostic"]
                self.assertEqual(diagnostic, {
                    "capture": "complete", "body_bytes_inspected": len(raw),
                    "message_category": "forbidden",
                    "headers": {"x-github-request-id": "F00D:AB:123", "x-ratelimit-remaining": "0"},
                })
                digest = hashlib.sha256(
                    json.dumps(diagnostic, sort_keys=True, separators=(",", ":")).encode())
                self.assertEqual(record["diagnostic_sha256"], digest.hexdigest())

    def test_http_diagnostic_incomplete_captures_remain_stop(self):
        for raw, expected in ((b'{"message":', "failed"), (b"{}", "complete"),
                              (b"x" * 9000, "truncated"), (None, "unavailable")):
            with self.subTest(expected=expected), tempfile.TemporaryDirectory() as directory:
                error = self.http_error(raw)
                intent, sidecar = self.run_refusal(directory, error)
                self.assertEqual(intent["diagnostic_capture"], expected)
                record = json.loads(sidecar.read_text())
                self.assertLessEqual(record["diagnostic"]["body_bytes_inspected"],
                                     probe.HTTP_ERROR_LIMIT + 1)
                self.assertEqual(record["diagnostic"]["capture"], expected)
        with tempfile.TemporaryDirectory() as directory:
            intent, sidecar = self.run_refusal(directory, TimeoutError("offline-secret"))
            self.assertIsNone(intent["http_status"])
            self.assertEqual(json.loads(sidecar.read_text())["diagnostic"]["capture"], "unavailable")

    def test_diagnostic_file_and_directory_sync_failure_preserve_consumed_intent(self):
        for stage in ("write", "file", "directory"):
            with self.subTest(stage=stage), tempfile.TemporaryDirectory() as directory:
                error = self.http_error(b'{"message":"Forbidden"}')
                intent, _ = self.run_refusal(directory, error, fail_at=stage)
                self.assertEqual(intent["diagnostic_capture"], "failed")

    def test_actual_http_response_framing_and_capture_boundaries(self):
        exact = b"{}" + b" " * (probe.HTTP_ERROR_LIMIT - 2)
        chunked = b"Transfer-Encoding: chunked\r\n"
        for body, framing, expected, examined in (
            (b"{}", b"Content-Length: 2\r\n", "complete", 2),
            (b"{}", b"Content-Length: 100\r\n", "failed", 2),
            (b"{}", b"Content-Length: 9000\r\n", "failed", 2),
            (b"{}", b"Content-Length: invalid\r\n", "failed", 0),
            (b"{}", b"Content-Length: 2\r\nContent-Length: 100\r\n", "failed", 0),
            (b"2\r\n{}\r\n0\r\n\r\n", chunked, "complete", 2),
            (b"2\r\n{}\r\n", chunked, "failed", 0),
            (b"2\r\n{}\r\n0\r\n", chunked, "failed", 2),
            (b"{}", b"Connection: close\r\n", "complete", 2),
            (exact, b"Content-Length: 4096\r\n", "complete", 4096),
            (exact + b" ", b"Content-Length: 4097\r\n", "truncated", 4097),
        ):
            with self.subTest(framing=framing, size=len(body)), tempfile.TemporaryDirectory() as directory:
                intent, sidecar = self.run_refusal(directory, self.http_error(body, framing))
                self.assertEqual(intent["diagnostic_capture"], expected)
                self.assertEqual(json.loads(sidecar.read_text())["diagnostic"]["body_bytes_inspected"],
                                 examined)

    def test_malformed_ordinary_201_cannot_succeed_with_matching_poststate(self):
        for body in (b'{"message":"offline-secret"', b"\xffoffline-secret", b'{"x":1,"x":2}'):
            with self.subTest(body=body), tempfile.TemporaryDirectory() as directory:
                response = self.http_response(
                    body, f"Content-Length: {len(body)}\r\n".encode(), status=201)
                intent, sidecar = self.run_refusal(directory, response, poststate={REF: TARGET})
                self.assertEqual(intent["http_status"], 201)
                self.assertEqual(intent["observed_refs_after"], {REF: TARGET})
                self.assertEqual(intent["diagnostic_capture"], "failed")
                record = json.loads(sidecar.read_text())
                self.assertEqual(record["http_status"], 201)
                self.assertEqual(record["request_completed_at"], intent["request_completed_at"])
                self.assertEqual(record["diagnostic"]["failure_stage"], "ordinary-response-processing")
                self.assertNotIn("offline-secret", sidecar.read_text())

    def test_diagnostic_read_and_duplicate_json_fail_closed(self):
        for body in (b'{"message":"Forbidden","message":"offline-secret"}', None):
            with self.subTest(body=body), tempfile.TemporaryDirectory() as directory:
                error = self.http_error(body if body is not None else b"{}")
                if body is None:
                    error.fp.read = mock.Mock(side_effect=OSError("offline-secret"))
                intent, sidecar = self.run_refusal(directory, error)
                self.assertEqual(intent["diagnostic_capture"], "failed")
                self.assertNotIn("offline-secret", sidecar.read_text())

    def test_diagnostic_survives_poststate_and_final_stop_persistence_failures(self):
        for failure in ("poststate", "replace", "final-directory"):
            with self.subTest(failure=failure), tempfile.TemporaryDirectory() as directory:
                kwargs = ({"poststate": OSError("offline-secret")} if failure == "poststate"
                          else {"fail_at": failure})
                _, sidecar = self.run_refusal(directory, self.http_error(b"{}"), **kwargs)
                record = json.loads(sidecar.read_text())
                self.assertEqual(record["http_status"], 403)
                self.assertEqual(record["diagnostic"]["capture"], "complete")

    def test_synthetic_historical_403_stop_receipt_remains_rejected(self):
        with self.assertRaisesRegex(probe.Stop, "requires its own successful receipt"):
            self.classify("create", [], alter_intent=lambda intent: intent.update(
                decision="STOP_UNEXPECTED_OR_AMBIGUOUS_POSTSTATE",
                http_status=403, observed_refs_after={}))

    def test_abort_cleanup_never_relabels_phase_c(self):
        with tempfile.TemporaryDirectory() as d:
            state = {"repo": REPO, "repository_id": ID, "ref": REF,
                     "target_sha": TARGET, "default_sha": DEFAULT,
                     "observed_refs": {REF: TARGET}}
            class Fake:
                repo = REPO
                def operator(self, expected):
                    return ACTOR
                def admitted(self):
                    return {}
                def request(self, method, suffix, payload=None):
                    return 204, None
            args = argparse.Namespace(repo=REPO, repo_id=ID, actor=ACTOR,
                                      nonce="a1b2c3d4e5f6", target_sha=TARGET,
                                      default_sha=DEFAULT, action="abort-cleanup",
                                      confirm="ABORT_CLEANUP_TEST_ONLY", state_dir=d)
            with mock.patch.object(probe, "GitHub", return_value=Fake()), \
                 mock.patch.object(probe, "preflight", return_value=state), \
                 contextlib.redirect_stdout(io.StringIO()):
                probe.execute(args)
            marker = json.loads((Path(d)/"a1b2c3d4e5f6.delete-intent.json").read_text())
            self.assertEqual(marker["decision"], "ABORT_CLEANUP_STATE_VERIFIED")
            for modify in (lambda d: d.update(action="abort-cleanup"),
                           lambda d: d.update(decision="ABORT_CLEANUP_STATE_VERIFIED")):
                with self.assertRaises(probe.Stop):
                    self.classify("delete", [
                        witness(1, "UNFILTERED", deleted=True),
                        witness(2, "W3_ONLY", deleted=True)],
                        alter_intent=modify)

    def test_exact_fixture_equivalence(self):
        root = Path(__file__).resolve().parent/"fixtures"
        for flavor in probe.VARIANTS.values():
            rel = Path(".github/workflows")/("w3-"+flavor+".yml")
            target = (root/"target_v1"/rel).read_text()
            default = (root/"default_v1"/rel).read_text()
            self.assertEqual(target.replace("TARGET_V1", "DEFAULT_V1"), default)
            for source in (target, default):
                self.assertIn("permissions: {}", source)
                self.assertNotIn("uses:", source)
                self.assertNotIn("actions/checkout", source)
                self.assertIn("W3_WITNESS_JSON:", source)
                self.assertIn('event_boolean("EVENT_DELETED_JSON")', source)

    def test_production_target_denied(self):
        for repo in ("abiggerhammer/phil", "owner/production", "wrong-format"):
            with self.assertRaises(probe.Stop):
                probe.verify_repo_name(repo)

    def test_spent_nonce_denied(self):
        with self.assertRaises(probe.Stop):
            probe.ref_for("d948536ad68f")

    def test_deletion_genuine_controls(self):
        self.assertEqual(self.classify("delete", [
            witness(1, "UNFILTERED", deleted=True),
            witness(2, "W3_ONLY", deleted=True, source="TARGET_V1")]),
            "SUPPORTS_MODEL_BOUNDED_NOT_CERTIFIED")

    def test_legitimate_deletion_auxiliary_does_not_count_as_push(self):
        self.assertEqual(self.classify("delete", [
            witness(1, "UNFILTERED", deleted=True),
            witness(2, "W3_ONLY", deleted=True, source="TARGET_V1"),
            witness(3, "UNFILTERED", event="delete")]),
            "SUPPORTS_MODEL_BOUNDED_NOT_CERTIFIED")
        self.assertEqual(self.classify("delete", [
            witness(3, "UNFILTERED", event="delete")]),
            "INCONCLUSIVE_MISSING_POSITIVE_WITNESS")

    def test_same_name_tag_delete_is_unexpected(self):
        self.assertEqual(self.classify("delete", [
            witness(1, "UNFILTERED", deleted=True),
            witness(2, "W3_ONLY", deleted=True, source="TARGET_V1"),
            witness(3, "UNFILTERED", event="delete", ref_type="tag")]),
            "STOP_UNRELATED_OR_AMBIGUOUS_TRAFFIC")

    def test_main_control(self):
        self.assertEqual(self.classify("main", [
            witness(1, "UNFILTERED", ref="refs/heads/main"),
            witness(2, "MAIN_ONLY", ref="refs/heads/main"),
            witness(3, "IGNORE_PAIR", ref="refs/heads/main")]),
            "SUPPORTS_MODEL_BOUNDED_NOT_CERTIFIED")

    def test_create_control_and_expected_auxiliary_create(self):
        controls = [witness(1, "UNFILTERED", created=True),
                    witness(2, "W3_ONLY", created=True, source="TARGET_V1")]
        for source, ref_type, expected in (
            ("TARGET_V1", "branch", "SUPPORTS_MODEL_BOUNDED_NOT_CERTIFIED"),
            ("DEFAULT_V1", "branch", "STOP_UNRELATED_OR_AMBIGUOUS_TRAFFIC"),
            ("TARGET_V1", "tag", "STOP_UNRELATED_OR_AMBIGUOUS_TRAFFIC"),
        ):
            with self.subTest(source=source, ref_type=ref_type):
                auxiliary = witness(3, "UNFILTERED", event="create",
                                    source=source, ref_type=ref_type)
                self.assertEqual(self.classify("create", controls + [auxiliary]), expected)

    def test_forbidden_branch_controls_are_counterexamples(self):
        for phase, forbidden in (("delete", "MAIN_ONLY"),
                                 ("delete", "IGNORE_PAIR"),
                                 ("create", "MAIN_ONLY"),
                                 ("main", "W3_ONLY")):
            with self.subTest(phase=phase, kind=forbidden):
                if phase == "main":
                    positives = [witness(1, "UNFILTERED", ref="refs/heads/main"),
                                 witness(2, "MAIN_ONLY", ref="refs/heads/main"),
                                 witness(3, "IGNORE_PAIR", ref="refs/heads/main")]
                    forbidden_run = witness(4, forbidden, ref="refs/heads/main")
                else:
                    positives = [witness(1, "UNFILTERED",
                                         created=phase=="create",
                                         deleted=phase=="delete"),
                                 witness(2, "W3_ONLY",
                                         created=phase=="create",
                                         deleted=phase=="delete")]
                    forbidden_run = witness(4, forbidden,
                                             created=phase=="create",
                                             deleted=phase=="delete")
                self.assertEqual(self.classify(phase, positives+[forbidden_run]),
                                 "COUNTEREXAMPLE_STOP")

    def test_phase_cannot_use_witnesses_from_before_its_request(self):
        for phase in ("create", "delete"):
            with self.subTest(phase=phase):
                runs = [
                    witness(1, "UNFILTERED", created=phase == "create",
                            deleted=phase == "delete",
                            started="2026-11-21T11:06:59Z"),
                    witness(2, "W3_ONLY", created=phase == "create",
                            deleted=phase == "delete", source="TARGET_V1"),
                ]
                self.assertEqual(self.classify(phase, runs),
                                 "STOP_UNRELATED_OR_AMBIGUOUS_TRAFFIC")

    def test_receipt_requires_exact_pre_mutation_ref_state(self):
        for phase, wrong_refs in (("create", {REF: TARGET}), ("delete", {}),
                                  ("delete", {REF: DEFAULT})):
            with self.subTest(phase=phase, wrong_refs=wrong_refs):
                with self.assertRaisesRegex(probe.Stop, "receipt not exact"):
                    self.classify(phase, [], alter_intent=lambda doc: doc.update(
                        observed_refs=wrong_refs))

    def test_delayed_create_cannot_count_as_delete(self):
        self.assertEqual(self.classify("delete", [
            witness(1, "UNFILTERED", deleted=True),
            witness(2, "W3_ONLY", created=True)]),
            "STOP_UNRELATED_OR_AMBIGUOUS_TRAFFIC")

    def test_string_false_not_boolean(self):
        x = witness(2, "W3_ONLY", deleted=True)
        x["witness"]["event_deleted"] = "false"
        self.assertEqual(self.classify("delete", [
            witness(1, "UNFILTERED", deleted=True), x]),
            "STOP_UNRELATED_OR_AMBIGUOUS_TRAFFIC")

    def test_missing_positive_is_inconclusive_not_support(self):
        self.assertEqual(self.classify("delete", [
            witness(1, "UNFILTERED", deleted=True)]),
            "INCONCLUSIVE_MISSING_POSITIVE_WITNESS")

    def test_surprising_create_delete_push_are_counted_and_stop(self):
        positives = [witness(1, "UNFILTERED", deleted=True),
                     witness(2, "W3_ONLY", deleted=True)]
        for hostile in (
            witness(3, "UNFILTERED", event="create"),
            witness(3, "UNFILTERED", event="delete", ref="refs/heads/other"),
            witness(3, "UNFILTERED", deleted=True, ref="refs/heads/other"),
            witness(3, "UNFILTERED", deleted=True)):
            with self.subTest(event=hostile["event"],
                              ref=hostile["witness"]["event_ref"]):
                # Duplicate push in a single kind is not silent evidence.
                self.assertEqual(
                    self.classify("delete", positives+[hostile]),
                    "STOP_UNRELATED_OR_AMBIGUOUS_TRAFFIC")

    def test_snapshot_identity_source_and_log_attacks_stop(self):
        base = [witness(1, "UNFILTERED", deleted=True),
                witness(2, "W3_ONLY", deleted=True)]
        tamper = (
            lambda d: d.update(repository_id=9999),
            lambda d: d.update(approved_actor="attacker"),
            lambda d: d.update(api_origin="https://github.example"),
            lambda d: d.update(target_sha="f"*40),
            lambda d: d["runs"][0].update(actor="attacker"),
            lambda d: d["runs"][0].update(head_sha="f"*40),
            lambda d: d["runs"][0].update(repository_id=9999),
            lambda d: d["runs"][0].update(created_at="2026-11-21T14:00:00Z"),
            lambda d: d["runs"][0].update(run_attempt=2),
            lambda d: d["runs"][0].update(url="https://github.example/forged"),
            lambda d: d["runs"][0]["log_provenance"].update(
                status="UNAVAILABLE"))
        for n, mutate in enumerate(tamper):
            with self.subTest(tamper=n):
                changes = copy.deepcopy(base)
                def alter(doc):
                    mutate(doc)
                try:
                    decision = self.classify("delete", changes, alter_after=alter)
                except probe.Stop:
                    pass
                else:
                    self.assertNotEqual(decision, "SUPPORTS_MODEL_BOUNDED_NOT_CERTIFIED")
        witness_tampers = (
            ("github_sha", "f"*40), ("run_id", "42"),
            ("event_ref", "refs/heads/other"), ("actor", "attacker"),
            ("github_ref", "refs/heads/other"),
            ("workflow_ref", "attacker/repo/.github/workflows/test.yml@main"),
            ("source_marker", "TARGET_V1"), ("event_deleted", "true"))
        for key, value in witness_tampers:
            with self.subTest(field=key):
                changes = copy.deepcopy(base)
                changes[1]["witness"][key] = value
                self.assertEqual(self.classify("delete", changes),
                                 "STOP_UNRELATED_OR_AMBIGUOUS_TRAFFIC")

    def test_early_after_is_stop(self):
        with self.assertRaises(probe.Stop):
            self.classify("delete", [], after_time="2026-11-21T11:31:00Z")

    def test_receipt_time_and_identity_binding_fail_closed(self):
        for edit in (
            lambda x: x.update(request_started_at="2026-11-21T10:59:00Z"),
            lambda x: x.update(request_completed_at="2026-11-21T11:35:00Z"),
            lambda x: x.update(ref="refs/heads/other"),
            lambda x: x.update(approved_actor="attacker"),
            lambda x: x.update(http_status=500)):
            with self.assertRaises(probe.Stop):
                self.classify("delete", [
                    witness(1, "UNFILTERED", deleted=True),
                    witness(2, "W3_ONLY", deleted=True)],
                    alter_intent=edit)

    def test_before_snapshot_must_have_clean_event_window(self):
        with self.assertRaises(probe.Stop):
            self.classify("delete", [
                witness(2, "UNFILTERED", deleted=True),
                witness(3, "W3_ONLY", deleted=True)],
                alter_before=lambda d: (
                    d["runs"].append(witness(1, "UNFILTERED", deleted=True)),
                    d["event_totals"].update(push=1)))

    def test_phase_a_capture_main_transition_through_real_request_builder(self):
        tree = "d"*40
        control_records = {
            rid: witness(rid, kind, ref="refs/heads/main")
            for rid, kind in enumerate(("UNFILTERED", "MAIN_ONLY", "IGNORE_PAIR"), 1)
        }
        requests = []

        def open_request(request, timeout):
            self.assertEqual(request.get_method(), "GET")
            url = urllib.parse.urlsplit(request.full_url)
            self.assertEqual(url.netloc, "api.github.com")
            requests.append((url.path, urllib.parse.parse_qs(url.query)))
            path, query = requests[-1]
            if path == "/user":
                data = {"login": ACTOR, "id": 12}
            else:
                self.assertTrue(path.startswith("/repos/" + REPO))
                path = path.removeprefix("/repos/" + REPO)
                if not path:
                    data = {"id": ID, "full_name": REPO, "default_branch": "main",
                            "archived": False, "owner": {"login": ACTOR}}
                elif path == "/git/ref/heads/main":
                    data = {"ref": "refs/heads/main", "object": {"sha": main}}
                elif path.startswith("/git/commits/"):
                    revision = path.rsplit("/", 1)[-1]
                    data = {"sha": revision, "tree": {
                                "sha": changed_tree if revision == DEFAULT else tree},
                            "parents": [{"sha": SETUP if revision == DEFAULT else TARGET}]}
                elif path.startswith("/contents/"):
                    revision = query["ref"][0]
                    self.assertIn(revision, (TARGET, main))
                    flavor = "target_v1" if revision == TARGET else "default_v1"
                    fixture = probe.ROOT / "fixtures" / flavor / path.removeprefix("/contents/")
                    data = {"encoding": "base64", "content":
                            base64.b64encode(fixture.read_bytes()).decode()}
                else:
                    self.assertEqual(path, "/actions/runs")
                    self.assertEqual(query["created"], [f"{WIN_START}..{WIN_END}"])
                    self.assertEqual(query["per_page"], ["100"])
                    self.assertEqual(query["page"], ["1"])
                    rows = []
                    if main == DEFAULT and query["event"] == ["push"]:
                        for run in control_records.values():
                            rows.append({**run, "repository": {"id": ID},
                                         "head_repository": {"id": ID},
                                         "actor": {"login": ACTOR}})
                    data = {"total_count": len(rows), "workflow_runs": rows}
            response = mock.MagicMock()
            response.__enter__.return_value.status = 200
            response.__enter__.return_value.read.return_value = json.dumps(data).encode()
            return response

        api = object.__new__(probe.GitHub)
        api.repo, api._token = REPO, "offline-fixture"
        api._opener = types.SimpleNamespace(open=open_request)
        api._log_env = {"GH_HOST": "github.com", "GH_TOKEN": "offline-fixture"}

        def fake_log(argv, **kwargs):
            run_id = int(argv[3])
            return types.SimpleNamespace(
                returncode=0, stdout=probe.WITNESS_PREFIX +
                json.dumps(control_records[run_id]["witness"]) + "\n")

        with tempfile.TemporaryDirectory() as directory, contextlib.redirect_stdout(io.StringIO()):
            before, after = (Path(directory) / filename for filename in ("before", "after"))
            args = argparse.Namespace(repo=REPO, repo_id=ID, actor=ACTOR,
                                      nonce="a1b2c3d4e5f6", target_sha=TARGET,
                                      default_sha=SETUP, main_before_sha=None,
                                      window_start=WIN_START, window_end=WIN_END, out=before)
            with mock.patch.object(probe, "GitHub", return_value=api), \
                 mock.patch.object(probe.dt, "datetime", wraps=probe.dt.datetime) as clock, \
                 mock.patch.object(probe.subprocess, "run", side_effect=fake_log):
                main, changed_tree = SETUP, tree
                clock.now.return_value = probe.utc("2026-11-21T11:05:00Z")
                probe.snapshot(args)
                main = DEFAULT
                args.default_sha, args.main_before_sha, args.out = DEFAULT, SETUP, after
                clock.now.return_value = probe.utc("2026-11-21T12:05:00Z")
                changed_tree = "e"*40
                with self.assertRaisesRegex(probe.Stop, "exact empty child"):
                    probe.snapshot(args)
                changed_tree = tree
                probe.snapshot(args)
                phases = argparse.Namespace(phase="main", before=before, after=after, intent=None)
                with contextlib.redirect_stdout(io.StringIO()) as result:
                    probe.classify(phases)
                self.assertEqual(json.loads(result.getvalue())["decision"],
                                 "SUPPORTS_MODEL_BOUNDED_NOT_CERTIFIED")
        self.assertEqual(sum(path.endswith("/actions/runs") for path, _ in requests), 6)
        for revision in (SETUP, DEFAULT):
            self.assertEqual(sum(path.startswith(f"/repos/{REPO}/contents/") and
                                 query == {"ref": [revision]} for path, query in requests),
                             4 if revision == SETUP else 8)

    def test_unapproved_census_query_rejected_before_transport(self):
        api = object.__new__(probe.GitHub)
        api.repo, api._token, api._opener = REPO, "offline-fixture", mock.Mock()
        for suffix in ("/actions/../runs", "/actions/runs?event=push",
                       "/actions/runs?event=push&event=delete"):
            with self.subTest(suffix=suffix), self.assertRaises(probe.Stop):
                api.must_get(suffix)
        api._opener.open.assert_not_called()

    def test_pagination_total_drift_and_short_page_stop(self):
        class Fake:
            repo = REPO
            def __init__(self, mode):
                self.mode = mode
            def repo_metadata(self):
                return {"id": ID}
            def operator(self, expected):
                return ACTOR
            def main(self):
                return DEFAULT
            def verify_fixture(self, default, target):
                return None
            def must_get(self, suffix):
                q = urllib.parse.parse_qs(urllib.parse.urlsplit(suffix).query)
                page = int(q["page"][0])
                event = q["event"][0]
                if event != "push":
                    return {"total_count": 0, "workflow_runs": []}
                if page == 1:
                    return {"total_count": 101,
                            "workflow_runs": [self.run(i) for i in range(1, 101)]}
                return {"total_count": 102 if self.mode == "drift" else 101,
                        "workflow_runs": []}
            def run(self, i):
                x = witness(i, "UNFILTERED")
                return {
                    **{k: v for k, v in x.items() if
                       k not in ("witness", "log_provenance", "repository_id",
                                 "actor")},
                    "repository": {"id": ID}, "head_repository": {"id": ID},
                    "actor": {"login": ACTOR}}
        for case in ("drift", "short"):
            with tempfile.TemporaryDirectory() as d:
                args = argparse.Namespace(repo=REPO, repo_id=ID, actor=ACTOR,
                                          nonce="a1b2c3d4e5f6", target_sha=TARGET,
                                          default_sha=DEFAULT,
                                          window_start=WIN_START,
                                          window_end=WIN_END,
                                          out=str(Path(d)/"snapshot.json"))
                with mock.patch.object(probe, "GitHub", return_value=Fake(case)):
                    with self.subTest(case=case), self.assertRaises(probe.Stop):
                        probe.snapshot(args)
                self.assertFalse(Path(args.out).exists())

    def test_explicit_log_binding_and_no_implicit_host_or_token(self):
        calls = []
        def fake_run(argv, **kwargs):
            calls.append((argv, kwargs))
            line = probe.WITNESS_PREFIX + json.dumps(
                witness(7, "UNFILTERED")["witness"])
            return types.SimpleNamespace(returncode=0, stdout=line+"\n")
        api = types.SimpleNamespace(repo=REPO, _log_env={
            "GH_HOST": "github.com", "GH_TOKEN": "test-only",
        })
        with mock.patch.object(probe.subprocess, "run", side_effect=fake_run):
            output, evidence = probe.log_witness(api, {"id": 7, "run_attempt": 1})
        self.assertEqual(output["run_id"], "7")
        self.assertEqual(evidence["status"], "ONE_RECORD")
        argv, kwargs = calls[0]
        self.assertEqual(argv[argv.index("--repo")+1], REPO)
        self.assertEqual(kwargs["env"]["GH_HOST"], "github.com")
        self.assertEqual(kwargs["env"]["GH_TOKEN"], "test-only")
        with self.assertRaises(probe.Stop):
            probe.log_witness(api, {"id": 7, "run_attempt": 2})


    def test_runner_script_echo_and_actual_emission(self):
        fixture = (probe.ROOT / "fixtures/default_v1/.github/workflows/w3-unfiltered.yml")
        script = textwrap.dedent(fixture.read_text().split("run: |\n", 1)[1])
        body = script.split("python3 - <<'PY'\n", 1)[1].rsplit("\nPY", 1)[0]
        env = {
            "WITNESS_KIND": "UNFILTERED", "SOURCE_MARKER": "DEFAULT_V1",
            "EVENT_NAME": "delete", "EVENT_REF": REF.removeprefix("refs/heads/"),
            "EVENT_CREATED_JSON": "null", "EVENT_DELETED_JSON": "null",
            "GITHUB_EVENT_REF": "refs/heads/main", "GITHUB_EVENT_SHA": DEFAULT,
            "GITHUB_RUN_IDENTIFIER": "7", "GITHUB_EVENT_ACTOR": ACTOR,
            "WORKFLOW_SOURCE_REF": f"{REPO}/.github/workflows/w3-unfiltered.yml@refs/heads/main",
        }
        api = types.SimpleNamespace(repo=REPO, _log_env={})
        prefix = "witness\tEmit strictly typed event metadata\t2026-11-21T11:15:00.123Z "
        for ref_type in ("branch", "tag"):
            with self.subTest(ref_type=ref_type):
                output = subprocess.run(
                    [sys.executable, "-B", "-c", body], text=True, capture_output=True,
                    check=True, env={**env, "EVENT_REF_TYPE_JSON": json.dumps(ref_type)},
                ).stdout
                runner_log = "".join(prefix + line + "\n" for line in
                                     (script + output).splitlines())
                self.assertEqual(runner_log.count(probe.WITNESS_PREFIX), 2)
                for extra in ("", output.strip(), probe.WITNESS_PREFIX + "malformed"):
                    stdout = runner_log + (prefix + extra + "\n" if extra else "")
                    with mock.patch.object(probe.subprocess, "run", return_value=
                                           types.SimpleNamespace(returncode=0, stdout=stdout)):
                        record, details = probe.log_witness(api, {"id": 7, "run_attempt": 1})
                    if extra:
                        self.assertIsNone(record)
                        self.assertEqual(details["status"], "AMBIGUOUS_OR_MISSING")
                    else:
                        self.assertEqual(record, witness(7, "UNFILTERED", event="delete",
                                                         ref_type=ref_type)["witness"])
                        self.assertEqual(details["status"], "ONE_RECORD")

    def test_log_duplicate_or_unparsable_records_never_count(self):
        good = probe.WITNESS_PREFIX + json.dumps(
            witness(7, "UNFILTERED")["witness"])
        for body in (good+"\n"+good+"\n",
                     good+"\n"+probe.WITNESS_PREFIX+"garbage\n",
                     "no marker\n"):
            with self.subTest(length=len(body)):
                fake = types.SimpleNamespace(
                    returncode=0, stdout=body)
                api = types.SimpleNamespace(
                    repo=REPO, _log_env={"GH_HOST": "github.com",
                                        "GH_TOKEN": "test-only"})
                with mock.patch.object(probe.subprocess, "run",
                                       return_value=fake):
                    doc, source = probe.log_witness(
                        api, {"id": 7, "run_attempt": 1})
                self.assertIsNone(doc)
                self.assertEqual(source["status"], "AMBIGUOUS_OR_MISSING")

    def test_non_github_host_context_refuses_before_token_lookup(self):
        with mock.patch.dict(probe.os.environ, {"GH_HOST": "github.enterprise.test"}):
            with mock.patch.object(probe.subprocess, "run") as run:
                with self.assertRaises(probe.Stop):
                    probe.GitHub(REPO)
                run.assert_not_called()


if __name__ == "__main__":
    unittest.main()
