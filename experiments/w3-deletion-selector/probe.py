#!/usr/bin/env python3
"""Disposable-repository W3 selector experiment. SOURCE-ONLY; independent review required."""
from __future__ import annotations
import argparse
import base64
from dataclasses import dataclass
import datetime as dt
import hashlib
from http.client import HTTPResponse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import urllib.error
import urllib.parse
import urllib.request

ROOT = Path(__file__).resolve().parent
REPO_RE = re.compile(r"[A-Za-z0-9_.-]+/w3-delete-selector-probe-[A-Za-z0-9_.-]+\Z")
HEX = re.compile(r"[0-9a-f]{40}\Z")
NONCE = re.compile(r"[0-9a-f]{12}\Z")
EVENTS = ("push", "create", "delete")
VARIANTS = {"UNFILTERED": "unfiltered", "MAIN_ONLY": "main-only",
            "W3_ONLY": "w3-only", "IGNORE_PAIR": "ignore-pair"}
WITNESS_PREFIX = "W3_WITNESS_JSON:"
MAX_RUNS = 200
API_ORIGIN = "https://api.github.com"
LOG_TRANSPORT = "gh run view (GH_HOST=github.com, pinned GH_TOKEN)"
UTC = dt.timezone.utc

class Stop(RuntimeError):
    pass

def check(condition, reason):
    if not condition:
        raise Stop(reason)

def utc(text):
    check(isinstance(text, str) and text.endswith("Z"), "UTC Z timestamp required")
    try:
        value = dt.datetime.fromisoformat(text.replace("Z", "+00:00"))
    except ValueError as exc:
        raise Stop("invalid UTC timestamp") from exc
    check(value.utcoffset() == dt.timedelta(0), "non-UTC time")
    return value

def iso(value):
    return value.astimezone(UTC).isoformat(timespec="seconds").replace("+00:00", "Z")

def ref_for(nonce):
    check(bool(NONCE.fullmatch(nonce)) and nonce != "d948536ad68f",
          "nonce invalid or previously spent in Phil")
    return f"refs/heads/hamster/admitted/w3-{nonce}-canary"

def verify_repo_name(repo):
    check(isinstance(repo, str) and bool(REPO_RE.fullmatch(repo)) and
          repo.lower() != "abiggerhammer/phil",
          "STOP: only a separately owner-approved disposable probe repo is allowed")
    return repo

def sha(value):
    check(isinstance(value, str) and bool(HEX.fullmatch(value)), "invalid SHA")
    return value

def strict_json(raw):
    def pairs(items):
        result = {}
        for k, v in items:
            check(k not in result, "duplicate JSON property")
            result[k] = v
        return result
    return json.loads(raw, object_pairs_hook=pairs)

def durable_new(path, obj):
    path = Path(path)
    check(path.parent.is_dir() and not path.parent.is_symlink() and
          not path.exists() and not path.is_symlink(), "evidence path occupied or missing parent")
    data = (json.dumps(obj, sort_keys=True, separators=(",", ":")) + "\n").encode()
    flags = os.O_CREAT | os.O_EXCL | os.O_WRONLY
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    # Bind the marker creation and directory fsync to the SAME verified
    # directory handle. An fsynced file alone does not make its name durable.
    dir_flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0)
    if hasattr(os, "O_NOFOLLOW"):
        dir_flags |= os.O_NOFOLLOW
    dir_fd = os.open(path.parent, dir_flags)
    try:
        with os.fdopen(os.open(path.name, flags, 0o600, dir_fd=dir_fd), "wb") as fd:
            fd.write(data)
            fd.flush()
            os.fsync(fd.fileno())
        os.fsync(dir_fd)
    finally:
        os.close(dir_fd)
    return path

def durable_replace(path, obj):
    path = Path(path)
    tmp = path.with_name(path.name + ".reconcile-tmp")
    durable_new(tmp, obj)
    os.replace(tmp, path)
    fd = os.open(path.parent, os.O_RDONLY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)

HTTP_ERROR_LIMIT = 4096
DIAGNOSTIC_HEADERS = {
    "X-GitHub-Request-Id": r"[0-9A-Fa-f]{1,16}(?::[0-9A-Fa-f]{1,16}){2,7}",
    "X-RateLimit-Limit": r"[0-9]{1,16}",
    "X-RateLimit-Remaining": r"[0-9]{1,16}",
    "X-RateLimit-Reset": r"[0-9]{1,16}",
    "Retry-After": r"[0-9]{1,16}",
}
ERROR_MESSAGES = {
    "Forbidden": "forbidden",
    "Not Found": "not-found",
    "Validation Failed": "validation-failed",
    "Resource not accessible by personal access token": "pat-resource-inaccessible",
    "Resource not accessible by integration": "integration-resource-inaccessible",
}


@dataclass(frozen=True)
class HttpErrorDiagnostic:
    payload: dict


class ChunkTrailerObserver:
    """Observe the final line because HTTPResponse tolerates EOF in trailers."""

    def __init__(self, stream):
        self.stream = stream
        self.last_line = None

    def readline(self, limit):
        self.last_line = self.stream.readline(limit)
        return self.last_line

    def read(self, limit):
        return self.stream.read(limit)

    def close(self):
        self.stream.close()


def bounded_body(response, limit):
    """Return bounded body bytes and whether HTTP framing finished."""
    if not isinstance(response, HTTPResponse):
        return response.read(limit), False
    lengths = response.headers.get_all("Content-Length", [])
    encodings = response.headers.get_all("Transfer-Encoding", [])
    if (len(lengths) > 1 or (lengths and not re.fullmatch(r"[0-9]+", lengths[0])) or
        (encodings and (lengths or len(encodings) != 1 or not response.chunked))):
        return b"", False
    if response.chunked:
        observer = ChunkTrailerObserver(response.fp)
        response.fp = observer
        try:
            body = response.read(limit)
            return body, response.isclosed() and observer.last_line == b"\r\n"
        finally:
            if response.fp is observer:
                response.fp = observer.stream
    if response.length is not None:
        body = response.read(limit)
        return body, response.length == 0
    # Close-delimited bodies have no declared size. Require the HTTP reader
    # to observe EOF while staying within the same cumulative byte budget.
    body = bytearray()
    while len(body) < limit and not response.isclosed():
        body.extend(response.read(limit - len(body)))
    return bytes(body), response.will_close and response.isclosed()


def capture_http_error(error, token):
    """Read bounded error evidence without retaining server-supplied prose."""
    evidence = {"capture": "unavailable", "headers": {}, "body_bytes_inspected": 0}
    try:
        if error.headers is not None:
            for name, grammar in DIAGNOSTIC_HEADERS.items():
                values = error.headers.get_all(name, [])
                if (len(values) == 1 and len(values[0]) <= 135 and
                    not (token and token in values[0]) and re.fullmatch(grammar, values[0])):
                    evidence["headers"][name.lower()] = values[0]
        if error.fp is None:
            return evidence
        raw, complete = bounded_body(error.fp, HTTP_ERROR_LIMIT + 1)
        evidence["body_bytes_inspected"] = len(raw)
        if len(raw) > HTTP_ERROR_LIMIT:
            evidence["capture"] = "truncated"
        elif not complete:
            evidence["capture"] = "failed"
        elif raw:
            doc = strict_json(raw.decode("utf-8"))
            check(isinstance(doc, dict), "invalid error response shape")
            message = doc.get("message")
            evidence["message_category"] = (
                ERROR_MESSAGES.get(message, "other") if isinstance(message, str) else "other")
            evidence["capture"] = "complete"
    except Exception:
        evidence["capture"] = "failed"
    return evidence


def preserve_diagnostic(marker, intent, diagnostic, nonce, probe_digest):
    capture = diagnostic["capture"]
    evidence = {
        "schema": "W3-SELECTOR-HTTP-DIAGNOSTIC-V1",
        "identity": {
            **{key: intent[key] for key in (
                "action", "repo", "repository_id", "ref", "target_sha", "default_sha",
                "api_origin", "approved_actor", "prepared_at")},
            "nonce": nonce,
            "probe_sha256": probe_digest,
        },
        "request_started_at": intent["request_started_at"],
        "request_completed_at": intent["request_completed_at"],
        "http_status": intent["http_status"],
        "diagnostic": diagnostic,
        "diagnostic_sha256": hashlib.sha256(
            json.dumps(diagnostic, sort_keys=True, separators=(",", ":")).encode()
        ).hexdigest(),
    }
    path = marker.with_suffix(".http-diagnostic.json")
    try:
        durable_new(path, evidence)
    except (OSError, Stop):
        intent["diagnostic_capture"] = "failed"
        raise Stop("HTTP diagnostic preservation failed; intent remains consumed") from None
    intent["diagnostic_capture"] = capture


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args, **kwargs):
        return None

class GitHub:

    def __init__(self, repo):
        self.repo = verify_repo_name(repo)
        check(os.getenv("GITHUB_ACTIONS", "").lower() != "true",
              "forbidden inside GitHub Actions")
        check(os.getenv("GH_HOST", "github.com").lower() == "github.com",
              "GH_HOST must be github.com")
        check(not os.getenv("GH_ENTERPRISE_TOKEN") and
              not os.getenv("GITHUB_ENTERPRISE_TOKEN"),
              "enterprise token context forbidden")
        cp = subprocess.run(["gh", "auth", "token", "--hostname", "github.com"],
                            text=True, capture_output=True, timeout=15, check=False)
        check(cp.returncode == 0 and bool(cp.stdout.strip()) and
              "\n" not in cp.stdout.strip(), "GitHub.com CLI local auth unavailable")
        self._token = cp.stdout.strip()
        self._opener = urllib.request.build_opener(NoRedirect())
        # gh log retrieval and direct REST MUST use the same GitHub.com bearer,
        # never an implicit alternate GH_HOST/GITHUB_TOKEN credential.
        self._log_env = dict(os.environ)
        for name in ("GITHUB_TOKEN", "GH_ENTERPRISE_TOKEN",
                     "GITHUB_ENTERPRISE_TOKEN", "GH_REPO"):
            self._log_env.pop(name, None)
        self._log_env["GH_HOST"] = "github.com"
        self._log_env["GH_TOKEN"] = self._token

    def request(self, method, suffix, payload=None):
        # The repository metadata endpoint is the repository root itself:
        # GET /repos/{owner}/{repo}, with no suffix. No mutating empty routes.
        check(method in ("GET", "POST", "DELETE") and
              (suffix.startswith("/") or (method == "GET" and suffix in ("", "@user"))) and
              "\n" not in suffix and "\r" not in suffix,
              "unapproved API route")
        route = urllib.parse.urlsplit(suffix)
        check(not suffix.startswith("//") and not any(c in suffix for c in
              ("\\", "#", "\t")) and not route.scheme and not route.netloc and
              (suffix in ("", "@user") or route.path.startswith("/")),
              "invalid API suffix")
        check(not any(part in route.path.lower() for part in (
              "..", "%2f", "%2e", "%5c", "%00")), "unsafe API route encoding")
        if method == "GET" and "?" in suffix:
            try:
                query = urllib.parse.parse_qs(route.query, strict_parsing=True,
                                             keep_blank_values=True)
            except ValueError as exc:
                raise Stop("invalid API query") from exc
            if route.path == "/actions/runs":
                check(set(query) == {"event", "created", "per_page", "page"} and
                      all(len(values) == 1 for values in query.values()) and
                      query["event"][0] in EVENTS and query["per_page"] == ["100"] and
                      query["page"][0] in ("1", "2", "3"), "invalid census query")
                bounds = query["created"][0].split("..")
                check(len(bounds) == 2 and
                      all(re.fullmatch(r"[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z",
                                       bound) for bound in bounds) and
                      dt.timedelta(0) < utc(bounds[1]) - utc(bounds[0]) <=
                      dt.timedelta(minutes=120), "invalid census query window")
            else:
                check(route.path in {f"/contents/.github/workflows/w3-{name}.yml"
                                     for name in VARIANTS.values()} and
                      set(query) == {"ref"} and len(query["ref"]) == 1 and
                      HEX.fullmatch(query["ref"][0]), "invalid fixture query")
        if method == "POST":
            check(suffix == "/git/refs" and isinstance(payload, dict) and
                  set(payload) == {"ref", "sha"} and
                  isinstance(payload["ref"], str) and
                  bool(re.fullmatch(
                      r"refs/heads/hamster/admitted/w3-[0-9a-f]{12}-canary",
                      payload["ref"])) and
                  bool(NONCE.fullmatch(
                      payload["ref"].split("/w3-", 1)[1].split("-canary", 1)[0])) and
                  sha(payload["sha"]) == payload["sha"],
                  "unapproved REST ref create")
        if method == "DELETE":
            check(payload is None and bool(re.fullmatch(
                  r"/git/refs/heads/hamster/admitted/w3-[0-9a-f]{12}-canary",
                  suffix)), "unapproved REST ref deletion")
        if suffix == "@user":
            check(method == "GET" and payload is None, "user endpoint is GET only")
            path = API_ORIGIN + "/user"
        else:
            path = f"{API_ORIGIN}/repos/{self.repo}{suffix}"
        body = None if payload is None else json.dumps(
            payload, separators=(",", ":")).encode()
        request = urllib.request.Request(path, data=body, method=method, headers={
            "Accept": "application/vnd.github+json",
            "Authorization": "Bearer " + self._token,
            "User-Agent": "phil-w3-disposable-selector-probe",
            "X-GitHub-Api-Version": "2022-11-28",
            "Content-Type": "application/json",
        })
        status = None
        try:
            with self._opener.open(request, timeout=20) as resp:
                status = resp.status
                limit = 1024 * 1024 + 1
                if method != "GET" and isinstance(resp, HTTPResponse):
                    raw, complete = bounded_body(resp, limit)
                    check(complete, "incomplete mutation response framing")
                else:
                    raw = resp.read(limit)
                check(len(raw) < limit, "oversized API response")
                return status, strict_json(raw.decode()) if raw.strip() else None
        except urllib.error.HTTPError as exc:
            try:
                diagnostic = (None if method == "GET" else
                              HttpErrorDiagnostic(capture_http_error(exc, self._token)))
                return exc.code, diagnostic
            finally:
                try:
                    exc.close()
                except Exception:
                    pass  # A close failure does not erase a received HTTP status.
        except Exception:
            if method != "GET" and status is not None:
                # No untrusted bytes from ordinary response processing are
                # admitted into the diagnostic sidecar.
                return status, HttpErrorDiagnostic({
                    "capture": "failed", "headers": {}, "body_bytes_inspected": 0,
                    "failure_stage": "ordinary-response-processing",
                })
            raise Stop("API response unavailable or invalid") from None

    def must_get(self, suffix):
        status, data = self.request("GET", suffix)
        check(status == 200, f"read-only GitHub GET rejected HTTP {status}")
        return data


    def repo_metadata(self):
        meta = self.must_get("")
        check(isinstance(meta, dict) and meta.get("full_name") == self.repo and
              meta.get("default_branch") == "main" and
              meta.get("archived") is False and
              type(meta.get("id")) is int and meta["id"] > 0 and
              isinstance(meta.get("owner"), dict) and
              meta["owner"].get("login", "").casefold() ==
              self.repo.split("/", 1)[0].casefold(),
              "disposable repository identity/default changed")
        return meta

    def operator(self, expected):
        check(isinstance(expected, str) and
              bool(re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9-]{0,38}", expected)),
              "approved operator login required")
        person = self.must_get("@user")
        check(isinstance(person, dict) and
              isinstance(person.get("login"), str) and
              person["login"].casefold() == expected.casefold() and
              type(person.get("id")) is int and person["id"] > 0,
              "authenticated GitHub.com principal not approved")
        return person["login"]

    def main(self):
        j = self.must_get("/git/ref/heads/main")
        check(j.get("ref") == "refs/heads/main", "main ref mismatch")
        return sha(j["object"]["sha"])

    def admitted(self):
        rows = self.must_get("/git/matching-refs/heads/hamster/admitted/")
        check(isinstance(rows, list) and len(rows) < 100, "invalid/large admitted prefix")
        result = {}
        for row in rows:
            name = row.get("ref")
            check(isinstance(name, str) and
                  name.startswith("refs/heads/hamster/admitted/") and
                  name not in result and row.get("object", {}).get("type") == "commit",
                  "noncanonical admitted ref inventory")
            result[name] = sha(row["object"]["sha"])
        return result

    def verify_fixture(self, default_sha, target_sha):
        for name, rev, flavor in (("main", default_sha, "default_v1"),
                                  ("target", target_sha, "target_v1")):
            for file in VARIANTS.values():
                filename = f"w3-{file}.yml"
                expected = (ROOT / "fixtures" / flavor / ".github" /
                            "workflows" / filename).read_bytes()
                response = self.must_get(
                    f"/contents/.github/workflows/{filename}?ref={rev}")
                check(response.get("encoding") == "base64" and
                      isinstance(response.get("content"), str),
                      f"missing fixture content at {name}/{filename}")
                actual = base64.b64decode(response["content"], validate=False)
                check(actual == expected,
                      f"workflow fixture bytes differ at {name}/{filename}")

def preflight(api, ref, target, default):
    meta = api.repo_metadata()
    check(api.main() == default and default != target,
          "default SHA moved or matches target")
    target_commit = api.must_get("/git/commits/" + target)
    check(target_commit.get("sha") == target, "unavailable exact target commit")
    api.verify_fixture(default, target)
    refs = api.admitted()
    check(set(refs).issubset({ref}), "foreign admitted refs: STOP")
    return {"repo": api.repo, "repository_id": meta["id"], "ref": ref,
            "target_sha": target, "default_sha": default,
            "observed_refs": refs}


def execute(args):
    repo = verify_repo_name(args.repo)
    ref = ref_for(args.nonce)
    target, default = sha(args.target_sha), sha(args.default_sha)
    api = GitHub(repo)
    operator = api.operator(args.actor)
    before = preflight(api, ref, target, default)
    check(before["repository_id"] == args.repo_id and args.repo_id > 0,
          "approved test repository numeric identity changed")
    action = args.action
    if action == "plan":
        print(json.dumps({"decision": "GET_ONLY_PLAN_NO_WRITES",
                          "api_origin": API_ORIGIN, "approved_actor": operator,
                          **before}, sort_keys=True))
        return
    check(args.confirm == {"create": "CREATE_TEST_ONLY",
                           "delete": "DELETE_TEST_ONLY",
                           "abort-cleanup": "ABORT_CLEANUP_TEST_ONLY"}[action],
          "manual phase confirmation mismatch")
    check(action != "create" or not before["observed_refs"],
          "create requires empty admitted namespace")
    check(action == "create" or before["observed_refs"] in ({}, {ref: target}),
          "cleanup requires absent or exact owned ref/SHA")
    directory = Path(args.state_dir)
    check(directory.is_dir() and not directory.is_symlink(),
          "pre-existing local state directory required")
    marker = directory / (args.nonce + (".create-intent.json" if action == "create"
                                        else ".delete-intent.json"))
    intent = {"schema": "W3-SELECTOR-LOCAL-MUTATION-V1", "action": action,
              "decision": "INTENT_UNKNOWN_AFTER_INTERRUPTION",
              "prepared_at": iso(dt.datetime.now(UTC)),
              "api_origin": API_ORIGIN, "approved_actor": operator,
              **before}
    probe_digest = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    durable_new(marker, intent)  # file AND containing-directory fsynced
    if action != "create" and not before["observed_refs"]:
        intent["decision"] = "ALREADY_ABSENT_NO_WRITE"
        durable_replace(marker, intent)
        print(json.dumps(intent, sort_keys=True))
        return
    method = "POST" if action == "create" else "DELETE"
    route = "/git/refs" if action == "create" else "/git/refs/" + ref.removeprefix("refs/")
    payload = {"ref": ref, "sha": target} if action == "create" else None
    expected_status = 201 if action == "create" else 204
    unavailable = {"capture": "unavailable", "headers": {}, "body_bytes_inspected": 0}
    try:
        intent["request_started_at"] = iso(dt.datetime.now(UTC))
        try:
            status, response = api.request(method, route, payload)
        except Stop:
            intent["request_completed_at"] = iso(dt.datetime.now(UTC))
            intent["http_status"] = None
            preserve_diagnostic(marker, intent, unavailable, args.nonce, probe_digest)
            raise Stop("mutation response unavailable; intent remains consumed") from None
        received_expected_response = (
            status == expected_status and not isinstance(response, HttpErrorDiagnostic))
        if not received_expected_response:
            intent["request_completed_at"] = iso(dt.datetime.now(UTC))
            intent["http_status"] = status
            diagnostic = (response.payload if isinstance(response, HttpErrorDiagnostic)
                          else unavailable)
            preserve_diagnostic(marker, intent, diagnostic, args.nonce, probe_digest)
        actual = api.admitted()
        if received_expected_response:
            intent["request_completed_at"] = iso(dt.datetime.now(UTC))
        intent["http_status"] = status
        intent["observed_refs_after"] = actual
        verified = received_expected_response and actual == (
            {ref: target} if action == "create" else {})
        intent["decision"] = (
            ("ABORT_CLEANUP_STATE_VERIFIED" if action == "abort-cleanup"
             else "EXACT_STATE_VERIFIED") if verified else
            "STOP_UNEXPECTED_OR_AMBIGUOUS_POSTSTATE")
    except Exception:
        intent["decision"] = "STOP_UNKNOWN_AFTER_REQUEST"
        try:
            durable_replace(marker, intent)
        except (OSError, Stop):
            raise Stop("final STOP receipt could not be preserved; intent remains consumed") from None
        raise Stop("mutation evidence incomplete; intent remains consumed") from None
    try:
        durable_replace(marker, intent)
    except (OSError, Stop):
        raise Stop("final mutation receipt could not be preserved; intent remains consumed") from None
    # Only the intent summary is printable. The sidecar stays owner-local.
    print(json.dumps(intent, sort_keys=True))
    check(intent["decision"] in ("EXACT_STATE_VERIFIED",
                                 "ABORT_CLEANUP_STATE_VERIFIED"),
          "mutation is not VERIFIED")


def log_witness(api, run):
    # Bound log provenance to the same credential, host, repository, run ID,
    # and original attempt used for the direct GitHub.com REST inventory.
    run_id = run["id"]
    check(type(run_id) is int and run_id > 0 and run["run_attempt"] == 1,
          "log target is not original authenticated run")
    cp = subprocess.run(["gh", "run", "view", str(run_id), "--repo", api.repo,
                         "--attempt", "1", "--log"], env=api._log_env,
                        capture_output=True, text=True, timeout=50, check=False)
    if cp.returncode != 0 or len(cp.stdout) > 2_000_000:
        return None, {"transport": LOG_TRANSPORT, "status": "UNAVAILABLE"}
    raw_log = cp.stdout
    records = []
    for line in raw_log.splitlines():
        # gh prefixes each runner log line with job and step columns. The
        # runner timestamps the message before gh adds those columns.
        message = re.sub(
            r"^(?:[^\t]+\t[^\t]+\t)?[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9:.]+Z ",
            "", line, count=1)
        if not message.startswith(WITNESS_PREFIX):
            continue
        raw = message.removeprefix(WITNESS_PREFIX).strip()
        try:
            doc = strict_json(raw)
        except (ValueError, Stop):
            records.append(None)  # malformed witness never becomes absence
            continue
        records.append(doc)
    receipt = {"transport": LOG_TRANSPORT, "status": (
        "ONE_RECORD" if len(records) == 1 and isinstance(records[0], dict)
        else "AMBIGUOUS_OR_MISSING"),
        "sha256": hashlib.sha256(raw_log.encode()).hexdigest()}
    return (records[0] if receipt["status"] == "ONE_RECORD" else None), receipt


def snapshot(args):
    repo = verify_repo_name(args.repo)
    nonce_ref = ref_for(args.nonce)
    target, default = sha(args.target_sha), sha(args.default_sha)
    check(target != default, "source revisions must be distinct")
    start, end = utc(args.window_start), utc(args.window_end)
    check(dt.timedelta(0) < end-start <= dt.timedelta(minutes=120),
          "window outside bounds")
    api = GitHub(repo)
    meta = api.repo_metadata()
    check(meta["id"] == args.repo_id and args.repo_id > 0,
          "approved test repository numeric identity changed")
    operator = api.operator(args.actor)
    check(api.main() == default, "selected default SHA has moved")
    api.verify_fixture(default, target)
    main_before = getattr(args, "main_before_sha", None)
    if main_before is not None:
        check(sha(main_before) not in (default, target), "invalid Phase A setup SHA")
        setup = api.must_get("/git/commits/" + main_before)
        control = api.must_get("/git/commits/" + default)
        check(isinstance(setup, dict) and setup.get("sha") == main_before and
              isinstance(control, dict) and control.get("sha") == default and
              isinstance(setup.get("tree"), dict) and
              isinstance(control.get("tree"), dict) and
              sha(setup["tree"].get("sha")) == control["tree"].get("sha") and
              isinstance(control.get("parents"), list) and
              len(control["parents"]) == 1 and isinstance(control["parents"][0], dict) and
              control["parents"][0].get("sha") == main_before,
              "Phase A requires an exact empty child of the setup SHA")
    found, counts = {}, {}
    created = f"{iso(start)}..{iso(end)}"
    for event in EVENTS:
        event_runs = {}
        total = None
        for page in range(1, 4):
            query = urllib.parse.urlencode({"event": event, "created": created,
                                            "per_page": 100, "page": page})
            doc = api.must_get("/actions/runs?" + query)
            check(isinstance(doc, dict), "run census is not an object")
            observed_total, runs = doc.get("total_count"), doc.get("workflow_runs")
            check(type(observed_total) is int and
                  0 <= observed_total < MAX_RUNS and isinstance(runs, list),
                  "unbounded/invalid run census")
            if total is None:
                total = observed_total
            check(observed_total == total,
                  "run census total drifted between pages")
            expected_len = max(0, min(100, total - len(event_runs)))
            check(len(runs) == expected_len,
                  "run census page has a hole or unstable page length")
            for run in runs:
                check(isinstance(run, dict) and run.get("event") == event and
                      type(run.get("id")) is int and run["id"] > 0 and
                      run["id"] not in event_runs and
                      start <= utc(run.get("created_at")) <= end and
                      type(run.get("run_attempt")) is int and
                      run["run_attempt"] == 1,
                      "noncanonical/replayed/duplicate run inventory")
                rid = run["id"]
                check(run.get("url") ==
                      f"{API_ORIGIN}/repos/{repo}/actions/runs/{rid}" and
                      run.get("html_url") ==
                      f"https://github.com/{repo}/actions/runs/{rid}" and
                      isinstance(run.get("repository"), dict) and
                      type(run["repository"].get("id")) is int and
                      run["repository"]["id"] == meta["id"] and
                      (run.get("head_repository") is None or
                       (type(run["head_repository"].get("id")) is int and
                        run["head_repository"]["id"] == meta["id"])) and
                      isinstance(run.get("actor"), dict) and
                      run["actor"].get("login") == operator and
                      type(run.get("workflow_id")) is int and
                      run["workflow_id"] > 0 and
                      type(run.get("run_number")) is int and
                      run["run_number"] > 0,
                      "untrusted run host/repository/operator/attempt provenance")
                head = sha(run.get("head_sha"))
                check(head in (target, default),
                      "run head SHA not one of the two independently pinned sources")
                event_runs[rid] = {
                    "id": rid, "event": event,
                    "created_at": run["created_at"],
                    "path": run.get("path"),
                    "head_branch": run.get("head_branch"),
                    "head_sha": head, "actor": operator,
                    "status": run.get("status"),
                    "conclusion": run.get("conclusion"),
                    "workflow_id": run["workflow_id"],
                    "run_number": run["run_number"],
                    "run_attempt": run["run_attempt"],
                    "repository_id": meta["id"],
                    "url": run["url"], "html_url": run["html_url"]}
            if len(event_runs) == total:
                break
        check(len(event_runs) == total, "truncated run census")
        counts[event] = total
        for rid, item in event_runs.items():
            check(rid not in found, "duplicate run across event inventories")
            if item["status"] == "completed":
                item["witness"], item["log_provenance"] = log_witness(api, item)
            else:
                item["witness"] = None
                item["log_provenance"] = {
                    "transport": LOG_TRANSPORT, "status": "NOT_COMPLETED"}
            found[rid] = item
    evidence = {
        "schema": "W3-SELECTOR-CENSUS-V3",
        "repository": repo, "repository_id": meta["id"],
        "api_origin": API_ORIGIN, "log_transport": LOG_TRANSPORT,
        "approved_actor": operator,
        "ref": nonce_ref, "nonce": args.nonce,
        "target_sha": target, "default_sha": default,
        "main_before_sha": main_before,
        "window_start": iso(start), "window_end": iso(end),
        "observed_at": iso(dt.datetime.now(UTC)),
        "event_totals": counts,
        "runs": sorted(found.values(), key=lambda j: j["id"]),
        "decision": "READ_ONLY_NOT_CERTIFIED"}
    durable_new(args.out, evidence)
    print(json.dumps({"decision": evidence["decision"], "count": len(found),
                      "event_totals": counts, "out": str(args.out)},
                     sort_keys=True))


def load_snapshot(path):
    doc = strict_json(Path(path).read_text())
    check(isinstance(doc, dict) and
          doc.get("schema") == "W3-SELECTOR-CENSUS-V3" and
          doc.get("decision") == "READ_ONLY_NOT_CERTIFIED" and
          doc.get("api_origin") == API_ORIGIN and
          doc.get("log_transport") == LOG_TRANSPORT and
          isinstance(doc.get("runs"), list), "invalid census snapshot")
    repo = verify_repo_name(doc.get("repository"))
    check(type(doc.get("repository_id")) is int and doc["repository_id"] > 0 and
          isinstance(doc.get("approved_actor"), str) and
          bool(re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9-]{0,38}",
                            doc["approved_actor"])) and
          doc.get("ref") == ref_for(doc.get("nonce")) and
          sha(doc.get("target_sha")) != sha(doc.get("default_sha")),
          "census repository, identity or source binding mismatch")
    check("main_before_sha" in doc and
          (doc["main_before_sha"] is None or
           sha(doc["main_before_sha"]) not in (doc["target_sha"], doc["default_sha"])),
          "invalid Phase A setup SHA")
    check(doc["repository"] == repo and
          isinstance(doc.get("event_totals"), dict) and
          set(doc["event_totals"]) == set(EVENTS) and
          all(type(v) is int and 0 <= v < MAX_RUNS for v in
              doc["event_totals"].values()) and
          len(doc["runs"]) == sum(doc["event_totals"].values()),
          "census pagination evidence missing or inconsistent")
    start, end = utc(doc.get("window_start")), utc(doc.get("window_end"))
    observed = utc(doc.get("observed_at"))
    check(dt.timedelta(0) < end-start <= dt.timedelta(minutes=120) and
          observed >= start, "invalid census capture window")
    ids, per_event = set(), {name: 0 for name in EVENTS}
    for run in doc["runs"]:
        check(isinstance(run, dict) and type(run.get("id")) is int and
              run["id"] > 0 and run["id"] not in ids and
              run.get("event") in EVENTS and
              type(run.get("repository_id")) is int and
              run["repository_id"] == doc["repository_id"] and
              run.get("url") == f"{API_ORIGIN}/repos/{repo}/actions/runs/{run['id']}" and
              run.get("html_url") ==
              f"https://github.com/{repo}/actions/runs/{run['id']}" and
              type(run.get("workflow_id")) is int and run["workflow_id"] > 0 and
              type(run.get("run_number")) is int and run["run_number"] > 0 and
              type(run.get("run_attempt")) is int and run["run_attempt"] == 1 and
              run.get("actor") == doc["approved_actor"] and
              sha(run.get("head_sha")) in (doc["target_sha"], doc["default_sha"]) and
              start <= utc(run.get("created_at")) <= end and
              utc(run["created_at"]) <= observed and
              isinstance(run.get("log_provenance"), dict) and
              run["log_provenance"].get("transport") == LOG_TRANSPORT and
              run["log_provenance"].get("status") in
              ("ONE_RECORD", "AMBIGUOUS_OR_MISSING",
               "UNAVAILABLE", "NOT_COMPLETED"),
              "census run provenance is inconsistent or forged")
        ids.add(run["id"])
        per_event[run["event"]] += 1
        if run["log_provenance"]["status"] == "ONE_RECORD":
            check(isinstance(run.get("witness"), dict) and
                  isinstance(run["log_provenance"].get("sha256"), str) and
                  bool(re.fullmatch("[0-9a-f]{64}",
                                    run["log_provenance"]["sha256"])),
                  "log witness lacks authenticated retrieval checksum")
        else:
            check(run.get("witness") is None, "unverified log witness")
    check(per_event == doc["event_totals"], "event totals do not reconcile")
    return doc


def load_intent(path, before, after, phase):
    check(path is not None, "phase requires exact one-use mutation receipt")
    marker = strict_json(Path(path).read_text())
    check(isinstance(marker, dict) and
          marker.get("schema") == "W3-SELECTOR-LOCAL-MUTATION-V1" and
          marker.get("action") == phase and
          marker.get("decision") == "EXACT_STATE_VERIFIED",
          "planned phase requires its own successful receipt; abort-cleanup is NOT Phase C")
    for a, b in (("repo", "repository"),
                 ("repository_id", "repository_id"),
                 ("ref", "ref"), ("target_sha", "target_sha"),
                 ("default_sha", "default_sha"),
                 ("approved_actor", "approved_actor"),
                 ("api_origin", "api_origin")):
        check(marker.get(a) == after[b], "mutation and census provenance mismatch")
    check(type(marker.get("repository_id")) is int and
          type(marker.get("http_status")) is int and
          marker["http_status"] == (201 if phase == "create" else 204) and
          marker.get("observed_refs") ==
          ({} if phase == "create" else {after["ref"]: after["target_sha"]}) and
          marker.get("observed_refs_after") ==
          ({after["ref"]: after["target_sha"]} if phase == "create" else {}),
          "mutation receipt not exact and verified")
    start = utc(before["window_start"])
    end = utc(before["window_end"])
    early = utc(before["observed_at"])
    prepared, request, completed = (
        utc(marker.get(key)) for key in
        ("prepared_at", "request_started_at", "request_completed_at"))
    check(start <= early <= prepared <= request <= completed <= end and
          completed <= utc(after["observed_at"]),
          "mutation not time-bound inside selected window")
    return marker


def valid_witness(run, census):
    witness = run.get("witness")
    if not isinstance(witness, dict):
        return None
    keys = {"schema", "variant", "source_marker", "event_name", "event_ref",
            "event_created", "event_deleted", "event_ref_type", "github_ref", "github_sha",
            "run_id", "actor", "workflow_ref"}
    if set(witness) != keys or witness["schema"] != "PHIL-W3-SELECTOR-WITNESS-V2":
        return None
    kind = witness["variant"]
    if kind not in VARIANTS or witness["source_marker"] not in (
            "TARGET_V1", "DEFAULT_V1"):
        return None
    if (type(witness["event_created"]) not in (bool, type(None)) or
        type(witness["event_deleted"]) not in (bool, type(None)) or
        witness["event_ref_type"] not in (
            ("branch", "tag") if run["event"] in ("create", "delete") else (None,)) or
        type(witness["run_id"]) is not str or
        str(run["id"]) != witness["run_id"] or
        run["event"] != witness["event_name"] or
        run["actor"] != witness["actor"] or
        witness["actor"] != census["approved_actor"] or
        witness["github_sha"] != run["head_sha"]):
        return None
    path = ".github/workflows/w3-" + VARIANTS[kind] + ".yml"
    source_sha = (census["target_sha"] if
                  witness["source_marker"] == "TARGET_V1"
                  else census["default_sha"])
    selected_ref = ("refs/heads/main" if source_sha == census["default_sha"]
                    else census["ref"])
    if (run["path"] != path or run["head_sha"] != source_sha or
        witness["github_ref"] != selected_ref or
        witness["workflow_ref"] !=
            census["repository"] + "/" + path + "@" + selected_ref or
        run["head_branch"] !=
            ("main" if source_sha == census["default_sha"]
             else census["ref"].removeprefix("refs/heads/"))):
        return None
    return witness


def classify(args):
    before, after = load_snapshot(args.before), load_snapshot(args.after)
    keys = ("repository", "repository_id", "ref", "nonce", "window_start",
            "window_end", "api_origin", "log_transport", "approved_actor",
            "target_sha")
    check(all(before.get(k) == after.get(k) for k in keys),
          "census binding mismatch")
    check(before["main_before_sha"] is None, "invalid before capture")
    if args.phase == "main":
        check(after["main_before_sha"] == before["default_sha"] and
              before["default_sha"] != after["default_sha"],
              "unexpected Phase A default SHA transition")
    else:
        check(after["main_before_sha"] is None and
              before["default_sha"] == after["default_sha"],
              "unexpected default SHA transition")
    check(before["event_totals"] == {name: 0 for name in EVENTS} and
          not before["runs"], "before capture already has event traffic")
    start, end = utc(before["window_start"]), utc(before["window_end"])
    t0, t1 = utc(before["observed_at"]), utc(after["observed_at"])
    check(start <= t0 <= t1 and t1 >= end + dt.timedelta(minutes=30),
          "incomplete bounded observation delay")
    earliest_run = t0
    if args.phase in ("create", "delete"):
        marker = load_intent(getattr(args, "intent", None), before, after, args.phase)
        earliest_run = utc(marker["request_started_at"])
    else:
        check(getattr(args, "intent", None) is None,
              "main control does not use a mutation receipt")
    old = {r["id"]: r for r in before["runs"]}
    new = {r["id"]: r for r in after["runs"] if r["id"] not in old}
    check(len(old) == len(before["runs"]) and
          len(old)+len(new) == len(after["runs"]), "run inventory changed")
    for rid, original in old.items():
        run = next((r for r in after["runs"] if r["id"] == rid), None)
        check(run is not None, "previously observed run disappeared")
        invariant = ("id", "event", "created_at", "path", "head_branch",
                     "head_sha", "actor", "workflow_id", "run_number",
                     "run_attempt", "repository_id", "url", "html_url")
        check(all(run.get(k) == original.get(k) for k in invariant),
              "retained run provenance changed between captures")
        check(original.get("witness") is None or
              run.get("witness") == original.get("witness"),
              "retained witness changed between captures")
    desired_ref = "refs/heads/main" if args.phase == "main" else after["ref"]
    positives, forbidden_seen, unexpected, auxiliary = {}, set(), [], []
    required = ({"UNFILTERED", "MAIN_ONLY", "IGNORE_PAIR"} if
                args.phase == "main" else {"UNFILTERED", "W3_ONLY"})
    forbidden = ({"W3_ONLY"} if args.phase == "main"
                 else {"MAIN_ONLY", "IGNORE_PAIR"})
    for run in new.values():
        witness = valid_witness(run, after)
        if (utc(run["created_at"]) < earliest_run or
            witness is None or run["status"] != "completed" or
            run["conclusion"] != "success" or
            run["log_provenance"]["status"] != "ONE_RECORD"):
            unexpected.append(run["id"])
            continue
        if run["event"] in ("create", "delete"):
            # Auxiliary events are observable evidence, NOT deletion-caused
            # push controls. Allow only the one expected unfiltered event.
            short_ref = after["ref"].removeprefix("refs/heads/")
            if (args.phase == run["event"] and
                witness["variant"] == "UNFILTERED" and
                witness["event_ref"] == short_ref and
                witness["event_created"] is None and
                witness["event_deleted"] is None and
                witness["event_ref_type"] == "branch" and
                witness["source_marker"] ==
                ("TARGET_V1" if run["event"] == "create" else "DEFAULT_V1")):
                auxiliary.append(run["id"])
            else:
                unexpected.append(run["id"])
            continue
        if (run["event"] != "push" or witness["event_ref"] != desired_ref or
            (args.phase == "main" and witness["source_marker"] != "DEFAULT_V1")):
            unexpected.append(run["id"])
            continue
        if witness["variant"] in forbidden:
            forbidden_seen.add(witness["variant"])
        expected_flags = (False, False) if args.phase == "main" else (
            (True, False) if args.phase == "create" else (False, True))
        if ((witness["event_created"], witness["event_deleted"]) !=
                expected_flags or witness["variant"] in positives):
            unexpected.append(run["id"])
        else:
            positives[witness["variant"]] = run["id"]
    if forbidden_seen:
        decision = "COUNTEREXAMPLE_STOP"
    elif unexpected or len(auxiliary) > 1:
        decision = "STOP_UNRELATED_OR_AMBIGUOUS_TRAFFIC"
    elif not required.issubset(positives):
        decision = "INCONCLUSIVE_MISSING_POSITIVE_WITNESS"
    else:
        decision = "SUPPORTS_MODEL_BOUNDED_NOT_CERTIFIED"
    print(json.dumps({
        "decision": decision, "phase": args.phase,
        "required": sorted(required), "positive": sorted(positives),
        "forbidden": sorted(forbidden_seen),
        "unexpected_run_ids": sorted(unexpected),
        "auxiliary_event_run_ids": sorted(auxiliary),
        "new_run_ids": sorted(new),
        "event_totals": after["event_totals"],
        "observation_lag_seconds": int((t1-end).total_seconds()),
        "execution_authorized": False, "quarantine_certified": False},
        sort_keys=True))

def cli():
    ap=argparse.ArgumentParser(description=__doc__)
    sub=ap.add_subparsers(dest="command",required=True)
    for name in ("plan","create","delete","abort-cleanup"):
        p=sub.add_parser(name)
        p.add_argument("--repo",required=True)
        p.add_argument("--repo-id",type=int,required=True)
        p.add_argument("--actor",required=True)
        p.add_argument("--nonce",required=True)
        p.add_argument("--target-sha",required=True)
        p.add_argument("--default-sha",required=True)
        if name!="plan":
            p.add_argument("--state-dir",required=True)
            p.add_argument("--confirm",required=True)
        p.set_defaults(action=name,handler=execute)
    p=sub.add_parser("snapshot")
    p.add_argument("--repo",required=True)
    p.add_argument("--repo-id",type=int,required=True)
    p.add_argument("--actor",required=True)
    p.add_argument("--nonce",required=True)
    p.add_argument("--target-sha",required=True)
    p.add_argument("--default-sha",required=True)
    p.add_argument("--main-before-sha",
                   help="Phase A after capture only: exact setup commit before the empty main push")
    p.add_argument("--window-start",required=True)
    p.add_argument("--window-end",required=True)
    p.add_argument("--out",required=True)
    p.set_defaults(handler=snapshot)
    p=sub.add_parser("classify")
    p.add_argument("--phase",choices=("main","create","delete"),required=True)
    p.add_argument("--before",required=True)
    p.add_argument("--after",required=True)
    p.add_argument("--intent",help="required verified create/delete receipt; never abort-cleanup")
    p.set_defaults(handler=classify)
    args=ap.parse_args()
    try:
        args.handler(args)
    except Stop as exc:
        print("W3 DISPOSABLE SELECTOR STOP: "+str(exc),file=sys.stderr)
        sys.exit(1)

if __name__=="__main__":
    cli()
