#!/usr/bin/env python3
"""Disposable-repository W3 selector experiment. SOURCE-ONLY; independent review required."""
from __future__ import annotations
import argparse
import base64
import datetime as dt
import hashlib
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
    with os.fdopen(os.open(path, flags, 0o600), "wb") as fd:
        fd.write(data)
        fd.flush()
        os.fsync(fd.fileno())
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

class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args, **kwargs):
        return None

class GitHub:
    def __init__(self, repo):
        self.repo = verify_repo_name(repo)
        check(os.getenv("GITHUB_ACTIONS", "").lower() != "true",
              "forbidden inside GitHub Actions")
        cp = subprocess.run(["gh", "auth", "token"], text=True,
                            capture_output=True, timeout=15, check=False)
        check(cp.returncode == 0 and bool(cp.stdout.strip()) and
              "\n" not in cp.stdout.strip(), "GitHub CLI local auth unavailable")
        self._token = cp.stdout.strip()
        self._opener = urllib.request.build_opener(NoRedirect())

    def request(self, method, suffix, payload=None):
        check(method in ("GET", "POST", "DELETE") and suffix.startswith("/") and
              "\n" not in suffix and "\r" not in suffix,
              "unapproved API route")
        path = f"https://api.github.com/repos/{self.repo}{suffix}"
        body = None if payload is None else json.dumps(
            payload, separators=(",", ":")).encode()
        request = urllib.request.Request(path, data=body, method=method, headers={
            "Accept": "application/vnd.github+json",
            "Authorization": "Bearer " + self._token,
            "User-Agent": "phil-w3-disposable-selector-probe",
            "X-GitHub-Api-Version": "2022-11-28",
            "Content-Type": "application/json",
        })
        try:
            with self._opener.open(request, timeout=20) as resp:
                status = resp.status
                raw = resp.read(1024 * 1024 + 1)
        except urllib.error.HTTPError as exc:
            # Never expose arbitrary API response bodies, URLs with auth, or tokens.
            return exc.code, None
        except Exception as exc:
            raise Stop("UNKNOWN_AFTER_API_REQUEST: reconcile before any retry") from exc
        check(len(raw) <= 1024 * 1024, "oversized API response")
        return status, strict_json(raw.decode()) if raw.strip() else None

    def must_get(self, suffix):
        status, data = self.request("GET", suffix)
        check(status == 200, f"read-only GitHub GET rejected HTTP {status}")
        return data

    def repo_metadata(self):
        meta = self.must_get("")
        check(meta.get("full_name") == self.repo and meta.get("default_branch") == "main" and
              meta.get("archived") is False and isinstance(meta.get("id"), int),
              "disposable repository identity/default changed")
        return meta

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
    before = preflight(api, ref, target, default)
    check(before["repository_id"] == args.repo_id and args.repo_id > 0,
          "approved test repository numeric identity changed")
    action = args.action
    if action == "plan":
        print(json.dumps({"decision": "GET_ONLY_PLAN_NO_WRITES", **before},
                         sort_keys=True))
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
              **before}
    durable_new(marker, intent)  # one-use marker BEFORE request; no retries
    if action != "create" and not before["observed_refs"]:
        intent["decision"] = "ALREADY_ABSENT_NO_WRITE"
        durable_replace(marker, intent)
        print(json.dumps(intent, sort_keys=True))
        return
    status = None
    try:
        if action == "create":
            status, _ = api.request("POST", "/git/refs",
                                    {"ref": ref, "sha": target})
            expected_status = 201
        else:
            suffix = ref.removeprefix("refs/")
            status, _ = api.request("DELETE", "/git/refs/" + suffix)
            expected_status = 204
        actual = api.admitted()
        intent["http_status"] = status
        intent["observed_refs_after"] = actual
        intent["decision"] = ("EXACT_STATE_VERIFIED" if status == expected_status and
                              actual == ({ref: target} if action == "create" else {})
                              else "STOP_UNEXPECTED_OR_AMBIGUOUS_POSTSTATE")
    except Exception:
        intent["decision"] = "STOP_UNKNOWN_AFTER_REQUEST"
        durable_replace(marker, intent)
        raise
    durable_replace(marker, intent)
    print(json.dumps(intent, sort_keys=True))
    check(intent["decision"] == "EXACT_STATE_VERIFIED", "mutation is not VERIFIED")

def log_witness(repo, run_id):
    cp = subprocess.run(["gh", "run", "view", str(run_id), "--repo", repo,
                         "--log"], capture_output=True, text=True,
                        timeout=50, check=False)
    if cp.returncode != 0 or len(cp.stdout) > 2_000_000:
        return None
    records = []
    for line in cp.stdout.splitlines():
        if WITNESS_PREFIX not in line:
            continue
        raw = line.split(WITNESS_PREFIX, 1)[1].strip()
        try:
            doc = strict_json(raw)
        except (ValueError, Stop):
            continue
        records.append(doc)
    return records[0] if len(records) == 1 else None

def snapshot(args):
    repo = verify_repo_name(args.repo)
    nonce_ref = ref_for(args.nonce)
    start, end = utc(args.window_start), utc(args.window_end)
    check(dt.timedelta(0) < end-start <= dt.timedelta(minutes=120),
          "window outside bounds")
    api = GitHub(repo)
    meta = api.repo_metadata()
    check(meta["id"] == args.repo_id and args.repo_id > 0,
          "approved test repository numeric identity changed")
    found = {}
    created = f"{iso(start)}..{iso(end)}"
    for event in EVENTS:
        event_runs = {}
        for page in range(1, 4):
            query = urllib.parse.urlencode({"event":event, "created":created,
                                            "per_page":100, "page":page})
            doc = api.must_get("/actions/runs?" + query)
            total, runs = doc.get("total_count"), doc.get("workflow_runs")
            check(type(total) is int and 0 <= total < MAX_RUNS and
                  isinstance(runs, list), "unbounded/invalid run census")
            for run in runs:
                check(run.get("event") == event and
                      type(run.get("id")) is int and
                      run["id"] not in event_runs and
                      start <= utc(run["created_at"]) <= end,
                      "noncanonical/duplicate run inventory")
                event_runs[run["id"]] = {
                    "id": run["id"], "event": event,
                    "created_at": run["created_at"],
                    "path": run.get("path"), "head_branch": run.get("head_branch"),
                    "head_sha": run.get("head_sha"),
                    "actor": (run.get("actor") or {}).get("login"),
                    "status": run.get("status"),
                    "conclusion": run.get("conclusion")}
            check(len(event_runs) <= total, "inconsistent pagination")
            if len(event_runs) == total:
                break
        check(len(event_runs) == total, "truncated event pagination")
        for rid, item in event_runs.items():
            check(rid not in found, "duplicate run across event inventories")
            item["witness"] = (log_witness(repo, rid)
                               if item["status"] == "completed" else None)
            found[rid] = item
    evidence = {"schema":"W3-SELECTOR-CENSUS-V1",
                "repository":repo, "repository_id":meta["id"],
                "ref":nonce_ref, "nonce":args.nonce,
                "window_start":iso(start), "window_end":iso(end),
                "observed_at":iso(dt.datetime.now(UTC)),
                "runs":sorted(found.values(),key=lambda j:j["id"]),
                "decision":"READ_ONLY_NOT_CERTIFIED"}
    durable_new(args.out, evidence)
    print(json.dumps({"decision":evidence["decision"],"count":len(found),
                      "out":str(args.out)},sort_keys=True))

def load_snapshot(path):
    doc = strict_json(Path(path).read_text())
    check(isinstance(doc, dict) and doc.get("schema") == "W3-SELECTOR-CENSUS-V1" and
          doc.get("decision") == "READ_ONLY_NOT_CERTIFIED" and
          isinstance(doc.get("runs"), list), "invalid census snapshot")
    return doc

def valid_witness(run):
    witness = run.get("witness")
    if not isinstance(witness, dict):
        return None
    keys = {"schema","variant","source_marker","event_name","event_ref",
            "event_created","event_deleted","github_ref","github_sha",
            "run_id","actor","workflow_ref"}
    if set(witness) != keys or witness["schema"] != "PHIL-W3-SELECTOR-WITNESS-V1":
        return None
    if witness["variant"] not in VARIANTS or witness["source_marker"] not in (
            "TARGET_V1","DEFAULT_V1"):
        return None
    if (type(witness["event_created"]) not in (bool,type(None)) or
        type(witness["event_deleted"]) not in (bool,type(None)) or
        str(run["id"]) != witness["run_id"] or
        run["event"] != witness["event_name"]):
        return None
    expected_path = ".github/workflows/w3-" + VARIANTS[witness["variant"]] + ".yml"
    if run["path"] != expected_path:
        return None
    return witness

def classify(args):
    before, after = load_snapshot(args.before), load_snapshot(args.after)
    keys = ("repository","repository_id","ref","nonce","window_start","window_end")
    check(all(before.get(k)==after.get(k) for k in keys), "census binding mismatch")
    verify_repo_name(before["repository"])
    ref_for(before["nonce"])
    start, end = utc(before["window_start"]), utc(before["window_end"])
    t0,t1 = utc(before["observed_at"]), utc(after["observed_at"])
    check(t0<=t1 and t0>=start and t1>=end+dt.timedelta(minutes=30),
          "incomplete bounded observation delay")
    old={r["id"]:r for r in before["runs"]}
    new={r["id"]:r for r in after["runs"] if r["id"] not in old}
    check(len(old)==len(before["runs"]) and
          len(old)+len(new)==len(after["runs"]) and
          all(r["id"] in old or r["id"] in new for r in after["runs"]),
          "duplicate or changed run inventory")
    for run in after["runs"]:
        original = old.get(run["id"])
        if original is None:
            continue
        invariant = ("id","event","created_at","path","head_branch",
                     "head_sha","actor")
        check(all(run.get(k)==original.get(k) for k in invariant),
              "retained run identity changed between captures")
        check(original.get("witness") is None or
              run.get("witness") == original.get("witness"),
              "retained witness changed between captures")
    desired_ref = "refs/heads/main" if args.phase=="main" else after["ref"]
    positive = set()
    unexpected = []
    contrary = set()
    for run in new.values():
        w=valid_witness(run)
        if w is None or run["status"]!="completed" or run["conclusion"]!="success":
            unexpected.append(run["id"])
            continue
        if (w["event_name"]!="push" or w["event_ref"]!=desired_ref or
            not isinstance(w["event_created"],bool) or
            not isinstance(w["event_deleted"],bool)):
            # Separate create/delete events may legitimately be reported;
            # never count them as a deletion-caused PUSH witness.
            if run["event"] in ("create","delete") and w["variant"]=="UNFILTERED":
                continue
            unexpected.append(run["id"])
            continue
        if args.phase=="main" and not w["event_created"] and not w["event_deleted"]:
            positive.add(w["variant"])
        elif args.phase=="create" and w["event_created"] and not w["event_deleted"]:
            positive.add(w["variant"])
        elif args.phase=="delete" and w["event_deleted"] and not w["event_created"]:
            positive.add(w["variant"])
            if w["variant"] in ("MAIN_ONLY","IGNORE_PAIR"):
                contrary.add(w["variant"])
        else:
            unexpected.append(run["id"])
    required={"UNFILTERED","MAIN_ONLY","IGNORE_PAIR"} if args.phase=="main" \
             else {"UNFILTERED","W3_ONLY"}
    forbidden={"W3_ONLY"} if args.phase=="main" else {"MAIN_ONLY","IGNORE_PAIR"}
    if contrary:
        decision="COUNTEREXAMPLE_STOP"
    elif unexpected:
        decision="INCONCLUSIVE_AMBIGUOUS_RUNS"
    elif not required.issubset(positive):
        decision="INCONCLUSIVE_MISSING_POSITIVE_WITNESS"
    elif positive & forbidden:
        decision="COUNTEREXAMPLE_STOP"
    else:
        decision="SUPPORTS_MODEL_BOUNDED_NOT_CERTIFIED"
    print(json.dumps({"decision":decision,"phase":args.phase,
                      "required":sorted(required),"positive":sorted(positive),
                      "unexpected_run_ids":sorted(unexpected),
                      "new_run_ids":sorted(new),
                      "observation_lag_seconds":int((t1-end).total_seconds()),
                      "execution_authorized":False,
                      "quarantine_certified":False},sort_keys=True))

def cli():
    ap=argparse.ArgumentParser(description=__doc__)
    sub=ap.add_subparsers(dest="command",required=True)
    for name in ("plan","create","delete","abort-cleanup"):
        p=sub.add_parser(name)
        p.add_argument("--repo",required=True)
        p.add_argument("--repo-id",type=int,required=True)
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
    p.add_argument("--nonce",required=True)
    p.add_argument("--window-start",required=True)
    p.add_argument("--window-end",required=True)
    p.add_argument("--out",required=True)
    p.set_defaults(handler=snapshot)
    p=sub.add_parser("classify")
    p.add_argument("--phase",choices=("main","create","delete"),required=True)
    p.add_argument("--before",required=True)
    p.add_argument("--after",required=True)
    p.set_defaults(handler=classify)
    args=ap.parse_args()
    try:
        args.handler(args)
    except Stop as exc:
        print("W3 DISPOSABLE SELECTOR STOP: "+str(exc),file=sys.stderr)
        sys.exit(1)

if __name__=="__main__":
    cli()
