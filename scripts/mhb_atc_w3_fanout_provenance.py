#!/usr/bin/env python3
"""W3 publisher fanout: immutable original-run authority and recovery binding.

Only local Git reads and authenticated GitHub GETs through an injected client.
No app-token minting, ref mutation, artifact overwrite, or untrusted code.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import re
import subprocess

from mhb_atc_w3_provenance import snapshot_tree

REPO = "abiggerhammer/phil"
WORKFLOW = ".github/workflows/mhb-atc-w3-publisher-fanout.yml"
POLICY_PATH = ".github/atc-w3-fanout.json"
ORIGIN_SCHEMA = "MHB-ATC-W3-FANOUT-ORIGIN-V1"
TARGET = "e38814a2e916252a8a7f3dd438943e8f4a21664a"
TREE = "4b8b338a7a0ebed852407c9288d4a293bc26066f"
PUBLISHER_ID = 5782193
RULESET_ID = 27365284
SHA = re.compile(r"[0-9a-f]{40}\Z")
NONCE = re.compile(r"[0-9a-f]{12}\Z")
RUN = re.compile(r"[1-9][0-9]{0,15}\Z")
MAX_BINDING_BYTES = 4096
MAX_POLICY_BYTES = 4096
POLICY_KEYS = {
    "schema", "repository", "source_authorized", "approved_nonce",
    "experiment", "publisher_app_id", "publisher_app_slug", "ruleset_id",
    "ref_template", "frozen_target_sha", "reviewed_target_workflows_sha",
    "max_authorized_ref_mutations", "observation_events",
    "observation_window_minutes_limit", "baseline", "cleanup", "approval",
    "outcome",
}


class FanoutStop(ValueError):
    pass


def check(value, message):
    if not value:
        raise FanoutStop(message)


def sha(value):
    check(isinstance(value, str) and SHA.fullmatch(value),
          "invalid fanout commit/tree SHA")
    return value


def nonce_ref(value):
    check(isinstance(value, str) and NONCE.fullmatch(value),
          "fanout nonce must be 12 lowercase hex")
    return "refs/heads/hamster/admitted/w3-fanout-" + value + "-canary"


def run_id(value):
    check(type(value) is int and 0 < value < 10**16,
          "invalid original Actions run ID")
    return value


def json_doc(raw):
    check(isinstance(raw, bytes) and len(raw) <= MAX_POLICY_BYTES,
          "oversized source policy")
    def unique(items):
        answer = {}
        for key, item in items:
            check(key not in answer, "duplicate source JSON key")
            answer[key] = item
        return answer
    try:
        return json.loads(raw.decode("utf-8"), object_pairs_hook=unique)
    except (UnicodeError, ValueError):
        raise FanoutStop("malformed source JSON") from None


def policy_check(doc, *, nonce=None, require_active=False):
    check(isinstance(doc, dict) and set(doc) == POLICY_KEYS and
          doc.get("schema") == "MHB-ATC-W3-PUBLISHER-FANOUT-V1" and
          doc.get("repository") == REPO and
          type(doc.get("source_authorized")) is bool and
          (doc.get("approved_nonce") is None or
           (isinstance(doc.get("approved_nonce"), str) and
            NONCE.fullmatch(doc["approved_nonce"]))) and
          doc.get("publisher_app_id") == PUBLISHER_ID and
          doc.get("publisher_app_slug") == "phil-atc-publisher" and
          doc.get("ruleset_id") == RULESET_ID and
          doc.get("ref_template") ==
              "refs/heads/hamster/admitted/w3-fanout-<nonce>-canary" and
          doc.get("frozen_target_sha") == TARGET and
          doc.get("reviewed_target_workflows_sha") == TREE and
          type(doc.get("max_authorized_ref_mutations")) is int and
          doc["max_authorized_ref_mutations"] == 2 and
          doc.get("observation_events") == ["push", "create", "delete"] and
          type(doc.get("observation_window_minutes_limit")) is int and
          doc["observation_window_minutes_limit"] == 120,
          "fanout source policy changed outside reviewed schema")
    if require_active:
        check(doc["source_authorized"] is True and
              doc["approved_nonce"] == nonce and
              isinstance(nonce, str) and NONCE.fullmatch(nonce),
              "fanout source activation/nonce is OFF or mismatched")
    return doc


def current_policy(root: Path):
    path = Path(root) / POLICY_PATH
    check(path.is_file() and not path.is_symlink(),
          "fanout source policy missing or symlinked")
    with path.open("rb") as fp:
        doc = json_doc(fp.read(MAX_POLICY_BYTES + 1))
    return policy_check(doc)


def git(root: Path, *args):
    result = subprocess.run(["git", *args], cwd=root,
                            capture_output=True, text=True,
                            check=False, timeout=25)
    check(result.returncode == 0, "trusted Git object query failed")
    return result.stdout.strip()


def trusted_checkout(root: Path):
    check(git(root, "branch", "--show-current") == "main",
          "fanout controller must use trusted main checkout")
    check(git(root, "status", "--porcelain", "--untracked-files=all") == "",
          "fanout controller checkout is not clean")
    head = sha(git(root, "rev-parse", "--verify", "HEAD"))
    check(os.getenv("GITHUB_SHA", head) == head,
          "fanout checkout differs from dispatch SHA")
    return head


def verify_target(root: Path, fanout_policy, w3_policy):
    policy_check(fanout_policy)
    check(isinstance(w3_policy, dict) and
          w3_policy.get("schema") == "MHB-ATC-W3-REF-TRIAL-V2" and
          w3_policy.get("live_authorized") is False and
          w3_policy.get("approved_nonce") is None and
          w3_policy.get("push_ci_quarantine_verified") is False,
          "W3 worker trial must remain fully disabled")
    trio = w3_policy.get("frozen_target_commits")
    check(isinstance(trio, dict) and
          set(trio) == {"source_sha", "parent_sha", "grandparent_sha"} and
          trio.get("parent_sha") == TARGET and
          w3_policy.get("reviewed_quarantine_tree_sha") == TREE,
          "fanout target no longer matches accepted W3 frozen trio")
    snapshot_tree(root, trio["source_sha"], trio["parent_sha"],
                  trio["grandparent_sha"], TREE)
    return TARGET


def policy_blob(root: Path, dispatch_sha):
    return sha(git(root, "rev-parse", "--verify",
                   sha(dispatch_sha) + ":" + POLICY_PATH))


def make_binding(nonce, dispatch_sha, original_run_id, blob_sha):
    ref = nonce_ref(nonce)
    return {
        "schema": ORIGIN_SCHEMA, "repository": REPO,
        "workflow": WORKFLOW, "event": "workflow_dispatch",
        "actor": "abiggerhammer", "run_attempt": 1, "mode": "run",
        "run_id": run_id(original_run_id),
        "nonce": nonce, "ref": ref,
        "dispatch_sha": sha(dispatch_sha),
        "policy_blob_sha": sha(blob_sha),
        "target_sha": TARGET, "workflow_tree_sha": TREE,
        "publisher_app_id": PUBLISHER_ID, "ruleset_id": RULESET_ID,
    }


def valid_binding(doc, *, nonce, expected_run_id):
    check(isinstance(doc, dict), "original fanout binding is not an object")
    keys = set(make_binding("0"*12, "a"*40, 1, "b"*40))
    check(set(doc) == keys, "original fanout binding fields are not canonical")
    canonical = make_binding(doc.get("nonce"), doc.get("dispatch_sha"),
                             doc.get("run_id"), doc.get("policy_blob_sha"))
    check(type(doc.get("run_attempt")) is int and
          doc["run_attempt"] == 1 and doc == canonical and
          doc["nonce"] == nonce and
          doc["run_id"] == run_id(expected_run_id),
          "original fanout binding differs from authorized source")
    return canonical


def write_binding(root: Path, doc):
    """Prepare and fsync nonsecret origin BEFORE any App-token-bearing job."""
    base = Path(os.environ.get("RUNNER_TEMP", "/nonexistent"))
    check(base.is_dir(), "runner origin temporary directory absent")
    output = base / "w3-fanout-origin.json"
    check(not output.exists() and not output.is_symlink(),
          "original fanout origin artifact already exists")
    raw = (json.dumps(doc, sort_keys=True, separators=(",", ":")) +
           "\n").encode("utf-8")
    check(len(raw) < MAX_BINDING_BYTES, "oversized original fanout binding")
    flags = os.O_CREAT | os.O_EXCL | os.O_WRONLY
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    fd = os.open(output, flags, 0o600)
    with os.fdopen(fd, "wb") as stream:
        stream.write(raw)
        stream.flush()
        os.fsync(stream.fileno())
    return output


def read_binding(path: Path, *, nonce, expected_run_id):
    path = Path(path)
    check(path.is_file() and not path.is_symlink() and
          path.name == "w3-fanout-origin.json",
          "original fanout origin artifact missing or symlinked")
    with path.open("rb") as stream:
        raw = stream.read(MAX_BINDING_BYTES + 1)
    check(len(raw) <= MAX_BINDING_BYTES, "oversized fanout original artifact")
    return valid_binding(json_doc(raw), nonce=nonce,
                         expected_run_id=expected_run_id)


def verify_original(client, root: Path, binding, current_source_policy,
                    *, require_current_activation=False):
    """Authenticate original manual run and its own ACTIVE source policy.

    Recovery may take place after current source and runtime switches go OFF:
    the original authorized policy must still be readable as Git data from
    the GitHub-authenticated original Actions dispatch commit.
    """
    valid_binding(binding, nonce=binding["nonce"],
                  expected_run_id=binding["run_id"])
    policy_check(current_source_policy, nonce=binding["nonce"],
                 require_active=require_current_activation)
    reply = client.request("GET", "/actions/runs/" + str(binding["run_id"]))
    check(reply.status == 200 and isinstance(reply.data, dict),
          "original fanout Actions run GET failed")
    run = reply.data
    check(run.get("id") == binding["run_id"] and
          run.get("event") == "workflow_dispatch" and
          run.get("path") == WORKFLOW and
          run.get("head_branch") == "main" and
          run.get("head_sha") == binding["dispatch_sha"] and
          type(run.get("run_attempt")) is int and
          run["run_attempt"] == 1 and
          isinstance(run.get("actor"), dict) and
          run["actor"].get("login") == "abiggerhammer" and
          isinstance(run.get("triggering_actor"), dict) and
          run["triggering_actor"].get("login") == "abiggerhammer" and
          isinstance(run.get("repository"), dict) and
          run["repository"].get("full_name") == REPO,
          "original fanout owner-run provenance mismatch")

    original_dispatch = sha(binding["dispatch_sha"])
    # After main moves, recovery still uses the historical exact original
    # principal/run source and the SAME frozen object, never today's HEAD.
    git(root, "merge-base", "--is-ancestor", original_dispatch, "HEAD")
    check(policy_blob(root, original_dispatch) == binding["policy_blob_sha"],
          "original fanout policy Git blob differs from binding")
    raw = subprocess.run(
        ["git", "show", original_dispatch + ":" + POLICY_PATH], cwd=root,
        capture_output=True, timeout=25, check=False)
    check(raw.returncode == 0 and len(raw.stdout) <= MAX_POLICY_BYTES,
          "original source policy Git object unavailable")
    original_policy = policy_check(json_doc(raw.stdout),
                                   nonce=binding["nonce"],
                                   require_active=True)
    check(original_policy["frozen_target_sha"] ==
          current_source_policy["frozen_target_sha"] and
          original_policy["reviewed_target_workflows_sha"] ==
          current_source_policy["reviewed_target_workflows_sha"],
          "recovery source target changed from authenticated original")
    return binding
