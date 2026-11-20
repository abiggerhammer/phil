#!/usr/bin/env python3
"""W3 exact origin binding: safe Git ancestry, authenticated Actions-run recovery.

Source-only utilities. The only network interactions are GET requests through
the injected, already authenticated GitHub transport. No GitHub writes, token
mint, credential or untrusted source execution.
"""
from __future__ import annotations

import json
from pathlib import Path
import re
import subprocess

REPO = "abiggerhammer/phil"
WORKFLOW_PATH = ".github/workflows/mhb-atc-w3-ref-commissioning.yml"
ORIGIN_SCHEMA = "MHB-ATC-W3-ORIGIN-V1"
SHA = re.compile(r"[0-9a-f]{40}\Z")
NONCE = re.compile(r"[0-9a-f]{12}\Z")
MAX_BINDING_BYTES = 4096


class ProvenanceError(ValueError):
    pass


def insist(value, reason):
    if not value:
        raise ProvenanceError(reason)


def commit_sha(value):
    insist(isinstance(value, str) and SHA.fullmatch(value),
           "origin contains invalid commit/tree SHA")
    return value


def run_id(value):
    insist(type(value) is int and value > 0 and value < 10**16,
           "origin contains invalid numeric run ID")
    return value


def snapshot_tree(repo_path: Path, head: str, parent: str, grandparent: str,
                  reviewed_tree: str) -> str:
    """Check *all* possible target SHAs, never only the current checkout.

    Because GitHub selects push workflows from the event commit, all three
    Git object trees MUST equal the independently reviewed quarantine tree.
    Any missing ancestor or changed workflow set is a STOP.
    """
    reviewed_tree = commit_sha(reviewed_tree)
    inspected = (head, parent, grandparent)
    insist(len(set(inspected)) == 3, "target commit SHAs are not distinct")
    for revision in inspected:
        commit_sha(revision)
        p = subprocess.run(
            ["git", "rev-parse", "--verify",
             revision + ":" + ".github/workflows"],
            cwd=repo_path, capture_output=True, text=True, check=False,
            timeout=20)
        insist(p.returncode == 0 and
               p.stdout.strip() == reviewed_tree,
               "target commit workflow tree differs from reviewed quarantine")
    return reviewed_tree


def make_binding(nonce, source, parent, grandparent, tree, attempt_run_id):
    insist(isinstance(nonce, str) and NONCE.fullmatch(nonce),
           "invalid origin nonce")
    head, first_parent, second_ancestor = (
        commit_sha(source), commit_sha(parent), commit_sha(grandparent))
    insist(len({head, first_parent, second_ancestor}) == 3,
           "duplicate original commit SHA")
    return {
        "schema": ORIGIN_SCHEMA,
        "repository": REPO,
        "workflow": WORKFLOW_PATH,
        "actor": "abiggerhammer",
        "event": "workflow_dispatch",
        "mode": "run",
        "run_attempt": 1,
        "run_id": run_id(attempt_run_id),
        "nonce": nonce,
        "source_sha": head,
        "parent_sha": first_parent,
        "grandparent_sha": second_ancestor,
        "workflow_tree_sha": commit_sha(tree),
    }


def validate_binding(doc, *, nonce, original_run_id, reviewed_tree):
    """Canonical, finite, nonsecret binding; reject any unknown/extra fields."""
    insist(isinstance(doc, dict), "original run binding is not an object")
    expected_keys = set(make_binding(
        "0"*12, "a"*40, "b"*40, "c"*40, "d"*40, 1))
    insist(set(doc) == expected_keys,
           "original run binding fields are not canonical")
    checked = make_binding(
        doc.get("nonce"), doc.get("source_sha"),
        doc.get("parent_sha"), doc.get("grandparent_sha"),
        doc.get("workflow_tree_sha"), doc.get("run_id"))
    insist(doc == checked and
           type(doc.get("run_attempt")) is int and
           doc["run_attempt"] == 1,
           "original run binding changed or contains unapproved metadata")
    insist(doc["nonce"] == nonce and
           doc["run_id"] == run_id(original_run_id) and
           doc["workflow_tree_sha"] == commit_sha(reviewed_tree),
           "original run binding does not match reviewed activation")
    return checked


def read_binding(path, *, nonce, original_run_id, reviewed_tree):
    path = Path(path)
    insist(path.is_file() and not path.is_symlink(),
           "missing or symlinked original run artifact")
    with path.open("rb") as fp:
        raw = fp.read(MAX_BINDING_BYTES + 1)
    insist(len(raw) <= MAX_BINDING_BYTES,
           "oversized original run artifact")
    try:
        def distinct(items):
            doc = {}
            for key, value in items:
                insist(key not in doc, "duplicate key in original run artifact")
                doc[key] = value
            return doc
        doc = json.loads(raw.decode("utf-8"), object_pairs_hook=distinct)
    except (ValueError, UnicodeError) as exc:
        raise ProvenanceError("invalid original run artifact") from exc
    return validate_binding(
        doc, nonce=nonce, original_run_id=original_run_id,
        reviewed_tree=reviewed_tree)


def verify_origin(client, binding):
    """GET live GitHub provenance and each target commit's workflow tree.

    A self-asserted artifact is never sufficient: it must belong to the exact
    owner-triggered, first-attempt W3 workflow run whose head GitHub attests,
    and the GitHub commit graph must reproduce its original three SHAs.
    """
    def get(endpoint):
        reply = client.request("GET", endpoint)
        insist(reply.status == 200 and isinstance(reply.data, dict),
               "authenticated GitHub origin GET failed")
        return reply.data

    origin = get("/actions/runs/" + str(binding["run_id"]))
    insist(origin.get("id") == binding["run_id"] and
           origin.get("event") == "workflow_dispatch" and
           origin.get("path") == WORKFLOW_PATH and
           origin.get("head_branch") == "main" and
           origin.get("head_sha") == binding["source_sha"] and
           type(origin.get("run_attempt")) is int and
           origin["run_attempt"] == 1 and
           isinstance(origin.get("actor"), dict) and
           origin["actor"].get("login") == "abiggerhammer" and
           isinstance(origin.get("triggering_actor"), dict) and
           origin["triggering_actor"].get("login") == "abiggerhammer" and
           isinstance(origin.get("repository"), dict) and
           origin["repository"].get("full_name") == REPO,
           "original Actions run identity or source SHA mismatched")
    def exact_child(parent_tree_sha, child_name):
        """Walk nonrecursive Git Trees; never compare the ROOT tree to .github/workflows."""
        doc = get("/git/trees/" + commit_sha(parent_tree_sha))
        insist(doc.get("sha") == parent_tree_sha and
               doc.get("truncated") is not True and
               isinstance(doc.get("tree"), list),
               "GitHub tree listing is missing/truncated")
        entries = [x for x in doc["tree"] if
                   isinstance(x, dict) and x.get("path") == child_name]
        insist(len(entries) == 1 and
               entries[0].get("type") == "tree",
               "original Git tree lacks unique reviewed directory")
        return commit_sha(entries[0].get("sha"))

    for current, next_parent in (
            (binding["source_sha"], binding["parent_sha"]),
            (binding["parent_sha"], binding["grandparent_sha"]),
            (binding["grandparent_sha"], None)):
        info = get("/git/commits/" + current)
        parents = info.get("parents")
        tree = info.get("tree")
        insist(info.get("sha") == current and
               isinstance(tree, dict) and
               isinstance(parents, list),
               "original GitHub commit or root tree missing")
        if next_parent is not None:
            insist(parents and isinstance(parents[0], dict) and
                   parents[0].get("sha") == next_parent,
                   "original GitHub first-parent ancestry changed")
        root_tree_sha = commit_sha(tree.get("sha"))
        github_tree_sha = exact_child(root_tree_sha, ".github")
        workflows_tree_sha = exact_child(github_tree_sha, "workflows")
        insist(workflows_tree_sha == binding["workflow_tree_sha"],
               "original GitHub .github/workflows subtree differs from pin")
    return binding
