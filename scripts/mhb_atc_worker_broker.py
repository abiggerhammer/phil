#!/usr/bin/env python3
"""Pure, fail-closed W2 authorization for an operator-mediated fork-to-stage broker.

Never holds a credential or executes a worker's code. GitHub and Git mutations
belong to separately reviewed, trusted-main workflow steps.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

REPO = "abiggerhammer/phil"
APP_ID = 5836223
APP_SLUG = "phil-atc-worker"
SHA = re.compile(r"[0-9a-f]{40}\Z")
LANE = re.compile(r"[a-z][a-z0-9-]{0,39}\Z")
CANDIDATE = re.compile(r"[a-z0-9](?:[a-z0-9-]{0,62}[a-z0-9])?\Z")
LOGIN = re.compile(r"[A-Za-z0-9](?:[A-Za-z0-9-]{0,37}[A-Za-z0-9])?\Z")
REPO_NAME = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]{0,99}\Z")
PREFIX = "hamster/staged/"
SOURCE_PREFIX = "hamster/proposed/"


def deny(condition: bool, reason: str) -> None:
    if not condition:
        raise ValueError(reason)


def exact_sha(value: object, name: str) -> str:
    deny(isinstance(value, str) and bool(SHA.fullmatch(value)) and
         value != "0" * 40, f"invalid {name}")
    return value


def load_json(path: str) -> object:
    raw = Path(path).read_bytes()
    deny(len(raw) <= 8_000_000, "oversized JSON input")

    def no_duplicate_keys(pairs):
        obj = {}
        for key, value in pairs:
            deny(key not in obj, "duplicate JSON key")
            obj[key] = value
        return obj

    return json.loads(raw.decode("utf-8"), object_pairs_hook=no_duplicate_keys)


def check_worker_policy(worker: dict) -> str:
    deny(isinstance(worker, dict) and
         worker.get("schema") == "MHB-ATC-WORKER-POLICY-V1" and
         worker.get("repository") == REPO and
         type(worker.get("worker_app_id")) is int and
         worker["worker_app_id"] == APP_ID and
         worker.get("worker_app_slug") == APP_SLUG and
         worker.get("environment") == "atc-worker-broker" and
         worker.get("intended_permissions") ==
         {"contents": "write", "metadata": "read", "pull_requests": "none"} and
         worker.get("credential_holder") == "trusted-main-broker-only" and
         worker.get("direct_worker_installation_tokens") is False and
         worker.get("broker_activation") in {"disabled", "enabled"},
         "worker App identity/custody policy mismatch")
    return worker["broker_activation"]


def resolve(worker: dict, registry: dict, *, repo: str, actor: str,
            lane: str, candidate: str) -> dict:
    activation = check_worker_policy(worker)
    deny(repo == REPO, "untrusted destination repository")
    deny(isinstance(lane, str) and bool(LANE.fullmatch(lane)),
         "invalid lane")
    deny(isinstance(candidate, str) and bool(CANDIDATE.fullmatch(candidate)) and
         not candidate.endswith("-"), "invalid candidate slug")
    deny(isinstance(registry, dict) and
         registry.get("schema") == "MHB-ATC-W2-LANES-V1" and
         registry.get("repository") == REPO and
         registry.get("source_model") == "public-github-fork" and
         registry.get("pilot_only") is True, "wrong lane registry contract")
    actors = registry.get("allowed_dispatch_actors")
    deny(actors == ["abiggerhammer"] and actor == "abiggerhammer",
         "broker dispatch actor not authorized")
    lanes = registry.get("lanes")
    deny(isinstance(lanes, dict) and lane in lanes,
         "lane not registered")
    entry = lanes[lane]
    deny(isinstance(entry, dict) and entry.get("enabled") is True,
         "lane not enabled in reviewed source registry")
    src = entry.get("source_repository")
    owner = entry.get("source_owner")
    source_repository_id = entry.get("source_repository_id")
    source_owner_id = entry.get("source_owner_id")
    deny(type(source_repository_id) is int and source_repository_id > 0 and
         type(source_owner_id) is int and source_owner_id > 0,
         "numeric fork/owner identity missing from reviewed lane registry")
    deny(isinstance(src, str) and isinstance(owner, str) and
         bool(LOGIN.fullmatch(owner)) and
         src.count("/") == 1 and src.split("/")[0] == owner and
         bool(REPO_NAME.fullmatch(src.split("/")[1])) and
         src.split("/")[1] not in (".", "..") and ".." not in src and
         src != REPO, "invalid or unconfigured per-lane source fork")
    source_ref = f"{SOURCE_PREFIX}{lane}/{candidate}"
    staged = f"{PREFIX}{lane}/{candidate}"
    deny(len(staged) < 240, "overlong stage ref")
    return {"decision": "authorized-source-lookup", "repo": REPO,
            "actor": actor, "lane": lane, "candidate": candidate,
            "source_repository": src, "source_owner": owner,
            "source_repository_id": source_repository_id,
            "source_owner_id": source_owner_id,
            "source_ref": source_ref, "staged_branch": staged,
            "broker_source_activation": activation}


def validate_plan(binding: dict, *, base_sha: str, head_sha: str,
                  main_sha: str, source_repository: object,
                  source_ref: object, staged_refs: object, issues: object) -> dict:
    base = exact_sha(base_sha, "base SHA")
    head = exact_sha(head_sha, "candidate SHA")
    main = exact_sha(main_sha, "trusted main SHA")
    deny(head != base and head != main, "no candidate commit to stage")
    deny(base != main or head != main, "main/candidate relationship invalid")

    src = binding["source_repository"]
    owner = binding["source_owner"]
    deny(isinstance(source_repository, dict) and
         source_repository.get("full_name") == src and
         type(source_repository.get("id")) is int and
         source_repository["id"] == binding["source_repository_id"] and
         source_repository.get("fork") is True and
         source_repository.get("private") is False and
         isinstance(source_repository.get("parent"), dict) and
         source_repository["parent"].get("full_name") == REPO and
         isinstance(source_repository.get("owner"), dict) and
         source_repository["owner"].get("login") == owner and
         type(source_repository["owner"].get("id")) is int and
         source_repository["owner"]["id"] == binding["source_owner_id"],
         "source must be the exact public Phil fork owned by registered lane owner")
    deny(isinstance(source_ref, dict) and
         source_ref.get("ref") == "refs/heads/" + binding["source_ref"] and
         isinstance(source_ref.get("object"), dict) and
         source_ref["object"].get("type") == "commit" and
         source_ref["object"].get("sha") == head,
         "requested source commit is not the fork's live exact head")

    deny(isinstance(staged_refs, list), "missing staged-ref census")
    stage_prefix = "refs/heads/" + PREFIX + binding["lane"] + "/"
    for ref in staged_refs:
        deny(isinstance(ref, dict) and isinstance(ref.get("ref"), str),
             "malformed staged-ref census")
        if ref["ref"].startswith(stage_prefix):
            raise ValueError("lane has an existing staged ref; no ref reuse or overwrite")

    deny(isinstance(issues, list), "missing open-issue census")
    target_title_prefix = "ATC candidate: " + PREFIX + binding["lane"] + "/"
    lane_label = "lane: " + binding["lane"]
    for issue in issues:
        deny(isinstance(issue, dict) and isinstance(issue.get("title"), str) and
             isinstance(issue.get("labels"), list),
             "malformed open-issue census")
        title = issue["title"]
        labels = issue["labels"]
        deny(all(isinstance(lab, dict) and isinstance(lab.get("name"), str)
                 for lab in labels), "malformed issue labels")
        names = {lab["name"] for lab in labels}
        if title.startswith(target_title_prefix) or (
                "atc: staged" in names and lane_label in names):
            raise ValueError("lane has an existing staged candidate issue")

    return {**binding, "decision": "validated-read-only-plan",
            "base_sha": base, "head_sha": head, "main_sha": main,
            "max_candidate_commits": 100,
            "scope": "create-only staged ref; never admitted ref or PR"}


def check_paths(data: bytes) -> dict:
    """Validate NUL-separated git diff --name-only -z output (never parse lines)."""
    deny(0 < len(data) <= 1_000_000 and data.endswith(b"\0"),
         "missing/oversized or non-NUL-terminated diff path list")
    paths = data[:-1].split(b"\0")
    deny(0 < len(paths) <= 1000, "no candidate changes or too many paths")
    for raw in paths:
        deny(raw and not raw.startswith(b"/") and
             not any(x in raw for x in (b"\n", b"\r", b"\\", b"\x00")) and
             all(part not in (b"", b".", b"..") for part in raw.split(b"/")),
             "unsafe Git file path")
        lower = raw.lower()
        deny(not (lower == b".github" or lower.startswith(b".github/") or
                  lower in (b".gitmodules", b".gitattributes") or
                  lower.startswith(b"scripts/mhb_atc")),
             "untrusted proposal changes credential, workflow or ATC policy code")
    return {"decision": "candidate-paths-reviewed", "changed_files": len(paths)}


def cli() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest="command", required=True)
    for cmd in ("resolve", "plan"):
        x = sub.add_parser(cmd)
        for arg in ("worker-policy", "lane-policy", "repo", "actor", "lane", "candidate"):
            x.add_argument("--" + arg, required=True)
        if cmd == "plan":
            for arg in ("base-sha", "head-sha", "main-sha", "source-repository-json",
                        "source-ref-json", "staged-refs-json", "issues-json"):
                x.add_argument("--" + arg, required=True)
    x = sub.add_parser("paths")
    x.add_argument("--paths-file", required=True)
    args = p.parse_args()
    if args.command == "paths":
        result = check_paths(Path(args.paths_file).read_bytes())
    else:
        worker = load_json(args.worker_policy)
        registry = load_json(args.lane_policy)
        binding = resolve(worker, registry, repo=args.repo, actor=args.actor,
                          lane=args.lane, candidate=args.candidate)
        if args.command == "resolve":
            result = binding
        else:
            result = validate_plan(
                binding, base_sha=args.base_sha, head_sha=args.head_sha,
                main_sha=args.main_sha,
                source_repository=load_json(args.source_repository_json),
                source_ref=load_json(args.source_ref_json),
                staged_refs=load_json(args.staged_refs_json),
                issues=load_json(args.issues_json))
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(cli())
    except (OSError, TypeError, KeyError, ValueError, UnicodeError) as exc:
        print("MHB-ATC W2 broker denied: " + str(exc), file=sys.stderr)
        sys.exit(2)
