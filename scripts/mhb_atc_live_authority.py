#!/usr/bin/env python3
"""Owner-local, read-only live GitHub settings attestation for MHB-ATC.

Run ONLY on a maintainer workstation with the maintainer's gh login.
Never runs in Actions, accesses secret values, mints tokens, or writes refs.
Outputs only a bounded, redacted pass/block ledger; incomplete data BLOCKS.
"""
from __future__ import annotations

import datetime as dt
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
REPO = "abiggerhammer/phil"
OWNER = "abiggerhammer"
OWNER_ID = 105089
APP_SLUG = "phil-atc-worker"
APP_ID = 5836223
MAX_RESPONSE = 2_000_000

APPLE_KEYS = frozenset({
    "APPLE_DEVELOPER_ID_P12_BASE64",
    "APPLE_DEVELOPER_ID_P12_PASSWORD",
    "APPLE_TEAM_ID",
    "APPLE_NOTARY_KEY_P8_BASE64",
    "APPLE_NOTARY_KEY_ID",
    "APPLE_NOTARY_ISSUER_ID",
})
WORKER_KEY = "MHB_ATC_WORKER_APP_PRIVATE_KEY"
PUBLISHER_KEY = "MHB_ATC_PUBLISHER_APP_PRIVATE_KEY"
ACTIVATION_FLAGS = frozenset({
    "MHB_ATC_WORKER_BROKER_ENABLED",
    "MHB_ATC_AUTO_ADMIT_ENABLED",
    "MHB_ATC_IMMUTABLE_HEADS_ENABLED",
    "MHB_ATC_PHASE2_STAGE_BRIDGE_ENABLED",
})
ENDPOINTS = {
    "actor": "user",
    "main_before": f"repos/{REPO}/git/ref/heads/main",
    "default_token": f"repos/{REPO}/actions/permissions/workflow",
    "variables": f"repos/{REPO}/actions/variables?per_page=100",
    "repository_secrets": f"repos/{REPO}/actions/secrets?per_page=100",
    "macos_environment": f"repos/{REPO}/environments/macos-release",
    "macos_branch_policies":
        f"repos/{REPO}/environments/macos-release/deployment-branch-policies?per_page=100",
    "macos_secrets": f"repos/{REPO}/environments/macos-release/secrets?per_page=100",
    "broker_environment": f"repos/{REPO}/environments/atc-worker-broker",
    "broker_branch_policies":
        f"repos/{REPO}/environments/atc-worker-broker/deployment-branch-policies?per_page=100",
    "broker_secrets": f"repos/{REPO}/environments/atc-worker-broker/secrets?per_page=100",
    "publisher_environment": f"repos/{REPO}/environments/atc-publisher",
    "publisher_branch_policies":
        f"repos/{REPO}/environments/atc-publisher/deployment-branch-policies?per_page=100",
    "publisher_secrets": f"repos/{REPO}/environments/atc-publisher/secrets?per_page=100",
    # Public metadata only; a private App may return 404. JWT GET /app and
    # signed installation authorization remain separate W1-ID evidence.
    "app_public": f"apps/{APP_SLUG}",
}


def no_duplicate_keys(pairs):
    out = {}
    for key, value in pairs:
        if key in out:
            raise ValueError("ambiguous duplicate JSON key")
        out[key] = value
    return out


def read_json(raw: str):
    if len(raw.encode("utf-8")) > MAX_RESPONSE:
        raise ValueError("oversized API response")
    return json.loads(raw, object_pairs_hook=no_duplicate_keys)


def complete_items(doc, field):
    """Only one fully enumerated API page is accepted; never truncate."""
    if not isinstance(doc, dict):
        return None
    items, n = doc.get(field), doc.get("total_count")
    if not isinstance(n, int) or isinstance(n, bool) or not 0 <= n <= 100:
        return None
    if not isinstance(items, list) or len(items) != n:
        return None
    return items


def secret_names(doc):
    items = complete_items(doc, "secrets")
    if items is None:
        return None
    names = [x.get("name") for x in items if isinstance(x, dict)]
    if len(names) != len(items) or any(not isinstance(x, str) for x in names):
        return None
    if len(set(names)) != len(names):
        return None
    return set(names)


def branches_exact_main(env, policies):
    if not isinstance(env, dict) or not isinstance(policies, dict):
        return False
    branch_policy = env.get("deployment_branch_policy")
    if branch_policy != {"protected_branches": False, "custom_branch_policies": True}:
        return False
    rules = env.get("protection_rules")
    if not isinstance(rules, list) or not any(
            isinstance(x, dict) and x.get("type") == "branch_policy" for x in rules):
        return False
    paths = complete_items(policies, "branch_policies")
    if paths is None or len(paths) != 1 or not isinstance(paths[0], dict):
        return False
    return (paths[0].get("name") == "main" and
            paths[0].get("type", "branch") == "branch")


def reviewers_required(env):
    if not isinstance(env, dict):
        return False
    rules = env.get("protection_rules")
    return isinstance(rules, list) and any(
        isinstance(rule, dict) and rule.get("type") == "required_reviewers"
        and isinstance(rule.get("reviewers"), list) and len(rule["reviewers"]) > 0
        for rule in rules)


def public_app_metadata_sound(doc):
    if not isinstance(doc, dict):
        return False
    if doc.get("id") != APP_ID or doc.get("slug") != APP_SLUG:
        return False
    if not isinstance(doc.get("owner"), dict) or (
            doc["owner"].get("login") != OWNER or doc["owner"].get("id") != OWNER_ID):
        return False
    perms = doc.get("permissions")
    return (isinstance(perms, dict) and
            perms.get("contents") == "write" and
            perms.get("metadata") == "read" and
            all(value in ("none", None) for key, value in perms.items()
                if key not in ("contents", "metadata")))


def audit_snapshot(raw):
    """Pure source-policy checks; never claim owner auth from a fixture."""
    if not isinstance(raw, dict):
        raise ValueError("missing snapshot")
    policy = read_json((ROOT / ".github/atc-worker-policy.json").read_text())
    lanes = read_json((ROOT / ".github/atc-worker-lanes.json").read_text())
    checks = {}

    def put(label, condition):
        checks[label] = "PASS" if condition else "BLOCKED"

    put("reviewed_source_dormant",
        policy.get("broker_activation") == "disabled"
        and policy.get("worker_app_id") == APP_ID
        and policy.get("worker_app_slug") == APP_SLUG
        and isinstance(lanes.get("lanes"), dict)
        and len(lanes["lanes"]) == 2
        and all(isinstance(x, dict) and x.get("enabled") is False
                and x.get("source_repository") is None
                for x in lanes["lanes"].values()))

    actor = raw.get("actor")
    put("maintainer_principal",
        isinstance(actor, dict) and actor.get("login") == OWNER
        and actor.get("id") == OWNER_ID and actor.get("type") == "User")
    before, after = raw.get("main_before"), raw.get("main_after")
    sha = before.get("object", {}).get("sha") if isinstance(before, dict) else None
    put("stable_exact_main",
        isinstance(sha, str) and bool(re.fullmatch(r"[0-9a-f]{40}", sha))
        and isinstance(after, dict)
        and after.get("object", {}).get("sha") == sha
        and raw.get("checkout_sha") == sha
        and raw.get("checkout_branch") == "main")

    default = raw.get("default_token")
    put("default_actions_token_read_only",
        isinstance(default, dict)
        and default.get("default_workflow_permissions") == "read"
        and default.get("can_approve_pull_request_reviews") is False)

    variables = complete_items(raw.get("variables"), "variables")
    values = {}
    if variables is not None:
        for x in variables:
            if not isinstance(x, dict) or not isinstance(x.get("name"), str) or (
                    not isinstance(x.get("value"), str)):
                variables = None
                break
            if x["name"] in values:
                variables = None
                break
            values[x["name"]] = x["value"]
    put("worker_app_variables_and_disabled_switches",
        variables is not None and
        values.get("MHB_ATC_WORKER_APP_ID") == str(APP_ID)
        and values.get("MHB_ATC_WORKER_APP_SLUG") == APP_SLUG
        and bool(values.get("MHB_ATC_WORKER_APP_CLIENT_ID"))
        and all(values.get(name, "").strip().lower() != "true"
                for name in ACTIVATION_FLAGS))

    environments = [
        ("macos", "macos-release"),
        ("broker", "atc-worker-broker"),
        ("publisher", "atc-publisher"),
    ]
    for short, name in environments:
        env = raw.get(short + "_environment")
        paths = raw.get(short + "_branch_policies")
        put(short + "_environment_exact_main",
            isinstance(env, dict) and env.get("name") == name
            and branches_exact_main(env, paths))

    put("macos_release_required_reviewers",
        reviewers_required(raw.get("macos_environment")))

    repo_keys = secret_names(raw.get("repository_secrets"))
    macos_keys = secret_names(raw.get("macos_secrets"))
    broker_keys = secret_names(raw.get("broker_secrets"))
    publisher_keys = secret_names(raw.get("publisher_secrets"))
    reserved = APPLE_KEYS | {WORKER_KEY, PUBLISHER_KEY}
    put("no_repository_wide_sensitive_secrets",
        repo_keys is not None and repo_keys.isdisjoint(reserved))
    put("apple_secrets_isolated_to_macos",
        macos_keys is not None and APPLE_KEYS <= macos_keys
        and WORKER_KEY not in macos_keys and PUBLISHER_KEY not in macos_keys)
    put("worker_key_only_in_broker_environment",
        broker_keys is not None and WORKER_KEY in broker_keys
        and PUBLISHER_KEY not in broker_keys
        and broker_keys.isdisjoint(APPLE_KEYS))
    put("publisher_key_only_in_publisher_environment",
        publisher_keys is not None and PUBLISHER_KEY in publisher_keys
        and WORKER_KEY not in publisher_keys
        and publisher_keys.isdisjoint(APPLE_KEYS))

    # Public App metadata is distinct from authenticated /app and installation
    # evidence. Never use this to certify W1-ID on its own.
    put("public_app_metadata_correspondence",
        public_app_metadata_sound(raw.get("app_public")))

    return {
        "schema": "MHB-ATC-OWNER-SETTINGS-AUDIT-V1",
        "repository": REPO,
        "source_head_sha": sha if checks["stable_exact_main"] == "PASS" else None,
        "checks": checks,
        "decision": "PASS_SOURCE_SETTINGS" if all(x == "PASS" for x in checks.values())
                    else "BLOCKED_INCOMPLETE_OR_UNSAFE",
        "scope": "Owner-local REST metadata only; no secret values, App JWT, W3 writes or admitted PR",
        "w1_id_authenticated_by_app_jwt": False,
        "w3_negative_write_commissioned": False,
    }


def live_api(endpoint: str):
    # This CLI is intentionally local-only. gh gets its credential from the
    # logged-in maintainer's credential store; it is never printed or copied.
    clean_env = dict(os.environ)
    clean_env.pop("GH_DEBUG", None)
    clean_env["GH_PROMPT_DISABLED"] = "1"
    proc = subprocess.run(["gh", "api", "--method", "GET", endpoint],
                          cwd=ROOT, env=clean_env, capture_output=True,
                          text=True, timeout=30, check=False)
    if proc.returncode:
        return {"_unavailable": True}
    try:
        return read_json(proc.stdout)
    except (UnicodeError, ValueError, json.JSONDecodeError):
        return {"_unavailable": True}


def local_git(*args):
    proc = subprocess.run(["git", *args], cwd=ROOT, capture_output=True,
                          text=True, timeout=10, check=False)
    return proc.stdout.strip() if proc.returncode == 0 else ""


def main():
    if os.environ.get("GITHUB_ACTIONS", "").lower() == "true":
        print("Refusing live owner-settings capture inside GitHub Actions", file=sys.stderr)
        return 2
    if local_git("branch", "--show-current") != "main":
        print("Run from a checked-out main branch on the maintainer workstation",
              file=sys.stderr)
        return 2

    snapshot = {"checkout_branch": "main",
                "checkout_sha": local_git("rev-parse", "HEAD")}
    for name, endpoint in ENDPOINTS.items():
        snapshot[name] = live_api(endpoint)
    snapshot["main_after"] = live_api(ENDPOINTS["main_before"])
    report = audit_snapshot(snapshot)
    report["collected_at_utc"] = dt.datetime.now(dt.timezone.utc).isoformat()
    print(json.dumps(report, sort_keys=True, indent=2))
    return 0 if report["decision"] == "PASS_SOURCE_SETTINGS" else 2


if __name__ == "__main__":
    sys.exit(main())
