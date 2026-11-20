#!/usr/bin/env python3
"""Pure fail-closed W1-ID checker for App-JWT GET /app + /app/installations.

No credential generation, network request or repository mutation occurs here.
The trusted manual preflight fetches these documents using a short-lived JWT.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

REPO = "abiggerhammer/phil"
OWNER = "abiggerhammer"
OWNER_ID = 105089
APP_ID = 5836223
APP_SLUG = "phil-atc-worker"
MAX_JSON = 1_000_000
EXPECTED_PERMISSIONS = {"contents": "write", "metadata": "read"}


def deny(ok: bool, reason: str) -> None:
    if not ok:
        raise ValueError(reason)


def duplicate_keys(pairs):
    result = {}
    for key, value in pairs:
        deny(key not in result, "duplicate JSON key")
        result[key] = value
    return result


def load(path: str):
    with Path(path).open("rb") as f:
        data = f.read(MAX_JSON + 1)
    deny(len(data) <= MAX_JSON, "oversized App metadata")
    return json.loads(data.decode("utf-8"), object_pairs_hook=duplicate_keys)


def exact_permissions(raw) -> bool:
    """Absence and explicit 'none' are equivalent only for other scopes."""
    return (
        isinstance(raw, dict)
        and raw.get("contents") == "write"
        and raw.get("metadata") == "read"
        and all(value in (None, "none")
                for name, value in raw.items()
                if name not in EXPECTED_PERMISSIONS)
    )


def verified_app(app, installations, *, policy, configured_client_id):
    deny(isinstance(policy, dict) and
         policy.get("schema") == "MHB-ATC-WORKER-POLICY-V1" and
         policy.get("repository") == REPO and
         policy.get("worker_app_id") == APP_ID and
         policy.get("worker_app_slug") == APP_SLUG and
         policy.get("environment") == "atc-worker-broker" and
         policy.get("credential_holder") == "trusted-main-broker-only" and
         policy.get("broker_activation") == "disabled" and
         policy.get("intended_permissions") ==
         {"contents": "write", "metadata": "read", "pull_requests": "none"} and
         policy.get("direct_worker_installation_tokens") is False,
         "reviewed worker policy changed or active")
    deny(isinstance(configured_client_id, str) and
         configured_client_id.startswith("Iv") and
         len(configured_client_id) <= 150, "invalid worker App Client ID")
    deny(isinstance(app, dict) and
         type(app.get("id")) is int and app["id"] == APP_ID and
         app.get("slug") == APP_SLUG and
         app.get("client_id") == configured_client_id and
         isinstance(app.get("owner"), dict) and
         app["owner"].get("login") == OWNER and
         type(app["owner"].get("id")) is int and
         app["owner"]["id"] == OWNER_ID and
         exact_permissions(app.get("permissions")),
         "authenticated JWT App identity or permissions mismatch")

    deny(isinstance(installations, list) and len(installations) == 1,
         "not exactly one authenticated App installation")
    installed = installations[0]
    deny(isinstance(installed, dict) and
         type(installed.get("id")) is int and installed["id"] > 0 and
         type(installed.get("app_id")) is int and
         installed["app_id"] == APP_ID and
         installed.get("app_slug") == APP_SLUG and
         installed.get("repository_selection") == "selected" and
         installed.get("suspended_at") is None and
         installed.get("target_type") == "User" and
         type(installed.get("target_id")) is int and
         installed["target_id"] == OWNER_ID and
         isinstance(installed.get("account"), dict) and
         installed["account"].get("login") == OWNER and
         type(installed["account"].get("id")) is int and
         installed["account"]["id"] == OWNER_ID and
         exact_permissions(installed.get("permissions")),
         "authenticated App installation identity, audience policy or grant mismatch")

    # This receipt is public nonsecret metadata. Installation selection='selected'
    # does NOT prove that every selected repo is Phil: the existing token-scoped
    # GET /installation/repositories independently checks the minted token.
    return {
        "decision": "authenticated-worker-app-and-installation",
        "app_id": APP_ID,
        "app_slug": APP_SLUG,
        "installation_id": installed["id"],
        "repository_selection": "selected",
        "permissions": EXPECTED_PERMISSIONS,
        "w1_id": "authenticated-by-GitHub-App-JWT",
        "unproved": "all selected installation repositories; effective protected-ref/PR denials",
    }


def cli():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--app-json", required=True)
    p.add_argument("--installations-json", required=True)
    p.add_argument("--worker-policy", required=True)
    p.add_argument("--configured-client-id", required=True)
    args = p.parse_args()

    decision = verified_app(
        load(args.app_json), load(args.installations_json),
        policy=load(args.worker_policy),
        configured_client_id=args.configured_client_id)
    print(json.dumps(decision, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(cli())
    except (OSError, ValueError, TypeError, KeyError, UnicodeError) as exc:
        print("MHB-ATC W1-ID denied: " + str(exc), file=sys.stderr)
        sys.exit(2)
