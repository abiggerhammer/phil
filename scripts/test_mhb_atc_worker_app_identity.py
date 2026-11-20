#!/usr/bin/env python3
"""W1-ID negative source and literal JWT transport replays. No GitHub network."""
from __future__ import annotations

import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import textwrap
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from mhb_atc_worker_app_identity import (
    APP_ID, APP_SLUG, OWNER_ID, verified_app, load
)

POLICY = ROOT / ".github/atc-worker-policy.json"
WORKFLOW = ROOT / ".github/workflows/mhb-atc-worker-token-preflight.yml"
CLIENT_ID = "Iv1.synthetic-example"


def fixtures():
    app = {
        "id": APP_ID, "slug": APP_SLUG, "client_id": CLIENT_ID,
        "owner": {"login": "abiggerhammer", "id": OWNER_ID},
        "permissions": {"metadata": "read", "contents": "write"},
    }
    installed = [{
        "id": 4567, "app_id": APP_ID, "app_slug": APP_SLUG,
        "account": {"login": "abiggerhammer", "id": OWNER_ID},
        "target_type": "User", "target_id": OWNER_ID,
        "repository_selection": "selected", "suspended_at": None,
        "permissions": {"metadata": "read", "contents": "write"},
    }]
    return app, installed, json.loads(POLICY.read_text())


def check(app, installations, policy, client_id=CLIENT_ID):
    return verified_app(app, installations, policy=policy,
                        configured_client_id=client_id)


class WorkerAppIdTests(unittest.TestCase):
    def test_jwt_authenticated_app_and_installation_receipt(self):
        app, installed, policy = fixtures()
        receipt = check(app, installed, policy)
        self.assertEqual(receipt["decision"],
                         "authenticated-worker-app-and-installation")
        self.assertEqual(receipt["app_id"], APP_ID)
        self.assertEqual(receipt["installation_id"], 4567)
        self.assertNotIn(CLIENT_ID, json.dumps(receipt))
        self.assertIn("unproved", receipt)

    def test_actual_app_id_slug_owner_and_client_binding(self):
        mutations = [
            lambda a: a.update(id=456),
            lambda a: a.update(slug="phil-atc-publisher"),
            lambda a: a.update(client_id="Iv1.wrong"),
            lambda a: a["owner"].update(login="attacker"),
            lambda a: a["owner"].update(id=1),
            lambda a: a["permissions"].update(pull_requests="read"),
            lambda a: a["permissions"].update(actions="write"),
            lambda a: a["permissions"].update(contents="read"),
            lambda a: a["permissions"].update(metadata="none"),
        ]
        for i, mutate in enumerate(mutations):
            app, installed, policy = fixtures()
            mutate(app)
            with self.subTest(case=i), self.assertRaises(ValueError):
                check(app, installed, policy)

    def test_underlying_installation_exactness_and_scope(self):
        mutations = [
            lambda a: a.append(copy.deepcopy(a[0])),
            lambda a: a.clear(),
            lambda a: a[0].update(app_id=7),
            lambda a: a[0].update(app_slug="phil-atc-publisher"),
            lambda a: a[0].update(repository_selection="all"),
            lambda a: a[0].update(suspended_at="2026-11-20T00:00:00Z"),
            lambda a: a[0].update(target_type="Organization"),
            lambda a: a[0].update(target_id=1),
            lambda a: a[0]["account"].update(login="attacker"),
            lambda a: a[0]["permissions"].update(issues="read"),
            lambda a: a[0]["permissions"].update(contents="read"),
        ]
        for i, mutate in enumerate(mutations):
            app, installed, policy = fixtures()
            mutate(installed)
            with self.subTest(case=i), self.assertRaises(ValueError):
                check(app, installed, policy)

    def test_policy_mutation_or_activation_denied(self):
        for key, value in [
            ("broker_activation", "enabled"),
            ("worker_app_id", 123),
            ("worker_app_slug", "wrong"),
            ("environment", "atc-publisher"),
            ("credential_holder", "hamster"),
            ("direct_worker_installation_tokens", True),
            ("intended_permissions", {"contents": "write", "pull_requests": "write"}),
        ]:
            app, installed, policy = fixtures()
            policy[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                check(app, installed, policy)

    def test_oversized_and_duplicate_json_inputs_denied(self):
        with tempfile.TemporaryDirectory() as d:
            file = Path(d) / "json"
            file.write_text('{"id":5836223,"id":456}')
            with self.assertRaisesRegex(ValueError, "duplicate JSON key"):
                load(str(file))
            with file.open("wb") as f:
                f.truncate(1_000_001)
            with self.assertRaisesRegex(ValueError, "oversized"):
                load(str(file))

    def test_manual_owner_gate_and_token_custody_unchanged(self):
        src = WORKFLOW.read_text()
        for value in ("github.event_name == 'workflow_dispatch'",
                      "github.ref == 'refs/heads/main'",
                      "github.actor == 'abiggerhammer'",
                      "environment: atc-worker-broker",
                      "persist-credentials: false",
                      "permissions:\n  contents: read\n",
                      "trap cleanup EXIT", "set +x"):
            self.assertIn(value, src)
        for forbidden in ("\n  push:", "\n  pull_request:",
                          "skip-token-revoke: true", "gh pr create", "git push"):
            self.assertNotIn(forbidden, src)
        jwt_step = src.index("Authenticate worker App numeric ID")
        mint_step = src.index("Mint repository-scoped worker App token")
        verify_step = src.index("Verify authenticated worker identity")
        self.assertLess(jwt_step, mint_step)
        self.assertLess(mint_step, verify_step)
        self.assertIn('"https://api.github.com/app"', src[jwt_step:mint_step])
        self.assertIn('"https://api.github.com/app/installations?per_page=100&page=1"',
                      src[jwt_step:mint_step])
        self.assertIn('"$RUNNER_TEMP/atc-w1id-receipt.json"', src[verify_step:])

    def test_literal_jwt_step_mock_curl_real_rsa_signing(self):
        src = WORKFLOW.read_text()
        begin = src.index("          set -euo pipefail",
                          src.index("Authenticate worker App numeric ID"))
        end = src.index("      - name: Mint repository-scoped worker App token", begin)
        script = textwrap.dedent(src[begin:end])
        with tempfile.TemporaryDirectory() as temp:
            d = Path(temp)
            rsa = d / "test-private.pem"
            p = subprocess.run(["openssl", "genpkey", "-algorithm", "RSA",
                                "-pkeyopt", "rsa_keygen_bits:2048",
                                "-out", str(rsa)],
                               capture_output=True, text=True)
            self.assertEqual(p.returncode, 0, p.stderr)
            app, installs, _ = fixtures()
            (d / "app.json").write_text(json.dumps(app))
            (d / "installs.json").write_text(json.dumps(installs))
            mock = textwrap.dedent(r'''
                curl() {
                  grep -Eq '^Authorization: Bearer [A-Za-z0-9_-]+\.[A-Za-z0-9_-]+\.[A-Za-z0-9_-]+$' "$RUNNER_TEMP/atc-w1id-auth-header.txt" || return 65
                  last=""
                  for arg in "$@"; do last="$arg"; done
                  case "$last" in
                    https://api.github.com/app) cat "$MOCK_APP" ;;
                    https://api.github.com/app/installations*) cat "$MOCK_INSTALLATIONS" ;;
                    *) return 66 ;;
                  esac
                }
            ''')
            env = dict(os.environ, APP_PRIVATE_KEY=rsa.read_text(),
                       APP_CLIENT_ID=CLIENT_ID, RUNNER_TEMP=str(d),
                       GITHUB_STEP_SUMMARY=str(d / "summary"),
                       MOCK_APP=str(d / "app.json"),
                       MOCK_INSTALLATIONS=str(d / "installs.json"))
            result = subprocess.run(["bash", "-c", mock + "\n" + script],
                                    cwd=ROOT, env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            receipt = json.loads((d / "atc-w1id-receipt.json").read_text())
            self.assertEqual(receipt["installation_id"], 4567)
            for name in ("atc-w1id-key.pem", "atc-w1id-app.json",
                         "atc-w1id-installations.json", "atc-w1id-auth-header.txt"):
                self.assertFalse((d / name).exists())
            self.assertNotIn("PRIVATE KEY", result.stdout + result.stderr)
            self.assertNotIn(CLIENT_ID, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
