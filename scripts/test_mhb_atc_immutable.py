#!/usr/bin/env python3
"""Offline adversarial tests for dedicated-App immutable ATC admission."""
from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from mhb_atc_immutable import (contract, check_ref, check_ruleset,
                              verify_pr, verified_publisher)

A, B = "a" * 40, "b" * 40
REPO, APP, RULESET = "abiggerhammer/phil", 45321, 18450
STAGED = "hamster/staged/phase2-selfhost/candidate"
PUBLISHER = {"app_id": APP, "app_slug": "test-publisher",
             "bot_login": "test-publisher[bot]", "bot_id": 71234}
CREATED = "2026-11-16T10:00:00Z"
UPDATED = "2026-11-16T10:10:00Z"


def policy():
    return {"format": "MHB-ATC-OWNER-RULESET-ATTESTATION-V1",
            "repository": REPO, "ruleset_id": RULESET,
            "publisher_app_id": APP,
            "publisher_app_slug": "test-publisher",
            "ruleset_created_at": CREATED, "ruleset_updated_at": UPDATED,
            "attested_bypass_actors": [{"actor_type": "Integration",
                                        "actor_id": APP, "bypass_mode": "always"}]}



def binding():
    return contract(1845, "phase2-selfhost", STAGED, A, REPO)


def ruleset():
    return {
        "id": RULESET, "target": "branch", "source_type": "Repository",
        "created_at": CREATED, "updated_at": UPDATED,
        "source": REPO, "enforcement": "active",
        "conditions": {"ref_name": {
            "include": ["refs/heads/hamster/admitted/*"], "exclude": []}},
        "rules": [{"type": kind} for kind in
                  ("creation", "update", "deletion", "non_fast_forward")],
        "bypass_actors": [{"actor_type": "Integration", "actor_id": APP,
                           "bypass_mode": "always"}],
    }


def ref(sha=A):
    return {"ref": "refs/heads/" + binding()["admitted_branch"],
            "object": {"sha": sha}}


def pr():
    b = binding()
    return {"number": 1847, "state": "open",
            "title": b["title"], "body": b["body"],
            "head": {"ref": b["admitted_branch"], "sha": A,
                     "repo": {"full_name": REPO}},
            "base": {"ref": "main", "repo": {"full_name": REPO}},
            "user": {"login": PUBLISHER["bot_login"],
                     "id": PUBLISHER["bot_id"], "type": "Bot"}}


class ImmutablePublisherTests(unittest.TestCase):
    def test_canonical_ref_has_exact_single_segment(self):
        b = binding()
        self.assertEqual(b["admitted_branch"],
                         "hamster/admitted/atc-1845-phase2-selfhost-" + A)
        self.assertEqual(b["admitted_branch"].count("/"), 2)
        for part in ("Candidate issue: #1845",
                     "- Staged branch: " + STAGED,
                     "- Admitted branch: " + b["admitted_branch"],
                     "- Exact registered head: " + A,
                     "- Base repository: " + REPO,
                     "- Publisher: dedicated MHB-ATC GitHub App"):
            self.assertIn(part, b["body"])

    def test_reject_malformed_canonical_identity(self):
        cases = [
            (0, "phase2-selfhost", STAGED, A, REPO),
            (1845, "phase2-embedded", STAGED, A, REPO),
            (1845, "phase2-selfhost", STAGED, B[:-1], REPO),
            (1845, "phase2-selfhost", "evil/staged/branch", A, REPO),
            (1845, "phase2-selfhost", STAGED, A, "not/a/repo"),
        ]
        for args in cases:
            with self.subTest(args=args), self.assertRaises(ValueError):
                contract(*args)

    def test_immutable_pr_exact_binding_and_receipt(self):
        self.assertEqual(verify_pr(pr(), binding(), PUBLISHER)["pr"], 1847)
        for mutate in (
            lambda x: x["head"].update(ref=STAGED),
            lambda x: x["head"].update(sha=B),
            lambda x: x["base"].update(ref="release"),
            lambda x: x["head"]["repo"].update(full_name="other/fork"),
            lambda x: x.update(body=x["body"].replace(A, B)),
            lambda x: x.update(title="tampered"),
            lambda x: x.update(number=0),
        ):
            test = pr()
            mutate(test)
            with self.subTest(pr=test), self.assertRaises(ValueError):
                verify_pr(test, binding(), PUBLISHER)

    def test_pr_receipt_tolerates_only_trailing_newline_normalization(self):
        q = pr()
        q["body"] = q["body"].rstrip("\n")
        self.assertEqual(verify_pr(q, binding(), PUBLISHER)["decision"], "immutable-pr-validated")

    def test_preexisting_ref_and_drift_fail_closed(self):
        with self.assertRaisesRegex(ValueError, "already exists"):
            check_ref([ref()], binding(), "absent")
        with self.assertRaisesRegex(ValueError, "drifted"):
            check_ref([ref(B)], binding(), "present")
        with self.assertRaisesRegex(ValueError, "missing"):
            check_ref([], binding(), "present")
        self.assertEqual(check_ref([], binding(), "absent")["state"], "absent")
        self.assertEqual(check_ref([ref()], binding(), "present")["state"], "present")

    def test_missing_ref_snapshot_not_equivalent_to_no_refs(self):
        with self.assertRaises(ValueError):
            check_ref(None, binding(), "absent")
        with self.assertRaises(ValueError):
            check_ref([{"ref": "refs/heads/" + binding()["admitted_branch"]}],
                      binding(), "present")

    def test_app_ruleset_validated_before_any_ref_creation(self):
        self.assertEqual(check_ruleset(ruleset(), REPO, APP, RULESET, policy())["decision"],
                         "ruleset-preflight-valid")

    def test_inactive_wrong_scope_or_wrong_rules_are_rejected(self):
        variants = []
        r = ruleset(); r["enforcement"] = "evaluate"; variants.append(r)
        r = ruleset(); r["source"] = "other/repo"; variants.append(r)
        r = ruleset(); r["conditions"]["ref_name"]["include"] = [
            "refs/heads/hamster/**"]; variants.append(r)
        r = ruleset(); r["conditions"]["ref_name"]["exclude"] = ["main"]; variants.append(r)
        r = ruleset(); r["rules"] = [{"type": "deletion"}]; variants.append(r)
        r = ruleset(); r["target"] = "tag"; variants.append(r)
        for v in variants:
            with self.subTest(rule=v), self.assertRaises(ValueError):
                check_ruleset(v, REPO, APP, RULESET, policy())

    def test_only_one_named_app_with_always_bypass(self):
        variants = []
        r = ruleset(); r["bypass_actors"] = []; variants.append(r)
        r = ruleset(); r["bypass_actors"][0]["actor_id"] = APP + 1; variants.append(r)
        r = ruleset(); r["bypass_actors"][0]["bypass_mode"] = "pull_request"; variants.append(r)
        r = ruleset(); r["bypass_actors"].append({
            "actor_type": "RepositoryRole", "actor_id": 5, "bypass_mode": "always"
        }); variants.append(r)
        for v in variants:
            with self.subTest(rule=v), self.assertRaisesRegex(ValueError, "conflicts"):
                check_ruleset(v, REPO, APP, RULESET, policy())

    def test_f1_redacted_bypass_requires_exact_owner_version(self):
        r = ruleset()
        r.pop("bypass_actors")
        result = check_ruleset(r, REPO, APP, RULESET, policy())
        self.assertEqual(result["evidence"], "redacted-live-plus-pinned-owner-version")
        r["updated_at"] = "2026-11-16T10:11:00Z"
        with self.assertRaisesRegex(ValueError, "version"):
            check_ruleset(r, REPO, APP, RULESET, policy())
        r["updated_at"] = UPDATED
        r.pop("created_at")
        with self.assertRaisesRegex(ValueError, "version"):
            check_ruleset(r, REPO, APP, RULESET, policy())

    def test_f1_malformed_attestation_or_broad_live_bypass_denied(self):
        r = ruleset()
        for wrong in (
            {**policy(), "publisher_app_id": APP + 1},
            {**policy(), "attested_bypass_actors": []},
            {**policy(), "ruleset_id": RULESET + 1},
        ):
            with self.subTest(policy=wrong), self.assertRaises(ValueError):
                check_ruleset(r, REPO, APP, RULESET, wrong)
        r["bypass_actors"].append({"actor_type": "User", "actor_id": 1,
                                   "bypass_mode": "always"})
        with self.assertRaisesRegex(ValueError, "bypass"):
            check_ruleset(r, REPO, APP, RULESET, policy())

    def test_f3_github_app_and_bot_identity_are_authenticated(self):
        identity = verified_publisher(
            {"id": APP, "slug": "test-publisher"},
            {"id": 71234, "login": "test-publisher[bot]", "type": "Bot"},
            "test-publisher", APP, policy())
        self.assertEqual(identity, PUBLISHER)
        # Private GitHub Apps return 403 from public /apps/{slug};
        # the owner-reviewed slug/ID pin plus real bot profile must suffice.
        self.assertEqual(verified_publisher(
            None,
            {"id": 71234, "login": "test-publisher[bot]", "type": "Bot"},
            "test-publisher", APP, policy()), PUBLISHER)
        with self.assertRaisesRegex(ValueError, "source-reviewed"):
            verified_publisher(
                None,
                {"id": 71234, "login": "wrong[bot]", "type": "Bot"},
                "wrong", APP, policy())
        for app, bot in (
            ({"id": APP + 1, "slug": "test-publisher"},
             {"id": 71234, "login": "test-publisher[bot]", "type": "Bot"}),
            ({"id": APP, "slug": "test-publisher"},
             {"id": 71234, "login": "foreign[bot]", "type": "Bot"}),
            ({"id": APP, "slug": "test-publisher"},
             {"id": 71234, "login": "test-publisher[bot]", "type": "User"}),
        ):
            with self.subTest(app=app, bot=bot), self.assertRaises(ValueError):
                verified_publisher(app, bot, "test-publisher", APP, policy())

    def test_f3_copied_receipt_never_authenticates_foreign_app(self):
        for change in (
            lambda x: x["user"].update(login="foreign[bot]"),
            lambda x: x["user"].update(id=999999),
            lambda x: x["user"].update(type="User"),
            lambda x: x.update(user=None),
            lambda x: x.update(performed_via_github_app={"id": APP + 1}),
        ):
            x = pr()
            change(x)
            with self.subTest(pr=x), self.assertRaisesRegex(ValueError, "publisher|attribution"):
                verify_pr(x, binding(), PUBLISHER)

    def test_workflow_contains_no_personal_token_publish_fallback(self):
        wf = (Path(__file__).resolve().parents[1] /
              ".github/workflows/mhb-atc-admit.yml").read_text(encoding="utf-8")
        self.assertNotIn("HAMSTER_PR_TOKEN", wf)
        self.assertIn("uses: actions/create-github-app-token@64ab729a6294000f5aa4a4bc0b73d1f32bc45510 # v3", wf)
        self.assertIn("vars.MHB_ATC_IMMUTABLE_HEADS_ENABLED == 'true'", wf)
        self.assertIn("MHB_ATC_PUBLISHER_RULESET_ID", wf)
        self.assertIn("repos/$GH_REPO/git/refs", wf)
        self.assertNotIn("git/refs/heads/$admitted -X PATCH", wf)
        self.assertIn("--expect absent", wf)
        self.assertIn("--expect present", wf)


if __name__ == "__main__":
    unittest.main()
