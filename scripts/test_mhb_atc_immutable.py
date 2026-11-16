#!/usr/bin/env python3
"""Offline adversarial tests for dedicated-App immutable ATC admission."""
from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from mhb_atc_immutable import contract, check_ref, check_ruleset, verify_pr

A, B = "a" * 40, "b" * 40
REPO, APP, RULESET = "abiggerhammer/phil", 45321, 18450
STAGED = "hamster/staged/phase2-selfhost/candidate"


def binding():
    return contract(1845, "phase2-selfhost", STAGED, A, REPO)


def ruleset():
    return {
        "id": RULESET, "target": "branch", "source_type": "Repository",
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
            "base": {"ref": "main", "repo": {"full_name": REPO}}}


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
        self.assertEqual(verify_pr(pr(), binding())["pr"], 1847)
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
                verify_pr(test, binding())

    def test_pr_receipt_tolerates_only_trailing_newline_normalization(self):
        q = pr()
        q["body"] = q["body"].rstrip("\n")
        self.assertEqual(verify_pr(q, binding())["decision"], "immutable-pr-validated")

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
        self.assertEqual(check_ruleset(ruleset(), REPO, APP, RULESET)["decision"],
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
                check_ruleset(v, REPO, APP, RULESET)

    def test_only_one_named_app_with_always_bypass(self):
        variants = []
        r = ruleset(); r["bypass_actors"] = []; variants.append(r)
        r = ruleset(); r["bypass_actors"][0]["actor_id"] = APP + 1; variants.append(r)
        r = ruleset(); r["bypass_actors"][0]["bypass_mode"] = "pull_request"; variants.append(r)
        r = ruleset(); r["bypass_actors"].append({
            "actor_type": "RepositoryRole", "actor_id": 5, "bypass_mode": "always"
        }); variants.append(r)
        for v in variants:
            with self.subTest(rule=v), self.assertRaisesRegex(ValueError, "only"):
                check_ruleset(v, REPO, APP, RULESET)

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
