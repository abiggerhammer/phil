#!/usr/bin/env python3
"""Adversarial complete-namespace PR, closed-history and orphan replays."""
from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from mhb_atc_stage import parse_intent
from mhb_atc_immutable import contract
from mhb_atc_inventory import validate_inventory, enumerate_refs

REPO = "abiggerhammer/phil"
A, B = "a" * 40, "b" * 40
BRANCH = "hamster/staged/mhb-atc/first"
OTHER = "hamster/staged/stdlib/second"
PUBLISHER = {"app_id": 5782193, "app_slug": "publisher-test",
             "bot_login": "publisher-test[bot]", "bot_id": 10451}


def issue(n=1701, branch=BRANCH, sha=A, state="open", label="atc: admitting"):
    parsed = parse_intent(branch, sha, sha)
    labels = [{"name": "lane: " + parsed["lane"]}]
    if label is not None:
        labels.append({"name": label})
    return {"state": state, "number": n,
            "title": parsed["title"], "body": parsed["body"],
            "user": {"login": "github-actions[bot]"}, "labels": labels}


def ref(n=1701, branch=BRANCH, sha=A):
    lane = branch.split("/")[2]
    bind = contract(n, lane, branch, sha, REPO)
    return {"ref": "refs/heads/" + bind["admitted_branch"],
            "object": {"sha": sha}}


def pr(n=1702, issue_n=1701, branch=BRANCH, sha=A, state="open"):
    lane = branch.split("/")[2]
    bind = contract(issue_n, lane, branch, sha, REPO)
    return {"number": n, "state": state,
            "title": bind["title"], "body": bind["body"],
            "head": {"ref": bind["admitted_branch"], "sha": sha,
                     "repo": {"full_name": REPO}},
            "base": {"ref": "main", "repo": {"full_name": REPO}},
            "user": {"login": PUBLISHER["bot_login"],
                     "id": PUBLISHER["bot_id"], "type": "Bot"}}


def check(refs, issues, prs):
    return validate_inventory(refs, issues, prs, REPO, PUBLISHER)


class InventoryTests(unittest.TestCase):
    def test_empty_namespace_is_verified_clear(self):
        x = check([], [], [])
        self.assertTrue(x["admission_clear"])
        self.assertEqual(x["total_refs"], 0)

    def test_authenticated_active_ref_holds_next_admission(self):
        x = check([ref()], [issue()], [pr()])
        self.assertFalse(x["admission_clear"])
        self.assertEqual(x["active_refs"][0]["issue"], 1701)

    def test_positive_closed_ref_with_closed_issue_and_pr_is_history(self):
        x = check([ref()], [issue(state="closed", label=None)],
                  [pr(state="closed")])
        self.assertTrue(x["admission_clear"])
        self.assertEqual(x["closed_history"][0]["issue"], 1701)

    def test_closed_history_plus_one_valid_live_ref_still_holds(self):
        x = check([ref(1701, BRANCH, A), ref(1703, OTHER, B)],
                  [issue(1701, BRANCH, A, "closed", None),
                   issue(1703, OTHER, B, "open", "atc: admitted")],
                  [pr(1702, 1701, BRANCH, A, "closed"),
                   pr(1704, 1703, OTHER, B, "open")])
        self.assertFalse(x["admission_clear"])
        self.assertEqual(len(x["closed_history"]), 1)
        self.assertEqual(len(x["active_refs"]), 1)

    def test_f2_issue_body_tamper_a_to_b_cannot_requeue_orphan(self):
        with self.assertRaisesRegex(ValueError, "disagrees"):
            check([ref(1701, BRANCH, A)],
                  [issue(1701, BRANCH, B, "open", "atc: admitting")], [])

    def test_f2_orphan_ref_cannot_hide_if_issue_loses_all_labels(self):
        with self.assertRaisesRegex(ValueError, "orphan"):
            check([ref()], [issue(label=None)], [])

    def test_f2_orphan_ref_cannot_hide_if_issue_closed(self):
        with self.assertRaisesRegex(ValueError, "orphan"):
            check([ref()], [issue(state="closed", label=None)], [])

    def test_f2_old_orphan_with_new_staged_issue_is_not_clear(self):
        with self.assertRaisesRegex(ValueError, "incomplete"):
            check([ref()], [issue(1703, OTHER, B, "open", "atc: staged")], [])

    def test_f2_ref_cannot_hide_without_original_issue(self):
        with self.assertRaisesRegex(ValueError, "incomplete"):
            check([ref()], [], [])

    def test_f2_closed_ref_without_real_closed_pr_still_blocks(self):
        with self.assertRaisesRegex(ValueError, "orphan"):
            check([ref()], [issue(state="closed")], [])

    def test_f3_foreign_publisher_cannot_take_over_orphan(self):
        x = pr()
        x["user"]["login"] = "other-app[bot]"
        with self.assertRaisesRegex(ValueError, "publisher"):
            check([ref()], [issue()], [x])

    def test_f3_human_publisher_cannot_take_over_orphan(self):
        x = pr()
        x["user"]["type"] = "User"
        with self.assertRaisesRegex(ValueError, "publisher"):
            check([ref()], [issue()], [x])

    def test_f3_wrong_reported_app_cannot_fake_author(self):
        x = pr()
        x["performed_via_github_app"] = {"id": 999}
        with self.assertRaisesRegex(ValueError, "attribution"):
            check([ref()], [issue()], [x])

    def test_empty_pr_snapshot_not_a_closed_history_proof(self):
        with self.assertRaisesRegex(ValueError, "orphan"):
            check([ref()], [issue(state="closed")], [])

    def test_unnamed_or_mismatched_namespace_ref_denied(self):
        test = ref()
        test["ref"] = "refs/heads/hamster/admitted/unknown-name"
        with self.assertRaisesRegex(ValueError, "noncanonical"):
            enumerate_refs([test])
        test = ref()
        test["object"]["sha"] = B
        with self.assertRaisesRegex(ValueError, "SHA"):
            enumerate_refs([test])
        with self.assertRaisesRegex(ValueError, "duplicate"):
            enumerate_refs([ref(), ref()])

    def test_r3_outside_namespace_siblings_do_not_block_census(self):
        sibling = {
            "ref": "refs/heads/hamster/admitted-not-atc",
            "object": {"sha": A},
        }
        sibling_exact_prefix = {
            "ref": "refs/heads/hamster/admitted",
            "object": {"sha": A},
        }
        self.assertEqual(enumerate_refs([sibling, sibling_exact_prefix]), [])
        self.assertEqual(enumerate_refs([sibling, ref(), sibling_exact_prefix]),
                         enumerate_refs([ref()]))
        # Even with an innocent sibling returned by GitHub's broad ref
        # prefix search, a fully validated real closed history remains clear.
        x = check([sibling, ref(), sibling_exact_prefix],
                  [issue(state="closed", label=None)], [pr(state="closed")])
        self.assertTrue(x["admission_clear"])

    def test_r3_noncanonical_inside_protected_namespace_still_denied(self):
        for bad in ("refs/heads/hamster/admitted/not-an-atc-ref",
                    "refs/heads/hamster/admitted/atc-1-wrong"):
            with self.subTest(ref=bad), self.assertRaisesRegex(ValueError, "noncanonical"):
                enumerate_refs([{"ref": bad, "object": {"sha": A}}])
        # An unrelated API prefix outside the requested GitHub search
        # prefix is still an error, not silently discarded.
        with self.assertRaisesRegex(ValueError, "unexpected branch"):
            enumerate_refs([{"ref": "refs/heads/some/other/prefix",
                             "object": {"sha": A}}])

    def test_unlabelled_open_admitted_issue_not_repaired_implicitly(self):
        with self.assertRaisesRegex(ValueError, "valid reservation"):
            check([ref()], [issue(label=None)], [pr()])

    def test_wrong_or_duplicate_pr_cannot_prove_history(self):
        with self.assertRaisesRegex(ValueError, "duplicate"):
            check([ref()], [issue()], [pr(), pr(n=1703)])
        p = pr()
        p["base"]["ref"] = "other"
        with self.assertRaisesRegex(ValueError, "mismatch"):
            check([ref()], [issue()], [p])


if __name__ == "__main__":
    unittest.main()
