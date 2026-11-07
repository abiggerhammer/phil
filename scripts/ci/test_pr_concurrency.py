#!/usr/bin/env python3
"""Offline PR-head concurrency policy regression tests."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_pr_concurrency import GROUP, CANCEL, validate_workflow, check_inventory


VALID = ("name: Example\n\nconcurrency:\n" + GROUP + "\n" + CANCEL +
         "\n\non:\n  pull_request:\n  push:\n    branches: [main]\n\n"
         "jobs:\n  verify:\n    runs-on: ubuntu-latest\n"
         "    steps:\n      - run: echo ok\n")


def group(workflow_ref, event, pr_number, run_id):
    """Model of the exact installed group expression, not an Actions engine."""
    return f"{workflow_ref}-{pr_number if event == 'pull_request' else run_id}"


class SupersessionPolicyTests(unittest.TestCase):
    def test_valid(self):
        self.assertEqual(validate_workflow(VALID), [])

    def test_missing_concurrency_rejected(self):
        without = VALID.replace("concurrency:\n" + GROUP + "\n" + CANCEL, "")
        self.assertTrue(validate_workflow(without))

    def test_main_release_and_manual_runs_do_not_collide(self):
        for event in ("push", "release", "workflow_dispatch"):
            self.assertNotEqual(group("repo/w.yml@main", event, None, 17),
                                group("repo/w.yml@main", event, None, 18))
            self.assertNotEqual(event, "pull_request")

    def test_same_pr_revisions_share_group(self):
        ref = "repo/w.yml@refs/pull/12/merge"
        self.assertEqual(group(ref, "pull_request", 12, 17),
                         group(ref, "pull_request", 12, 18))

    def test_different_prs_and_workflows_are_isolated(self):
        self.assertNotEqual(group("repo/w.yml@refs/pull/12/merge", "pull_request", 12, 17),
                            group("repo/w.yml@refs/pull/13/merge", "pull_request", 13, 18))
        self.assertNotEqual(group("repo/w.yml@refs/pull/12/merge", "pull_request", 12, 17),
                            group("repo/x.yml@refs/pull/12/merge", "pull_request", 12, 18))

    def test_unconditional_cancellation_rejected(self):
        self.assertTrue(validate_workflow(
            VALID.replace(CANCEL, "  cancel-in-progress: true")))

    def test_group_using_main_branch_ref_rejected(self):
        unsafe = "  group: ${{ github.workflow }}-${{ github.event.pull_request.number || github.ref }}"
        self.assertTrue(validate_workflow(VALID.replace(GROUP, unsafe)))

    def test_queue_control_rejected(self):
        self.assertTrue(validate_workflow(
            VALID.replace(CANCEL, CANCEL + "\n  queue: max")))

    def test_duplicate_concurrency_rejected(self):
        self.assertTrue(validate_workflow(
            VALID + "\nconcurrency:\n" + GROUP + "\n" + CANCEL))

    def test_missing_pull_request_event_rejected(self):
        self.assertTrue(validate_workflow(
            VALID.replace("  pull_request:\n", "  workflow_dispatch:\n")))

    def test_audited_repository_files(self):
        self.assertEqual(check_inventory(), [])


if __name__ == "__main__":
    unittest.main()
