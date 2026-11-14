#!/usr/bin/env python3

import copy
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

import mhb_lint


def clean_snapshot():
    head = "a" * 40
    return {
        "operation": "merge",
        "lane": "rocq-refinement",
        "expected_head": head,
        "main_sha": "m" * 40,
        "pr": {
            "labels": ["lane: rocq-refinement"],
            "head_ref": "hamster/rocq-refinement/example",
            "head_sha": head,
            "base_sha": "m" * 40,
            "changed_files": ["proof/Phil/Example.v"],
        },
        "checks": {
            "total_count": 2,
            "runs": [
                {"name": "build", "status": "completed", "conclusion": "success"},
                {"name": "proof", "status": "completed", "conclusion": "success"},
            ],
        },
        "intervening_main_files": [],
    }


class MhbLintTests(unittest.TestCase):
    def test_clean_snapshot_has_no_diagnostics(self):
        self.assertEqual(mhb_lint.lint_snapshot(clean_snapshot()), [])

    def test_all_initial_rules_are_reachable(self):
        snapshot = clean_snapshot()
        snapshot.update(
            {
                "operation": "refresh",
                "lane": "proof-audit",
                "expected_head": "b" * 40,
                "main_sha": "n" * 40,
                "refresh_family": "phase1-int007",
                "generated_changed_paths": ["README.md"],
                "intervening_main_files": ["proof/Phil/Example.v"],
            }
        )
        snapshot["pr"].update(
            {
                "labels": ["lane: impl-audit"],
                "head_ref": "hamster/impl-audit/example",
                "base_sha": "m" * 40,
            }
        )
        snapshot["checks"] = {
            "total_count": 2,
            "runs": [
                {"name": "build", "status": "completed", "conclusion": "failure"}
            ],
        }

        rule_ids = [item.rule_id for item in mhb_lint.lint_snapshot(snapshot)]
        self.assertEqual(
            rule_ids,
            [
                "MHB001",
                "MHB002",
                "MHB003",
                "MHB004",
                "MHB005",
                "MHB006",
                "MHB007",
                "MHB008",
            ],
        )

    def test_new_final_authority_proof_lanes_are_strictly_scoped(self):
        for lane in ("p8-representation", "p9-evidence"):
            for operation in ("auto-pr", "merge"):
                with self.subTest(lane=lane, operation=operation):
                    snapshot = clean_snapshot()
                    snapshot["operation"] = operation
                    snapshot["lane"] = lane
                    snapshot["pr"]["labels"] = ["lane: " + lane]
                    snapshot["pr"]["head_ref"] = "hamster/" + lane + "/first-proof"
                    self.assertEqual(mhb_lint.lint_snapshot(snapshot), [])

            # A new proof lane never inherits the separately authorized
            # generated-file refresh privilege of the impl-audit hamster.
            snapshot = clean_snapshot()
            snapshot["operation"] = "refresh"
            snapshot["lane"] = lane
            snapshot["pr"]["labels"] = ["lane: " + lane]
            snapshot["pr"]["head_ref"] = "hamster/" + lane + "/first-proof"
            self.assertIn("MHB001",
                          [x.rule_id for x in mhb_lint.lint_snapshot(snapshot)])

            # Exact lane isolation: no other lane label may confer authority.
            snapshot["operation"] = "merge"
            snapshot["pr"]["labels"] = ["lane: " + lane, "lane: impl-audit"]
            self.assertIn("MHB002",
                          [x.rule_id for x in mhb_lint.lint_snapshot(snapshot)])
            snapshot["pr"]["labels"] = ["lane: " + lane]
            snapshot["pr"]["head_ref"] = "hamster/impl-audit/foreign"
            self.assertIn("MHB003",
                          [x.rule_id for x in mhb_lint.lint_snapshot(snapshot)])

    def test_phase1_int007_generated_whitelist(self):
        snapshot = clean_snapshot()
        snapshot.update(
            {
                "operation": "refresh",
                "lane": "impl-audit",
                "refresh_family": "phase1-int007",
                "generated_changed_paths": [
                    "handoff/phase1/manifest-v1.tsv",
                    "handoff/phase1/witnesses/upload-verification-bundle-v1.tsv",
                    "handoff/phase1/witnesses/steve-assurance-manifest-v1.tsv",
                    "handoff/phase1/witnesses/upload-residual-tcb-v1.tsv",
                ],
            }
        )
        snapshot["pr"]["labels"] = ["lane: impl-audit"]
        snapshot["pr"]["head_ref"] = "hamster/impl-audit/example"

        rule_ids = [item.rule_id for item in mhb_lint.lint_snapshot(snapshot)]
        self.assertNotIn("MHB008", rule_ids)

    def test_diagnostics_are_deterministic(self):
        snapshot = clean_snapshot()
        snapshot["checks"]["runs"] = list(reversed(snapshot["checks"]["runs"]))
        first = [
            json.dumps(item.details, sort_keys=True)
            for item in mhb_lint.lint_snapshot(snapshot)
        ]
        second = [
            json.dumps(item.details, sort_keys=True)
            for item in mhb_lint.lint_snapshot(copy.deepcopy(snapshot))
        ]
        self.assertEqual(first, second)

    def test_cli_exit_status(self):
        script = Path(__file__).with_name("mhb_lint.py")
        with tempfile.NamedTemporaryFile("w", encoding="utf-8") as handle:
            json.dump(clean_snapshot(), handle)
            handle.flush()
            result = subprocess.run(
                [sys.executable, str(script), "--format", "json", handle.name],
                check=False,
                capture_output=True,
                text=True,
            )
        self.assertEqual(result.returncode, 0)
        self.assertEqual(json.loads(result.stdout), [])


if __name__ == "__main__":
    unittest.main()
