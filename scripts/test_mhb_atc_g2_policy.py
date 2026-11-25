"""G2-1 offline contract, including inert authority and recorded status fixtures."""
import json
from pathlib import Path
import tempfile
import unittest

import yaml

from mhb_atc_g2_policy import (
    CHECKOUT, artifact_identity, artifact_inventory, candidate_policy,
    execution, report, variants, verify_inventory, workflow,
)
from test_mhb_atc_privileged_pr_ci import check_pr_privileges

ROOT = Path(__file__).resolve().parents[1]
WORKFLOWS = ROOT / ".github/workflows"
EVIDENCE = ROOT / "docs/phase-2/g2-1"


def source(event="pull_request", **overrides):
    doc = {
        "on": {event: {"branches": ["main"]}} if event == "push" else event,
        "permissions": {"contents": "read"},
        "jobs": {"build": {
            "runs-on": "ubuntu-24.04",
            "steps": [{"uses": CHECKOUT, "with": {"persist-credentials": "false"}},
                      {"run": "true"}],
        }},
    }
    doc.update(overrides)
    return doc


class CandidateTests(unittest.TestCase):
    def decision(self, doc, event="pull_request", selected="reviewed-exact"):
        return candidate_policy(yaml.safe_dump(doc), "build", event, selected_source=selected)

    def test_counterexamples_in_both_guards(self):
        for rule, fragment in (
            ("PERMISSIONS_ABSENT", None),
            ("SECRET_CONTEXT", "secrets['HAMSTER_PR_TOKEN']"),
            ("SECRET_CONTEXT", "toJSON(secrets)"),
        ):
            doc = source()
            if fragment is None:
                del doc["permissions"]
            else:
                doc["jobs"]["build"]["env"] = {"UNUSED": "${{ " + fragment + " }}"}
            self.assertEqual(self.decision(doc), rule)
            with tempfile.TemporaryDirectory() as tmp:
                p = Path(tmp) / "fixture.yml"
                p.write_text(yaml.safe_dump(doc))
                with self.assertRaisesRegex(ValueError, f"fixture.yml/build/pull_request: {rule}"):
                    check_pr_privileges(p)

    def test_permission_and_checkout_policy(self):
        doc = source()
        self.assertEqual(self.decision(doc), "ELIGIBLE")
        self.assertEqual(self.decision(source("push"), "push"), "ELIGIBLE")
        job = doc["jobs"]["build"]
        doc["permissions"] = {"contents": "write"}
        job["permissions"] = {}
        self.assertEqual(self.decision(doc), "ELIGIBLE")
        for perms in ({"contents": "write"}, {"id-token": "write"}, "${{ inputs.permissions }}"):
            job["permissions"] = perms
            self.assertEqual(self.decision(doc), "PERMISSIONS_UNSAFE")
        job["permissions"] = {}
        step = job["steps"][0]
        for options, reason in (
            ({}, "CHECKOUT_PERSISTENCE"),
            ({"persist-credentials": "true"}, "CHECKOUT_PERSISTENCE"),
            ({"persist-credentials": "${{ inputs.persist }}"}, "EXPRESSION_UNKNOWN"),
            ({"persist-credentials": "false", "ref": "alternate"}, "CHECKOUT_SOURCE"),
        ):
            step["with"] = options
            self.assertEqual(self.decision(doc), reason)

    def test_unmodeled_indirection_and_events(self):
        for event in ("pull_request_target", "workflow_run", "repository_dispatch",
                      "workflow_dispatch", "schedule", "release", "workflow_call"):
            self.assertEqual(self.decision(source(event), event), "EVENT_AUTHORITY")
        self.assertEqual(self.decision(source("push", **{"on": {"push": {"tags": ["*"]}}}), "push"),
                         "EVENT_AUTHORITY")
        self.assertEqual(self.decision(source(), selected="historical"), "SOURCE_AUTHORITY")
        for key, value, rule in (
            ("uses", "./.github/workflows/other.yml", "INDIRECT_AUTHORITY"),
            ("environment", "privileged", "INDIRECT_AUTHORITY"),
            ("runs-on", "self-hosted", "RUNNER_AUTHORITY"),
            ("secrets", "inherit", "INDIRECT_AUTHORITY"),
            ("env", {"A": "${{ inputs.env }}"}, "EXPRESSION_UNKNOWN"),
            ("env", {"A": "${{ matrix.env }}"}, "EXPRESSION_UNKNOWN"),
            ("env", {"A": "${{ needs.other.outputs.env }}"}, "EXPRESSION_UNKNOWN"),
            ("strategy", {"matrix": {"v": "${{ fromJSON(inputs.m) }}"}}, "EXPRESSION_UNKNOWN"),
        ):
            doc = source()
            doc["jobs"]["build"][key] = value
            self.assertEqual(self.decision(doc), rule)
        for action in ("actions/cache@v4", "./local-action", "actions/checkout@v4"):
            doc = source()
            doc["jobs"]["build"]["steps"][0]["uses"] = action
            self.assertEqual(self.decision(doc), "ACTION_AUTHORITY")

    def test_strict_yaml(self):
        for invalid in ("on: push\non: release\njobs: {}\n",
                        "on: [push, push]\njobs: {x: {}}\n",
                        "on: &event push\njobs: {x: {}}\n"):
            self.assertEqual(candidate_policy(invalid, "x", "push", selected_source="reviewed-exact"),
                             "WORKFLOW_SCHEMA")


class InventoryTests(unittest.TestCase):
    def test_exact_snapshot(self):
        actual = report(WORKFLOWS)
        recorded = json.loads((EVIDENCE / "inventory.json").read_text())
        verify_inventory(recorded["definitions"], actual["definitions"])
        self.assertEqual(recorded, actual)
        base = json.loads((EVIDENCE / "baseline-definitions.json").read_text())
        self.assertEqual((len({x["workflow"] for x in base}),
                          len({(x["workflow"], x["job"]) for x in base}), len(base)), (636, 1079, 2093))
        self.assertEqual({(x["workflow"], x["job"], x["event"]) for x in base},
                         {(x["workflow"], x["job"], x["event"]) for x in actual["definitions"]})
        changes = {old["workflow"] for old, now in zip(base, actual["definitions"])
                   if old["blob"] != now["blob"]}
        repaired = {x["workflow"] for x in base if x["decision"] == "PERMISSIONS_ABSENT"
                    and x["event"] == "pull_request"}
        self.assertEqual(len(repaired), 19)
        self.assertEqual(changes, repaired | {"mhb-atc-tests.yml"})
        for name in repaired:
            doc, _ = workflow((WORKFLOWS / name).read_text())
            self.assertEqual(doc["permissions"], {"contents": "read"})
            for job in doc["jobs"].values():
                self.assertNotIn("permissions", job)
                checkout, = [s for s in job["steps"] if s.get("uses", "").startswith("actions/checkout@")]
                self.assertEqual(checkout["with"]["persist-credentials"], "false")

    def test_missing_duplicate_extra_and_stale(self):
        base = [{"workflow": "w", "job": "j", "event": "push", "blob": "a"}]
        verify_inventory(base, base)
        for actual, rule in (
            ([], "INVENTORY_IDENTITIES"), (base + base, "INVENTORY_DUPLICATE"),
            (base + [base[0] | {"job": "extra"}], "INVENTORY_IDENTITIES"),
            ([base[0] | {"blob": "b"}], "INVENTORY_STALE"),
        ):
            with self.assertRaisesRegex(ValueError, rule):
                verify_inventory(base, actual)

    def test_matrix_and_provider_execution_are_separate(self):
        self.assertEqual(variants({
            "os": ["linux", "darwin"], "target": ["a", "b"],
            "exclude": [{"os": "darwin", "target": "b"}],
            "include": [{"os": "linux", "flag": "x"}, {"os": "windows", "target": "a"}],
        }), {"state": "expanded", "variants": [
            {"os": "linux", "target": "a", "flag": "x"},
            {"os": "linux", "target": "b", "flag": "x"},
            {"os": "darwin", "target": "a"}, {"os": "windows", "target": "a"},
        ]})
        self.assertEqual(variants("${{ fromJSON(inputs.matrix) }}")["state"], "unresolved")
        skipped = json.loads((EVIDENCE / "skipped-job.json").read_text())
        self.assertEqual(execution(skipped), "skipped")
        self.assertEqual(execution(None), "absent")
        self.assertEqual(execution({"status": "queued"}), "pending")
        self.assertEqual(execution(skipped | {"conclusion": "cancelled"}), "cancelled")

    def test_known_producer_arms(self):
        rows = artifact_inventory(WORKFLOWS)
        self.assertEqual(sum(x["kind"] == "upload" for x in rows), 461)
        self.assertEqual(sum(x["kind"] == "download" for x in rows), 162)
        for workflow_name, job, step, expected in (
            ("phase1-steve-github-release.yml", "release-bundle", 1,
             {("linux-package", 5), ("darwin-poll-assess", 7)}),
            ("mhb-atc-w3-publisher-fanout.yml", "publisher_create", 4, {("prepare", 6)}),
            ("mhb-atc-w3-publisher-fanout.yml", "publisher_cleanup", 4, {("prepare", 6)}),
        ):
            r, = [x for x in rows if (x["workflow"], x["job"], x["step"]) == (workflow_name, job, step)]
            self.assertEqual({(x["job"], x["step"]) for x in r["possible_producers"]}, expected)
            self.assertEqual(r["runtime_provenance"], "unresolved")
            if job == "publisher_cleanup":
                self.assertIn("historical or unresolved run selector", r["unresolved"])

    def test_artifact_options_and_authentication(self):
        with tempfile.TemporaryDirectory() as tmp:
            file = Path(tmp) / "fixture.yml"
            doc = source()
            job = doc["jobs"]["build"]
            job["steps"] = [
                {"uses": "actions/upload-artifact@v4", "with": {"name": "a", "path": "out/**\n!out/key"}},
                {"uses": "actions/upload-artifact@v4", "with": {"name": "a", "path": "other", "include-hidden-files": "true"}},
                {"uses": "actions/upload-artifact@v4", "with": {"name": "${{ matrix.name }}", "path": "third"}},
                {"uses": "actions/download-artifact@v4", "with": {"name": "a"}},
                {"uses": "actions/download-artifact@v4", "with": {"pattern": "a*", "merge-multiple": "true"}},
                {"uses": "actions/download-artifact@v4"},
                {"uses": "actions/download-artifact@v4", "with": {"repository": "elsewhere/repo", "run-id": "40", "github-token": "${{ github.token }}"}},
                {"uses": "actions/download-artifact@unknown"},
            ]
            file.write_text(yaml.safe_dump(doc))
            u1, u2, _, exact, glob, all_files, other, unknown = artifact_inventory(Path(tmp))
            self.assertEqual(u1["effective"]["include-hidden-files"], "false")
            self.assertEqual(u2["effective"]["include-hidden-files"], "true")
            self.assertEqual(u1["inclusion"]["exclude"], ["out/key"])
            self.assertEqual(len(exact["possible_producers"]), 3)
            self.assertEqual(len(glob["possible_producers"]), 3)
            self.assertEqual(len(all_files["possible_producers"]), 3)
            self.assertTrue(any("collision" in x for x in exact["unresolved"]))
            self.assertEqual(glob["extraction"]["merge_multiple"], "true")
            self.assertEqual(other["possible_producers"], [])
            self.assertIsNone(unknown["effective"])
        identity = {k: str(i) for i, k in enumerate(
            ("principal", "repository", "run", "attempt", "job", "artifact_id", "digest"), 1)}
        self.assertEqual(artifact_identity(identity, identity), "MATCH")
        for key in identity:
            self.assertEqual(artifact_identity(identity, identity | {key: "wrong"}),
                             "ARTIFACT_" + key.upper())


if __name__ == "__main__":
    unittest.main()
