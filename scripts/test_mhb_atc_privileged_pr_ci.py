#!/usr/bin/env python3
"""G2 source-only guard: no PR candidate execution with release secrets or Actions-write.

A deliberately restrictive audit of the current workflow inventory, NOT a
GitHub settings/permissions attestation or a simulation of Actions execution.
No credential, live PR, release or App token is used by these tests.
"""
from __future__ import annotations

import copy
from pathlib import Path
import re
import shutil
import tempfile
import unittest

import yaml

from test_mhb_atc_staged_push_ci import StrictWorkflowLoader, parse_workflow_events
from mhb_atc_g2_policy import EXPRESSION, SECRET_CONTEXT, strings

ROOT = Path(__file__).resolve().parents[1]
WORKFLOWS = ROOT / ".github" / "workflows"

RELEASES = {
    "phase1-int011-darwin-distribution-release.yml",
    "phase1-int011-github-release.yml",
    "phase1-steve-github-release.yml",
}
INT007 = {
    "phase1-int007-runtime-build-discovery.yml",
    "phase1-int007-assurance-input-discovery.yml",
    "phase1-int007-complete-freeze-discovery.yml",
    "phase1-int007-ping-verification-discovery.yml",
    "phase1-int007-verification-discovery-macos.yml",
    "phase1-int007-assurance-closure-discovery.yml",
    "phase1-int-007-handoff-manifest.yml",
}
SIGNING_JOBS = {"darwin-build-submit", "darwin-poll-assess"}
TRUSTED_SIGNING_IF = (
    "github.ref == 'refs/heads/main' && "
    "(github.event_name == 'push' || "
    "(github.event_name == 'workflow_dispatch' && github.actor == 'abiggerhammer'))"
)
PUBLISH_IF = "github.event_name == 'push' && github.ref == 'refs/heads/main'"


def deny(condition, why):
    if not condition:
        raise ValueError(why)


def normalize_expr(value):
    deny(isinstance(value, str), "missing or nonliteral trust condition")
    return " ".join(value.split())


def write_scopes(perms):
    if perms is None or perms == "read-all":
        return set()
    deny(isinstance(perms, dict), "unknown permissions form in PR workflow")
    return {key for key, val in perms.items() if val == "write"}


def check_reconcile(path, doc, events, jobs):
    if path.name != "mhb-atc-reconcile.yml":
        return False
    deny(isinstance(events.get("pull_request"), dict) and
         events["pull_request"].get("types") == ["closed"],
         "reconciler must only react to a closed PR")
    deny(write_scopes(doc.get("permissions")) == {"issues", "pull-requests"},
         "reconciler permissions changed")
    deny(set(jobs) == {"reconcile"}, "unexpected privileged reconciler job")
    job = jobs["reconcile"]
    guard = normalize_expr(job.get("if"))
    deny("github.event_name != 'pull_request'" in guard and
         "startsWith(github.event.pull_request.head.ref, 'hamster/admitted/')" in guard and
         "github.event.pull_request.head.repo.full_name == github.repository" in guard,
         "reconciler must select exact admitted head")
    checkout = [
        x for x in job.get("steps", [])
        if isinstance(x, dict) and str(x.get("uses", "")).startswith("actions/checkout@")
    ]
    deny(len(checkout) == 1 and
         checkout[0].get("with") == {"ref": "main", "persist-credentials": "false"},
         "reconciler must execute only trusted main without cached credentials")
    return True


def check_pr_privileges(path: Path) -> None:
    try:
        doc = yaml.load(path.read_text(encoding="utf-8"), Loader=StrictWorkflowLoader)
    except yaml.YAMLError as exc:
        raise ValueError(f"{path.name}: malformed workflow YAML") from exc
    deny(isinstance(doc, dict), f"{path.name}: missing workflow mapping")
    events = parse_workflow_events(path.read_text(encoding="utf-8"))
    if "pull_request" not in events:
        return
    jobs = doc.get("jobs")
    deny(isinstance(jobs, dict) and jobs, f"{path.name}: malformed jobs")
    root_writes = write_scopes(doc.get("permissions"))
    is_reconcile = check_reconcile(path, doc, events, jobs)
    if not is_reconcile:
        deny(not root_writes,
             f"{path.name}: candidate PR workflows cannot have root write permissions")

    for value in strings({k: v for k, v in doc.items() if k != "jobs"}):
        deny(not any(SECRET_CONTEXT.search(expr) for expr in EXPRESSION.findall(value)),
             f"{path.name}/pull_request: SECRET_CONTEXT")

    for jobname, job in jobs.items():
        deny(isinstance(job, dict), f"{path.name}: malformed job {jobname}")
        effective = job.get("permissions", doc.get("permissions"))
        deny(effective is not None, f"{path.name}/{jobname}/pull_request: PERMISSIONS_ABSENT")
        writes = write_scopes(effective)
        is_publish = path.name in RELEASES and jobname == "publish"
        if is_publish:
            deny(writes == {"contents"} and
                 normalize_expr(job.get("if")) == PUBLISH_IF,
                 f"{path.name}: publishing must require push on trusted main")
        elif is_reconcile:
            deny("permissions" not in job, f"{path.name}: reconciler override changed")
        else:
            deny(not writes,
                 f"{path.name}: job {jobname} grants write to candidate PR code")

        env = job.get("environment")
        is_signer = path.name in RELEASES and jobname in SIGNING_JOBS
        if is_signer:
            deny(env == "macos-release" and
                 normalize_expr(job.get("if")) == TRUSTED_SIGNING_IF,
                 f"{path.name}: signer must be skipped on all PR events")
        else:
            deny(not env,
                 f"{path.name}: unreviewed PR job environment {jobname}")

        for value in strings(job):
            for expr in EXPRESSION.findall(value):
                if not SECRET_CONTEXT.search(expr):
                    continue
                match = re.fullmatch(r"secrets\.([A-Za-z0-9_]+)", expr)
                allowed = False
                if match:
                    name = match[1]
                    allowed = (is_signer and name.startswith("APPLE_")) or (
                        name == "GITHUB_TOKEN" and (
                            is_publish or (path.name == "fsem-claim-guard.yml" and
                                           jobname == "exact-claim-before-pr")))
                deny(allowed, f"{path.name}/{jobname}/pull_request: SECRET_CONTEXT")


def audit_pr_workflow_inventory(root: Path) -> int:
    paths = sorted(root.glob("*.yml")) + sorted(root.glob("*.yaml"))
    deny(len(paths) >= 500, "workflow inventory is incomplete")
    for path in paths:
        check_pr_privileges(path)
    return len(paths)


class PrivilegedPrIsolationTests(unittest.TestCase):
    def test_all_workflows_keep_pr_privileged_code_separate(self):
        self.assertGreater(audit_pr_workflow_inventory(WORKFLOWS), 500)

    def test_int007_pr_jobs_use_native_concurrency_not_actions_write(self):
        for name in sorted(INT007):
            with self.subTest(workflow=name):
                doc = yaml.load((WORKFLOWS / name).read_text(), Loader=StrictWorkflowLoader)
                self.assertEqual(doc.get("permissions"), {"contents": "read"})
                self.assertEqual(doc["concurrency"]["cancel-in-progress"], "true")
                self.assertNotIn("cancelWorkflowRun",
                                 (WORKFLOWS / name).read_text())
                self.assertIn("pull_request", parse_workflow_events(
                    (WORKFLOWS / name).read_text()))

    def test_release_signing_requires_trusted_main_event(self):
        for name in sorted(RELEASES):
            with self.subTest(workflow=name):
                doc = yaml.load((WORKFLOWS / name).read_text(), Loader=StrictWorkflowLoader)
                self.assertEqual(doc["permissions"], {"contents": "read"})
                self.assertIn("pull_request", parse_workflow_events(
                    (WORKFLOWS / name).read_text()))
                jobs = doc["jobs"]
                for signed in SIGNING_JOBS:
                    self.assertEqual(jobs[signed]["environment"], "macos-release")
                    self.assertEqual(normalize_expr(jobs[signed]["if"]),
                                     TRUSTED_SIGNING_IF)
                self.assertEqual(jobs["darwin-poll-assess"]["needs"],
                                 ["darwin-build-submit"])
                if name != "phase1-int011-darwin-distribution-release.yml":
                    self.assertEqual(normalize_expr(jobs["publish"]["if"]),
                                     PUBLISH_IF)
                    self.assertEqual(jobs["publish"]["permissions"],
                                     {"contents": "write"})
                    # Linux packaging remains runnable with read-only PR code.
                    self.assertNotIn("if", jobs["linux-package"])
                    self.assertNotIn("environment", jobs["linux-package"])

    def test_g2_audit_is_run_on_all_future_workflow_edits(self):
        ci = (WORKFLOWS / "mhb-atc-tests.yml").read_text()
        self.assertEqual(ci.count("      - '.github/workflows/**'"), 2)
        self.assertIn("python3 scripts/test_mhb_atc_privileged_pr_ci.py", ci)

    def test_global_audit_rejects_regressed_privileged_pr_workflows(self):
        # Mutation harness invokes the SAME full-inventory entry point as CI.
        with tempfile.TemporaryDirectory() as td:
            copied = Path(td) / "workflows"
            shutil.copytree(WORKFLOWS, copied)
            self.assertGreater(audit_pr_workflow_inventory(copied), 500)

            source = copied / "phase1-steve-github-release.yml"
            original = source.read_text()
            # Remove the trusted-main gate from a signer.
            source.write_text(original.replace(
                "      github.ref == 'refs/heads/main' &&\n"
                "      (github.event_name == 'push' ||\n"
                "       (github.event_name == 'workflow_dispatch' && github.actor == 'abiggerhammer'))",
                "      github.event_name == 'pull_request'", 1))
            with self.assertRaises(ValueError):
                audit_pr_workflow_inventory(copied)
            source.write_text(original)

            int007 = copied / "phase1-int007-runtime-build-discovery.yml"
            original_int = int007.read_text()
            int007.write_text(original_int.replace(
                "permissions:\n  contents: read\n",
                "permissions:\n  contents: read\n  actions: write\n", 1))
            with self.assertRaises(ValueError):
                audit_pr_workflow_inventory(copied)
            int007.write_text(original_int)

            hostile = copied / "g2-unreviewed-secrets.yml"
            hostile.write_text(
                "name: hostile\non: [pull_request]\n"
                "jobs:\n  leak:\n    runs-on: ubuntu-latest\n"
                "    environment: macos-release\n"
                "    steps:\n      - run: echo unauthorized\n")
            with self.assertRaises(ValueError):
                audit_pr_workflow_inventory(copied)
            hostile.unlink()

            published = copied / "phase1-int011-github-release.yml"
            original_pub = published.read_text()
            published.write_text(original_pub.replace(
                "    if: github.event_name == 'push' && github.ref == 'refs/heads/main'",
                "    if: github.event_name == 'pull_request'"))
            with self.assertRaises(ValueError):
                audit_pr_workflow_inventory(copied)
            published.write_text(original_pub)


if __name__ == "__main__":
    unittest.main()
