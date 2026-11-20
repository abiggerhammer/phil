#!/usr/bin/env python3
"""Offline G1 checks: staged ref push isolation and historical workflow-tree binding.

No GitHub credentials, network, staged ref or candidate execution.
"""
from __future__ import annotations

import fnmatch
import os
import shutil
from pathlib import Path
import re
import subprocess
import tempfile
import textwrap
import unittest

import yaml

ROOT = Path(__file__).resolve().parents[1]
WORKFLOWS = ROOT / ".github" / "workflows"
STAGED = "hamster/staged/phase2-selfhost/first-pilot"
UNBOUNDED_LEGACY = {
    "phase1-int-001-source-architecture.yml",
    "phase1-int-001-source-systems.yml",
    "phase1-int-001-witness-e2e.yml",
    "phase1-int-002-manifest-closure.yml",
}


# This dependency is pinned by the read-only ATC replay job. BaseLoader
# preserves the literal YAML key "on" (SafeLoader's YAML 1.1 boolean coercion
# would silently erase the GitHub Actions event key).
SUPPORTED_EVENTS = frozenset({
    "push", "pull_request", "workflow_dispatch", "schedule",
    "repository_dispatch", "pull_request_target", "workflow_run",
})
SUPPORTED_PUSH_FIELDS = frozenset({
    "branches", "branches-ignore", "tags", "tags-ignore",
    "paths", "paths-ignore",
})


class StrictWorkflowLoader(yaml.BaseLoader):
    """Decode real YAML, rejecting aliases and duplicate/merged mapping keys."""

    def compose_node(self, parent, index):
        event = self.peek_event()
        if isinstance(event, yaml.events.AliasEvent) or getattr(event, "anchor", None):
            raise ValueError("YAML aliases and anchors are not permitted in G1 policy")
        return super().compose_node(parent, index)

    def construct_mapping(self, node, deep=False):
        if not isinstance(node, yaml.MappingNode):
            raise ValueError("expected YAML mapping")
        result = {}
        for key_node, value_node in node.value:
            if not isinstance(key_node, yaml.ScalarNode):
                raise ValueError("non-scalar YAML mapping key")
            key = self.construct_object(key_node, deep=deep)
            if not isinstance(key, str) or key in result or key == "<<":
                raise ValueError("duplicate, merged or invalid YAML mapping key")
            result[key] = self.construct_object(value_node, deep=deep)
        return result


def parse_workflow_events(source: str) -> dict:
    """Decode a single workflow document; unknown event grammar denies."""
    try:
        doc = yaml.load(source, Loader=StrictWorkflowLoader)
    except yaml.YAMLError as exc:
        raise ValueError("invalid workflow YAML") from exc
    if not isinstance(doc, dict) or "on" not in doc:
        raise ValueError("missing or malformed workflow on event")
    events = doc["on"]
    if isinstance(events, str):
        events = {events: ""}
    elif isinstance(events, list):
        if not events or any(not isinstance(name, str) or not name for name in events):
            raise ValueError("malformed workflow event list")
        if len(set(events)) != len(events):
            raise ValueError("duplicate workflow event")
        events = {name: "" for name in events}
    if not isinstance(events, dict) or not events:
        raise ValueError("unrecognized workflow event mapping")
    if any(not isinstance(name, str) or name not in SUPPORTED_EVENTS
           for name in events):
        raise ValueError("unreviewed workflow event kind")
    return events


def push_properties(source: str):
    """Return real decoded on.push branch selectors, or None for no push.

    On a scalar/list push event or empty push mapping, return empty selectors:
    no branch filter means the workflow is UNSAFE on staged refs.
    """
    events = parse_workflow_events(source)
    if "push" not in events:
        return None
    props = events["push"]
    if props == "":  # A YAML "push:" without filters
        props = {}
    if not isinstance(props, dict):
        raise ValueError("unsupported push event configuration")
    if any(key not in SUPPORTED_PUSH_FIELDS for key in props):
        raise ValueError("unreviewed push event field")
    out = {}
    for key in ("branches", "branches-ignore"):
        if key in props:
            branches = props[key]
            if not isinstance(branches, list) or not branches or any(
                    not isinstance(item, str) or not item for item in branches):
                raise ValueError("invalid push branch selector list")
            if len(set(branches)) != len(branches):
                raise ValueError("duplicate push branch selector")
            out[key] = branches
    if set(out) == {"branches", "branches-ignore"}:
        raise ValueError("mutually exclusive push branch selectors")
    return out


def branch_pattern_disjoint_from_staged(pattern: str) -> bool:
    """Sound restriction for current allowlists, not GitHub glob simulation.

    Only literal names and * or ** at the VERY END are admitted. No optional
    characters, classes, braces, escapes, negation or interior wildcard can
    change the mandatory literal prefix. Any unsupported form denies.
    """
    if not isinstance(pattern, str) or not re.fullmatch(
            r"[A-Za-z0-9._/-]+(?:\*|\*\*)?", pattern):
        return False
    literal_prefix = pattern.rstrip("*")
    staged_prefix = "hamster/staged/"
    return not (staged_prefix.startswith(literal_prefix) or
                literal_prefix.startswith(staged_prefix))


def excludes_staged_push(source: str) -> bool:
    props = push_properties(source)
    if props is None:
        return True
    if set(props) == {"branches"}:
        return all(branch_pattern_disjoint_from_staged(p)
                   for p in props["branches"])
    if set(props) == {"branches-ignore"}:
        # Exactly two reviewed exclusions: staged untrusted code and
        # protected W3 disposable publisher canary/seed leaves.
        return props["branches-ignore"] == [
            "hamster/staged/**", "hamster/admitted/w3-*"]
    return False


def branch_pattern_disjoint_from_w3(pattern: str) -> bool:
    """Conservative allowlist proof for W3 single-leaf admitted refs."""
    if not isinstance(pattern, str) or not re.fullmatch(
            r"[A-Za-z0-9._/-]+(?:\*|\*\*)?", pattern):
        return False
    literal_prefix = pattern.rstrip("*")
    target_prefix = "hamster/admitted/w3-"
    return not (target_prefix.startswith(literal_prefix) or
                literal_prefix.startswith(target_prefix))


def excludes_w3_disposable_push(source: str) -> bool:
    props = push_properties(source)
    if props is None:
        return True
    if set(props) == {"branches"}:
        return all(branch_pattern_disjoint_from_w3(p)
                   for p in props["branches"])
    if set(props) == {"branches-ignore"}:
        # Negation/extra globs are not in the reviewed allowlist.
        return props["branches-ignore"] == [
            "hamster/staged/**", "hamster/admitted/w3-*"]
    return False


def audit_workflow_inventory(root: Path) -> int:
    """Fail on ANY unsafe workflow using the same path as hosted CI."""
    workflows = sorted(root.glob("*.yml")) + sorted(root.glob("*.yaml"))
    if len(workflows) < 500:
        raise ValueError("workflow inventory is incomplete")
    for path in workflows:
        try:
            source = path.read_text(encoding="utf-8")
            safe = excludes_staged_push(source) and excludes_w3_disposable_push(source)
        except ValueError as exc:
            raise ValueError(f"{path.name}: malformed or unsupported trigger: {exc}") from exc
        if not safe:
            raise ValueError(f"{path.name}: push may reach staged or W3 disposable admitted refs")
    return len(workflows)


class StagedPushIsolationTests(unittest.TestCase):
    def test_all_workflow_push_triggers_reject_staged_namespace(self):
        self.assertGreater(audit_workflow_inventory(WORKFLOWS), 500)

    def test_w3_protected_disposable_leaf_cannot_trigger_pre_admission_push(self):
        sample = "on:\n  push:\n    branches-ignore:\n" \
                 "      - 'hamster/staged/**'\n" \
                 "      - 'hamster/admitted/w3-*'\n"
        self.assertTrue(excludes_w3_disposable_push(sample))
        for branch in ("hamster/admitted/w3-deadbeef1234-canary",
                       "hamster/admitted/w3-deadbeef1234-seed",
                       "hamster/admitted/w3-deadbeef1234-create"):
            self.assertTrue(fnmatch.fnmatchcase(branch, "hamster/admitted/w3-*"))
        self.assertFalse(fnmatch.fnmatchcase("hamster/admitted/atc-1-lane-sha",
                                            "hamster/admitted/w3-*"))
        for unsafe in [
            sample.replace("      - 'hamster/admitted/w3-*'\n", ""),
            sample.replace("'hamster/admitted/w3-*'", "'hamster/admitted/w3/placeholder'"),
            "on:\n  push:\n    branches: [hamster/admitted/**]\n",
            "on:\n  push:\n    paths: ['src/**']\n",
        ]:
            with self.subTest(source=unsafe):
                self.assertFalse(excludes_w3_disposable_push(unsafe))

    def test_global_audit_is_registered_for_every_future_workflow_change(self):
        ci = (WORKFLOWS / "mhb-atc-tests.yml").read_text()
        self.assertEqual(ci.count("      - '.github/workflows/**'"), 2)
        self.assertIn("python3 scripts/test_mhb_atc_staged_push_ci.py", ci)

    def test_four_legacy_push_workflows_keep_normal_branches(self):
        for name in sorted(UNBOUNDED_LEGACY):
            path = WORKFLOWS / name
            source = path.read_text()
            props = push_properties(source)
            with self.subTest(workflow=name):
                self.assertEqual(props, {"branches-ignore": [
                    "hamster/staged/**", "hamster/admitted/w3-*"]})
                self.assertIn("  pull_request:", source)
                self.assertTrue(fnmatch.fnmatchcase(STAGED, props["branches-ignore"][0]))
                self.assertTrue(fnmatch.fnmatchcase(
                    "hamster/admitted/w3-d1e2f3a4b5c6-seed",
                    props["branches-ignore"][1]))
                self.assertFalse(fnmatch.fnmatchcase("main", props["branches-ignore"][0]))
                self.assertFalse(fnmatch.fnmatchcase("feature/my-work", props["branches-ignore"][0]))
                unprotected = source.replace(
                    "    branches-ignore:\n      - 'hamster/staged/**'\n"
                    "      # Disposable W3 publisher canary/seed refs are not admission.\n"
                    "      - 'hamster/admitted/w3-*'\n", "")
                self.assertFalse(excludes_staged_push(unprotected))
                too_narrow = source.replace(
                    "'hamster/staged/**'", "'hamster/proposed/**'")
                self.assertFalse(excludes_staged_push(too_narrow))

    def test_branch_allow_patterns_must_be_provably_disjoint(self):
        for pattern in ("main", "scratch/p8-h9-*", "hamster/proof-audit/**",
                        "hamster/p9-evidence/**", "phase1-int-001-*"):
            with self.subTest(pattern=pattern):
                self.assertTrue(branch_pattern_disjoint_from_staged(pattern))
        for pattern in ("**", "*", "hamster/**", "hamster/staged/**",
                        "hamster/staged/phase2-selfhost/x",
                        "ham?ter/staged/**", "!hamster/staged/**",
                        "hamster/stagedx?/**", "x?hamster/staged/**",
                        "hamster/[s]taged/**", "hamster/staged{,x}/**",
                        "hamster/staged\\x/**"):
            with self.subTest(pattern=pattern):
                self.assertFalse(branch_pattern_disjoint_from_staged(pattern))

    def test_unrecognized_push_filters_fail_closed(self):
        sample = "name: demo\non:\n  push:\n    paths:\n      - 'src/**'\njobs:\n  test:\n    runs-on: ubuntu-latest\n"
        for variant in [
            sample,
            sample.replace("  push:\n", "  push: {branches: [main]}\n"),
            sample.replace("on:\n  push:", "on: [push]\n  push:"),
            sample.replace("    paths:\n", "    branches: ['**']\n    paths:\n"),
            sample.replace("    paths:\n", "    branches-ignore:\n      - 'hamster/staged/*'\n    paths:\n"),
        ]:
            with self.subTest(variant=variant[:70]):
                try:
                    safe = excludes_staged_push(variant)
                except ValueError:
                    safe = False
                self.assertFalse(safe)


    def test_real_yaml_variants_and_duplicate_keys_are_fail_closed(self):
        # G1-01: these are real YAML structures. The formerly hand-rolled
        # parser either missed push or borrowed a different event's policy.
        hostile = [
            'on:\n  "push":\n    paths: ["src/**"]\n',
            'on:\n    push:\n        paths: ["src/**"]\n',
            'on:\n  - push\n  - pull_request\n',
            'on:\n  push:\n    paths: ["src/**"]\n  "pull_request":\n    branches: [main]\n',
            'on:\n  push:\n    branches-ignore: ["hamster/staged/**,suffix"]\n',
            'on:\n  push:\n    branches: ["hamster/stagedx?/**"]\n',
            'on:\n  push:\n    branches: ["x?hamster/staged/**"]\n',
            'on:\n  push:\n    branches: [main]\n  push:\n    paths: ["src/**"]\n',
            'on:\n  push:\n    branches: [main]\n    branches: [other]\n',
            'on:\n  push: &unsafe\n    paths: ["src/**"]\n',
            'on: [push, pull_request]\n',
            'on: push\n',
        ]
        for trigger in hostile:
            with self.subTest(trigger=trigger):
                try:
                    accepted = excludes_staged_push(trigger)
                except ValueError:
                    accepted = False
                self.assertFalse(accepted, trigger)
        # Safe nonstandard spelling and indentation are actually parsed.
        self.assertTrue(excludes_staged_push(
            'on:\n    "push":\n        branches-ignore: ["hamster/staged/**", "hamster/admitted/w3-*"]\n'))
        self.assertTrue(excludes_staged_push(
            'on:\n  push:\n    branches: [main]\n  "pull_request":\n    branches: [main]\n'))
        self.assertTrue(excludes_staged_push('on: ["pull_request"]\n'))

    def test_hostile_618th_workflow_fails_the_real_inventory_audit(self):
        # This exercises the PUBLIC global path, not just isolated helpers.
        # Every hostile workflow gets a legitimate jobs stanza.
        cases = {
            "quoted-push": 'on:\n  "push":\n    paths: ["src/**"]\n',
            "four-spaces": 'on:\n    push:\n        paths: ["src/**"]\n',
            "block-list": 'on:\n  - push\n  - pull_request\n',
            "quoted-sibling": 'on:\n  push:\n    paths: ["src/**"]\n  "pull_request":\n    branches: [main]\n',
            "quoted-comma": 'on:\n  push:\n    branches-ignore: ["hamster/staged/**,suffix"]\n',
            "optional-tail": 'on:\n  push:\n    branches: ["hamster/stagedx?/**"]\n',
            "optional-head": 'on:\n  push:\n    branches: ["x?hamster/staged/**"]\n',
            "duplicate-event": 'on:\n  push:\n    branches: [main]\n  push:\n    branches: [main]\n',
        }
        with tempfile.TemporaryDirectory() as td:
            destination = Path(td) / "workflows"
            shutil.copytree(WORKFLOWS, destination)
            self.assertGreater(audit_workflow_inventory(destination), 500)
            hostile_file = destination / "new-staged-execution.yml"
            for name, trigger in cases.items():
                hostile_file.write_text(
                    "name: hostile G1 fixture\n" + trigger +
                    "jobs:\n  danger:\n    runs-on: ubuntu-latest\n"
                    "    steps:\n      - run: echo forbidden\n")
                with self.subTest(case=name), self.assertRaises(ValueError):
                    audit_workflow_inventory(destination)

    def test_broker_guard_rejects_historical_and_modified_workflow_trees(self):
        # Execute the literal trusted workflow's guard against actual Git
        # commits: a valid OLD base may include pre-isolation triggers.
        source = (WORKFLOWS / "mhb-atc-worker-broker.yml").read_text()
        begin = source.index("          # MHB_ATC_G1_WORKFLOW_TREE_START")
        end = source.index("          # MHB_ATC_G1_WORKFLOW_TREE_END", begin)
        gate = "set -euo pipefail\n" + textwrap.dedent(source[begin:end])
        self.assertLess(source.index("# MHB_ATC_G1_WORKFLOW_TREE_END"),
                        source.index("Mint dedicated broker-held worker App token"))
        self.assertLess(source.index("# MHB_ATC_G1_WORKFLOW_TREE_END"),
                        source.index("if [ \"$MODE\" = \"plan\" ]"))

        with tempfile.TemporaryDirectory() as temp:
            work = Path(temp) / "repo"

            def git(*args):
                ran = subprocess.run(["git", *args], cwd=work.parent,
                                     text=True, capture_output=True)
                self.assertEqual(ran.returncode, 0, ran.stderr)
                return ran.stdout.strip()

            git("init", "-b", "main", str(work))
            git("-C", str(work), "config", "user.name", "Fixture")
            git("-C", str(work), "config", "user.email", "fixture@example.test")
            flows = work / ".github" / "workflows"
            flows.mkdir(parents=True)
            candidate_file = work / "src" / "candidate.txt"
            candidate_file.parent.mkdir()
            candidate_file.write_text("original\n")
            workflow_file = flows / "unsafe.yml"
            workflow_file.write_text("on:\n  push:\njobs:\n  test:\n    runs-on: ubuntu-latest\n")
            git("-C", str(work), "add", ".")
            git("-C", str(work), "commit", "-m", "old unsafe base")
            old_base = git("-C", str(work), "rev-parse", "HEAD")

            workflow_file.write_text(
                "on:\n  push:\n    branches-ignore:\n"
                "      - 'hamster/staged/**'\n"
                "jobs:\n  test:\n    runs-on: ubuntu-latest\n")
            git("-C", str(work), "commit", "-am", "reviewed trigger policy")
            trusted_main = git("-C", str(work), "rev-parse", "HEAD")

            def check(base, head):
                env = dict(os.environ, GIT_DIR=str(work / ".git"),
                           BASE_SHA=base, HEAD_SHA=head, MAIN_SHA=trusted_main)
                return subprocess.run(["bash", "-c", gate], env=env,
                                      cwd=work, text=True, capture_output=True)

            git("-C", str(work), "switch", "-c", "stale", old_base)
            candidate_file.write_text("old-source worker proposal\n")
            git("-C", str(work), "commit", "-am", "legitimate old-base proposal")
            stale_head = git("-C", str(work), "rev-parse", "HEAD")
            stale = check(old_base, stale_head)
            self.assertNotEqual(stale.returncode, 0)
            self.assertIn("workflow tree differs", stale.stderr)

            git("-C", str(work), "switch", "-c", "fresh", trusted_main)
            candidate_file.write_text("fresh worker proposal\n")
            git("-C", str(work), "commit", "-am", "compatible proposal")
            fresh_head = git("-C", str(work), "rev-parse", "HEAD")
            fresh = check(trusted_main, fresh_head)
            self.assertEqual(fresh.returncode, 0, fresh.stderr)

            git("-C", str(work), "switch", "-c", "tampered", trusted_main)
            workflow_file.write_text("on:\n  push:\njobs:\n  test:\n    runs-on: ubuntu-latest\n")
            git("-C", str(work), "commit", "-am", "proposed altered triggers")
            tampered_head = git("-C", str(work), "rev-parse", "HEAD")
            tampered = check(trusted_main, tampered_head)
            self.assertNotEqual(tampered.returncode, 0)
            self.assertIn("workflow tree differs", tampered.stderr)


if __name__ == "__main__":
    unittest.main()
