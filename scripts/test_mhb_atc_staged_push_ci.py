#!/usr/bin/env python3
"""Offline G1 checks: staged ref push isolation and historical workflow-tree binding.

No GitHub credentials, network, staged ref or candidate execution.
"""
from __future__ import annotations

import fnmatch
import os
from pathlib import Path
import re
import subprocess
import tempfile
import textwrap
import unittest

ROOT = Path(__file__).resolve().parents[1]
WORKFLOWS = ROOT / ".github" / "workflows"
STAGED = "hamster/staged/phase2-selfhost/first-pilot"
UNBOUNDED_LEGACY = {
    "phase1-int-001-source-architecture.yml",
    "phase1-int-001-source-systems.yml",
    "phase1-int-001-witness-e2e.yml",
    "phase1-int-002-manifest-closure.yml",
}


def push_properties(source: str):
    """Extract simple top-level on.push branch filters; reject unfamiliar syntax.

    This is a deliberately conservative source-policy check, not a general YAML
    parser or a substitute for GitHub's trigger semantics.
    """
    lines = source.splitlines()
    starts = [(i, line) for i, line in enumerate(lines)
              if re.match(r"^on\s*:", line)]
    if len(starts) != 1 or not re.fullmatch(r"on:\s*(?:#.*)?", starts[0][1]):
        raise ValueError("missing or unsupported top-level on event shape")
    events = []
    for line in lines[starts[0][0] + 1:]:
        if line.strip() and not line[0].isspace() and not line.startswith("#"):
            break
        events.append(line)
    indices = [i for i, line in enumerate(events)
               if re.match(r"^  push\s*:", line)]
    if not indices:
        return None
    if len(indices) != 1 or not re.fullmatch(
            r"  push:\s*(?:#.*)?", events[indices[0]]):
        raise ValueError("unsupported or repeated push trigger")
    body = []
    for line in events[indices[0] + 1:]:
        if re.match(r"^  [a-zA-Z_][a-zA-Z0-9_-]*\s*:", line):
            break
        body.append(line)
    props = {}
    for i, line in enumerate(body):
        m = re.fullmatch(r"    (branches|branches-ignore):\s*(.*)", line)
        if m is None:
            continue
        key, rest = m.groups()
        if key in props:
            raise ValueError("duplicate branch policy key")
        if rest and not rest.startswith("#"):
            if not (rest.startswith("[") and rest.endswith("]")):
                raise ValueError("unsupported inline branch policy")
            values = [v.strip().strip("'\"") for v in rest[1:-1].split(",")]
        else:
            values = []
            for item in body[i + 1:]:
                if not item.strip() or item.lstrip().startswith("#"):
                    continue
                if item.startswith("      - "):
                    values.append(item.strip()[2:].strip().strip("'\""))
                else:
                    break
        if not values or any(not v for v in values):
            raise ValueError("empty/unknown branch policy")
        props[key] = values
    return props


def branch_pattern_disjoint_from_staged(pattern: str) -> bool:
    """Conservative literal-prefix proof, not a permissive glob simulator.

    A branch allow pattern is safe only when its fixed prefix is provably
    incompatible with hamster/staged/. Otherwise deny, even if a particular
    example candidate fails to match it. Supports named Phase 1/hamster lanes
    while rejecting 'hamster/**', '**' and direct staged selectors.
    """
    if pattern.startswith("!"):
        return False  # Glob negation needs a separate ordered-pattern proof.
    marker = re.search(r"[*?\[\]{}!+@()\\]", pattern)
    literal_prefix = pattern[:marker.start()] if marker else pattern
    staged_prefix = "hamster/staged/"
    return not (staged_prefix.startswith(literal_prefix) or
                literal_prefix.startswith(staged_prefix))


def excludes_staged_push(source: str) -> bool:
    props = push_properties(source)
    if props is None:
        return True
    if set(props) == {"branches"}:
        # Allow alternate named lanes only when ALL selectors are provably
        # disjoint from the entire staged namespace, not one sample branch.
        return all(branch_pattern_disjoint_from_staged(p)
                   for p in props["branches"])
    if set(props) == {"branches-ignore"}:
        return "hamster/staged/**" in props["branches-ignore"]
    # No branch restriction, both mutually exclusive keys, or unknown form.
    return False


class StagedPushIsolationTests(unittest.TestCase):
    def test_all_workflow_push_triggers_reject_staged_namespace(self):
        workflows = sorted(WORKFLOWS.glob("*.yml")) + sorted(
            WORKFLOWS.glob("*.yaml"))
        self.assertGreater(len(workflows), 500, "workflow audit corpus missing")
        for path in workflows:
            with self.subTest(workflow=path.name):
                self.assertTrue(excludes_staged_push(path.read_text()),
                                "push is not restricted to main or excludes staged refs")

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
                self.assertEqual(props, {"branches-ignore": ["hamster/staged/**"]})
                self.assertIn("  pull_request:", source)
                self.assertTrue(fnmatch.fnmatchcase(STAGED, props["branches-ignore"][0]))
                self.assertFalse(fnmatch.fnmatchcase("main", props["branches-ignore"][0]))
                self.assertFalse(fnmatch.fnmatchcase("feature/my-work", props["branches-ignore"][0]))
                unprotected = source.replace(
                    "    branches-ignore:\n      - 'hamster/staged/**'\n", "")
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
                        "ham?ter/staged/**", "!hamster/staged/**"):
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
