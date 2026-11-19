#!/usr/bin/env python3
"""Offline W2 fork-to-stage authorization and no-credential regression tests."""
from __future__ import annotations

import copy
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from mhb_atc_worker_broker import (check_paths, check_raw_modes, load_json, resolve,
                                   validate_plan, check_worker_policy)

REPO = "abiggerhammer/phil"
BASE = "a" * 40
HEAD = "b" * 40
MAIN = "c" * 40
FORK = "example/phil"
LANE = "phase2-selfhost"
CANDIDATE = "first-experiment"


def fixtures():
    worker = json.loads((ROOT / ".github/atc-worker-policy.json").read_text())
    registry = json.loads((ROOT / ".github/atc-worker-lanes.json").read_text())
    registry["lanes"][LANE] = {
        "enabled": True, "source_repository": FORK, "source_owner": "example",
        "source_repository_id": 4001, "source_owner_id": 1234}
    source = {
        "id": 4001, "full_name": FORK, "fork": True, "private": False,
        "parent": {"full_name": REPO},
        "owner": {"login": "example", "id": 1234}}
    ref = {
        "ref": f"refs/heads/hamster/proposed/{LANE}/{CANDIDATE}",
        "object": {"type": "commit", "sha": HEAD}}
    return worker, registry, source, ref, [], []


def authorize(f, **changes):
    worker, registry, source, ref, refs, issues = copy.deepcopy(f)
    return resolve(worker, registry, repo=changes.get("repo", REPO),
                   actor=changes.get("actor", "abiggerhammer"),
                   lane=changes.get("lane", LANE),
                   candidate=changes.get("candidate", CANDIDATE))


def plan(f, **changes):
    worker, registry, source, ref, refs, issues = copy.deepcopy(f)
    binding = authorize(f)
    return validate_plan(binding, base_sha=changes.get("base_sha", BASE),
                         head_sha=changes.get("head_sha", HEAD),
                         main_sha=changes.get("main_sha", MAIN),
                         source_repository=changes.get("source", source),
                         source_ref=changes.get("ref", ref),
                         staged_refs=changes.get("refs", refs),
                         issues=changes.get("issues", issues))


class WorkerBrokerTests(unittest.TestCase):
    def setUp(self):
        self.f = fixtures()

    def test_reviewed_policy_starts_with_zero_active_lanes(self):
        w, r, *_ = fixtures()
        actual = json.loads((ROOT / ".github/atc-worker-lanes.json").read_text())
        self.assertEqual(actual["allowed_dispatch_actors"], ["abiggerhammer"])
        self.assertEqual(actual["source_model"], "public-github-fork")
        self.assertTrue(actual["pilot_only"])
        self.assertEqual(set(actual["lanes"]),
                         {"phase2-selfhost", "phase2-embedded"})
        self.assertTrue(all(not x["enabled"] and
                            x["source_repository"] is None and
                            x["source_owner"] is None and
                            x["source_repository_id"] is None and
                            x["source_owner_id"] is None
                            for x in actual["lanes"].values()))
        self.assertEqual(check_worker_policy(w), "disabled")

    def test_disabled_lane_cannot_enter_even_plan(self):
        w, r, *_ = self.f
        r["lanes"][LANE]["enabled"] = False
        with self.assertRaisesRegex(ValueError, "not enabled"):
            resolve(w, r, repo=REPO, actor="abiggerhammer",
                    lane=LANE, candidate=CANDIDATE)

    def test_valid_operator_mediated_fork_resolution(self):
        got = authorize(self.f)
        self.assertEqual(got["source_repository"], FORK)
        self.assertEqual(got["source_ref"],
                         f"hamster/proposed/{LANE}/{CANDIDATE}")
        self.assertEqual(got["staged_branch"],
                         f"hamster/staged/{LANE}/{CANDIDATE}")
        self.assertEqual(got["broker_source_activation"], "disabled")

    def test_valid_snapshot_plan_is_read_only(self):
        got = plan(self.f)
        self.assertEqual(got["decision"], "validated-read-only-plan")
        self.assertIn("create-only", got["scope"])
        self.assertEqual(got["base_sha"], BASE)
        self.assertEqual(got["head_sha"], HEAD)
        self.assertEqual(got["main_sha"], MAIN)

    def test_cannot_invent_another_actor(self):
        for actor in ("octocat", "github-actions[bot]", "phil-atc-worker[bot]",
                      "", "abiggerhammer\n", "abiggerhammer "):
            with self.subTest(actor=actor), self.assertRaises(ValueError):
                authorize(self.f, actor=actor)

    def test_cannot_target_other_repo_or_lane(self):
        for item in ("other/repo", "", "abiggerhammer/PHIL"):
            with self.subTest(repo=item), self.assertRaises(ValueError):
                authorize(self.f, repo=item)
        for item in ("phase2-embedded", "phase2-selfhostX",
                     "mhb-atc", "Phase2-selfhost", "phase2-selfhost/other", ""):
            with self.subTest(lane=item), self.assertRaises(ValueError):
                authorize(self.f, lane=item)

    def test_candidate_ref_injection_denied(self):
        for item in ("", "../foo", "go/other", "go.lock",
                     "a@{x}", "--delete", "a\nb", "a b",
                     "X", "-x", "x-", "x" * 67):
            with self.subTest(candidate=item), self.assertRaises(ValueError):
                authorize(self.f, candidate=item)

    def test_registry_cannot_redirect_to_another_source_or_unsafe_path(self):
        for repo, owner in [
            (REPO, "abiggerhammer"), ("example/other", "someone"),
            ("example/../phil", "example"), ("https://evil.test/a", "https:"),
            ("example/phil.git/extra", "example"), ("", "example"),
            ("example/phil", "../example"),
        ]:
            w, r, *_ = copy.deepcopy(self.f)
            r["lanes"][LANE]["source_repository"] = repo
            r["lanes"][LANE]["source_owner"] = owner
            with self.subTest(repo=repo, owner=owner), self.assertRaises(ValueError):
                resolve(w, r, repo=REPO, actor="abiggerhammer",
                        lane=LANE, candidate=CANDIDATE)

    def test_worker_policy_requires_exact_broker_identity_and_custody(self):
        for key, value in [
            ("worker_app_id", 5782193), ("worker_app_slug", "phil-atc-publisher"),
            ("repository", "other/repo"), ("environment", "atc-publisher"),
            ("direct_worker_installation_tokens", True),
            ("credential_holder", "hamster"),
            ("broker_activation", "surprise"),
            ("intended_permissions", {"contents": "write", "pull_requests": "write"}),
        ]:
            w, r, *_ = copy.deepcopy(self.f)
            w[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                resolve(w, r, repo=REPO, actor="abiggerhammer",
                        lane=LANE, candidate=CANDIDATE)

    def test_source_id_mismatch_denied_even_if_names_reused(self):
        src = copy.deepcopy(self.f[2])
        src["id"] = 4002
        with self.assertRaisesRegex(ValueError, "source must be"):
            plan(self.f, source=src)
        src = copy.deepcopy(self.f[2])
        src["owner"]["id"] = 1235
        with self.assertRaisesRegex(ValueError, "source must be"):
            plan(self.f, source=src)
        for field in ("source_repository_id", "source_owner_id"):
            w, reg, *_ = copy.deepcopy(self.f)
            reg["lanes"][LANE][field] = None
            with self.subTest(field=field), self.assertRaises(ValueError):
                resolve(w, reg, repo=REPO, actor="abiggerhammer",
                        lane=LANE, candidate=CANDIDATE)

    def test_actual_fork_and_owner_required(self):
        for key, value in [
            ("full_name", "bad/phil"), ("fork", False), ("private", True),
            ("id", "4001"), ("parent", {"full_name": "other/repo"}),
            ("owner", {"login": "attacker", "id": 1234}),
            ("owner", {"login": "example", "id": False}),
        ]:
            src = copy.deepcopy(self.f[2])
            src[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                plan(self.f, source=src)

    def test_exact_source_ref_commit_and_type_required(self):
        for key, value in [
            ("ref", "refs/heads/hamster/proposed/phase2-embedded/x"),
            ("ref", "refs/heads/hamster/proposed/phase2-selfhost/other"),
            ("object", {"sha": HEAD, "type": "tag"}),
            ("object", {"sha": BASE, "type": "commit"}),
            ("object", None),
        ]:
            obj = copy.deepcopy(self.f[3])
            obj[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                plan(self.f, ref=obj)

    def test_shas_are_exact_and_nonzero(self):
        for field in ("base_sha", "head_sha", "main_sha"):
            for value in ("", "0" * 40, "b" * 39, "Z" * 40, HEAD + "\n"):
                with self.subTest(field=field, value=value):
                    with self.assertRaises(ValueError):
                        plan(self.f, **{field: value})
        for values in [
            {"base_sha": HEAD}, {"head_sha": BASE},
            {"head_sha": MAIN}, {"base_sha": MAIN, "head_sha": MAIN},
        ]:
            with self.subTest(values=values), self.assertRaises(ValueError):
                plan(self.f, **values)

    def test_stage_namespace_is_create_only(self):
        for branch in [
            f"refs/heads/hamster/staged/{LANE}/{CANDIDATE}",
            f"refs/heads/hamster/staged/{LANE}/another",
        ]:
            with self.subTest(branch=branch), self.assertRaisesRegex(
                    ValueError, "existing staged ref"):
                plan(self.f, refs=[{"ref": branch, "object": {"sha": HEAD}}])
        # Similar lane name is not the same lane; snapshot can include it.
        got = plan(self.f, refs=[
            {"ref": "refs/heads/hamster/staged/phase2-selfhost-X/x"}])
        self.assertEqual(got["decision"], "validated-read-only-plan")
        with self.assertRaisesRegex(ValueError, "malformed staged-ref"):
            plan(self.f, refs=[{"wrong": "field"}])

    def test_stage_issue_orphan_refusal(self):
        for issue in [
            {"title": f"ATC candidate: hamster/staged/{LANE}/x", "labels": []},
            {"title": "anything", "labels": [
                {"name": "atc: staged"}, {"name": f"lane: {LANE}"}]},
        ]:
            with self.subTest(issue=issue), self.assertRaisesRegex(
                    ValueError, "existing staged candidate|unowned/ambiguous"):
                plan(self.f, issues=[issue])
        with self.assertRaisesRegex(ValueError, "malformed issue"):
            plan(self.f, issues=[{"title": "anything", "labels": [1]}])

    def test_one_active_admitted_and_one_staged_successor_allowed(self):
        accepted = {"title": f"ATC candidate: hamster/staged/{LANE}/previous",
                    "labels": [{"name": f"lane: {LANE}"},
                               {"name": "atc: admitted"}]}
        got = plan(self.f, issues=[accepted])
        self.assertEqual(got["decision"], "validated-read-only-plan")
        second = copy.deepcopy(accepted)
        second["labels"][-1]["name"] = "atc: admitting"
        with self.assertRaisesRegex(ValueError, "multiple active"):
            plan(self.f, issues=[accepted, second])
        bad = copy.deepcopy(accepted)
        bad["labels"].append({"name": "atc: staged"})
        with self.assertRaisesRegex(ValueError, "existing staged"):
            plan(self.f, issues=[bad])
        bad = copy.deepcopy(accepted)
        bad["labels"].append({"name": "atc: admitting"})
        with self.assertRaisesRegex(ValueError, "ambiguous"):
            plan(self.f, issues=[bad])

    def test_repository_snapshot_fail_closed(self):
        for name, value in [
            ("source_repository", None), ("source_ref", None),
            ("staged_refs", None), ("issues", None),
        ]:
            binding = authorize(self.f)
            kwargs = {"base_sha": BASE, "head_sha": HEAD, "main_sha": MAIN,
                      "source_repository": self.f[2], "source_ref": self.f[3],
                      "staged_refs": [], "issues": []}
            kwargs[name] = value
            with self.subTest(name=name), self.assertRaises(ValueError):
                validate_plan(binding, **kwargs)

    def test_changed_paths_allow_source_but_reject_trust_and_unusual_names(self):
        got = check_paths(b"src/Phil/Parser.hs\0proof/Phil/Core/Test.v\0")
        self.assertEqual(got["changed_files"], 2)
        for item in [
            b".github/workflows/evil.yml", b".GITHUB/policy.json",
            b"scripts/mhb_atc_admit.py", b"scripts/MHB_ATC_worker.py",
            b".gitmodules", b".gitattributes", b"a/../b", b"/absolute",
            b"a\nb", b"a\\b", b"a//b",
        ]:
            with self.subTest(path=item), self.assertRaises(ValueError):
                check_paths(item + b"\0")
        for raw in (b"", b"a", b"\0", b"a\0\0"):
            with self.subTest(raw=raw), self.assertRaises(ValueError):
                check_paths(raw)

    def test_git_raw_modes_match_paths_and_reject_symlinks_or_gitlinks(self):
        old, new = b"a" * 40, b"b" * 40
        raw = (b":100644 100755 " + old + b" " + new +
               b" M\0src/Main.hs\0")
        accepted = check_raw_modes(raw, b"src/Main.hs\0")
        self.assertEqual(accepted["changed_files"], 1)
        for modes in (b"120000 100644", b"100644 120000",
                      b"160000 100644", b"100644 160000"):
            bad = b":" + modes + b" " + old + b" " + new + b" M\0src/Main.hs\0"
            with self.subTest(modes=modes), self.assertRaisesRegex(
                    ValueError, "mode"):
                check_raw_modes(bad, b"src/Main.hs\0")
        for wrong in (b"other.hs\0", b"src/Main.hs\0extra.hs\0"):
            with self.subTest(paths=wrong), self.assertRaisesRegex(
                    ValueError, "disagree"):
                check_raw_modes(raw, wrong)
        with self.assertRaisesRegex(ValueError, "raw-diff"):
            check_raw_modes(b"bad", b"src/Main.hs\0")

    def test_load_json_rejects_duplicate_keys(self):
        with tempfile.TemporaryDirectory() as d:
            f = Path(d) / "p.json"
            f.write_text('{"enabled": false, "enabled": true}')
            with self.assertRaisesRegex(ValueError, "duplicate JSON key"):
                load_json(str(f))

    def test_cli_resolve_without_network_needs_explicit_lane_source(self):
        cmd = [
            sys.executable, str(ROOT / "scripts/mhb_atc_worker_broker.py"),
            "resolve", "--worker-policy", str(ROOT / ".github/atc-worker-policy.json"),
            "--lane-policy", str(ROOT / ".github/atc-worker-lanes.json"),
            "--repo", REPO, "--actor", "abiggerhammer",
            "--lane", LANE, "--candidate", CANDIDATE,
        ]
        ran = subprocess.run(cmd, capture_output=True, text=True)
        self.assertEqual(ran.returncode, 2)
        self.assertIn("lane not enabled", ran.stderr)

    def test_dormant_source_workflow_cannot_mint_without_explicit_gates(self):
        text = (ROOT / ".github/workflows/mhb-atc-worker-broker.yml").read_text()
        self.assertIn("\non:\n  workflow_dispatch:\n", text)
        self.assertIn("github.ref == 'refs/heads/main'", text)
        self.assertIn("github.actor == 'abiggerhammer'", text)
        self.assertIn("environment: atc-worker-broker", text)
        self.assertIn("persist-credentials: false", text)
        self.assertIn("MHB_ATC_WORKER_BROKER_ENABLED", text)
        self.assertIn("broker_activation", text)
        self.assertIn("== \"enabled\"", text)
        self.assertIn("git-askpass", text)
        self.assertIn("--force-with-lease=", text)
        self.assertIn("gh api --method POST", text)
        self.assertIn("permission-contents: write", text)
        self.assertIn('GH_TOKEN="$WORKER_TOKEN" gh api "installation/repositories"', text)
        self.assertIn('(.total_count == 1)', text)
        self.assertLess(text.index('GH_TOKEN="$WORKER_TOKEN" gh api "installation/repositories"'),
                        text.index('push --porcelain'))
        self.assertNotIn("permission-pull-requests:", text)
        self.assertNotIn("gh pr create", text)
        self.assertNotIn("git checkout ", text)
        self.assertNotIn("git submodule update", text)
        self.assertNotIn("github.event.client_payload", text)
        # Any broadening of the token action's explicit requested permissions
        # changes the established intended GitHub authority.
        block = text.split("      - name: Mint dedicated broker-held worker App token", 1)[1].split(
            "      - name: Create-only staged push and register candidate", 1)[0]
        requested = re.findall(r"(?m)^\s+(permission-[a-z-]+:\s+\w+)\s*$", block)
        self.assertEqual(requested, ["permission-contents: write"])


if __name__ == "__main__":
    unittest.main()
