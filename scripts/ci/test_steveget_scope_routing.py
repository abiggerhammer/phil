"""Offline controls for the workflow entry point, using actual Git and claim code."""
import base64
import contextlib
import copy
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
import urllib.error

import steveget_scope_routing as routing

WORKFLOW_05 = ".github/workflows/fsem05-steveget-selected-source-event.yml"
WORKFLOW_06 = ".github/workflows/fsem06-steveget-core-payload-refinement.yml"
HISTORICAL_05 = {
    WORKFLOW_05: "A",
    "docs/phase-1/fsem05-steveget-qualified-source-event-v1.md": "A",
    "phil-core.cabal": "M",
    "proof/Phil/Verification/FSEM05SteveGetSelectedSourceEvents.v": "A",
    "src/Phil/Surface/SelectedSteveGetExecution.hs": "A",
    "test/FSEM05SteveGetSelectedSourceEventMain.hs": "A",
}
HISTORICAL_06 = dict.fromkeys([
    WORKFLOW_06,
    "docs/phase-1/fsem06-steveget-core-payload-execution-v1.md",
    "proof/Phil/Verification/FSEM06SteveGetSelectedCorePayloadRefinement.v",
    "src/Phil/Compiler/SelectedSteveGetCoreExecution.hs",
    "test/FSEM06SteveGetSelectedCorePayloadMain.hs",
], "A")
D3 = {
    ".github/workflows/fsem05-doubleping-d3-preflight.yml": "A",
    "docs/phase-1/formal-semantics-doubleping-d3-fsem05-v1.md": "A",
    "phil-core.cabal": "M",
    "proof/Phil/Surface/DoublePingD3.v": "A",
    "src/Phil/Surface/GrammarV1/DoublePingExecution.hs": "A",
    "test/Phase1FSEM05DoublePingExecutionMain.hs": "A",
    "test/Phase1FSEM05DoublePingExecutionPrivateMain.hs": "A",
}
REC02B = {
    "src/Phil/Surface/Syntax.hs": "M",
    "src/Phil/Surface/Check/Engine.hs": "M",
    "src/Phil/Surface/Check/Preflight.hs": "M",
    "src/Phil/Surface/GrammarV1/RecordSourceIdentity.hs": "M",
    "src/Phil/Compiler.hs": "M",
    "src/Phil/Compiler/SourceArchitecture.hs": "M",
    "src/Phil/Compiler/SourceCore.hs": "M",
    "phil-core.cabal": "M",
    "src/Phil/Surface/GrammarV1/CheckedRecordProjection.hs": "A",
    "test/Phase1FSEM01Rec02BProductionMain.hs": "A",
    "test/Phase1FSEM01Rec02BProductionPrivate.ghci": "A",
    "test/fixtures/fsem01-rec02b-production-v1/equal-typed.phil": "A",
    "test/fixtures/fsem01-rec02b-production-v1/equal-typed.tsv": "A",
    "proof/Phil/Surface/RecordProductionREC02B.v": "A",
    "docs/phase-1/formal-semantics-record-production-rec02b-fsem01-v1.md": "A",
    ".github/workflows/fsem01-rec02b-production-preflight.yml": "A",
}
REPAIR = {WORKFLOW_05: "M", WORKFLOW_06: "M", routing.HELPER: "A",
          routing.TEST: "A", routing.DOCUMENT: "A"}
CLAIM = "c" * 40
EVIDENCE = os.getenv("STEVEGET_TEST_EVIDENCE") == "1"
REPO = {"id": 1341890518, "full_name": "abiggerhammer/phil"}
FORK = {"id": 2468, "full_name": "fork/phil"}
CHECKOUT = Path(__file__).resolve().parents[2]


def command(*args, stdin=None):
    return subprocess.check_output(["git", *args], input=stdin, stderr=subprocess.PIPE)


class RoutingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.controller = command("-C", str(CHECKOUT), "show", "HEAD:scripts/fsem_claim.py")

    def setUp(self):
        directory = self.enterContext(tempfile.TemporaryDirectory())
        self.enterContext(contextlib.chdir(directory))
        self.enterContext(patch.dict(os.environ, {
            "GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": os.devnull,
            "GIT_AUTHOR_DATE": "2026-11-26T00:00:00Z",
            "GIT_COMMITTER_DATE": "2026-11-26T00:00:00Z",
        }))
        command("init", "-q", "-b", "main")
        command("config", "user.name", "Fixture")
        command("config", "user.email", "fixture@example.test")
        Path("scripts").mkdir()
        Path("scripts/fsem_claim.py").write_bytes(self.controller)
        self.write("phil-core.cabal", "original")
        self.root = self.snapshot("root")
        self.event_path = Path(directory, ".git/event.json")
        self.requests = []
        self.network = self.enterContext(patch("urllib.request.urlopen", side_effect=self.respond))
        self.record = None
        self.comments = None
        self.claim_sha = CLAIM
        self.api_failure = None
        self.missing_ref = False

    def write(self, filename, body):
        path = Path(filename)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(body)

    def snapshot(self, reason):
        command("add", "-A")
        command("commit", "-qm", reason, "--allow-empty")
        return command("rev-parse", "HEAD").decode().strip()

    def select(self, commit):
        command("checkout", "-q", "--detach", commit)

    def changes(self, statuses):
        for filename, status in statuses.items():
            if status == "D":
                Path(filename).unlink()
            else:
                self.write(filename, f"changed {filename}\n")
        return self.snapshot("changed paths")

    def merge_subject(self, base, head, tree=None):
        tree = tree or head
        return command("commit-tree", f"{tree}^{{tree}}", "-p", base, "-p", head,
                       stdin=b"synthetic integration\n").decode().strip()

    def inputs(self, profile, kind, subject, ref):
        return {"GITHUB_EVENT_PATH": str(self.event_path),
                "GITHUB_EVENT_NAME": kind, "GITHUB_SHA": subject, "GITHUB_REF": ref,
                "GITHUB_REPOSITORY_ID": str(REPO["id"]), "GITHUB_REPOSITORY": REPO["full_name"],
                "GITHUB_WORKFLOW_SHA": subject,
                "GITHUB_WORKFLOW_REF": f'{REPO["full_name"]}/.github/workflows/'
                                       f'{routing.PROFILES[profile].workflow}@{ref}'}

    def pr(self, profile, head, *, base=None, head_ref="infra/ordinary", head_repo=REPO,
           base_ref="main", subject=None):
        base = base or self.root
        subject = subject or self.merge_subject(base, head)
        self.select(subject)
        env = self.inputs(profile, "pull_request", subject, "refs/pull/18/merge")
        env.update(GITHUB_HEAD_REF=head_ref, GITHUB_BASE_REF=base_ref)
        event = {"repository": copy.deepcopy(REPO), "action": "opened", "number": 18,
                 "pull_request": {"number": 18, "state": "open",
                                  "base": {"repo": copy.deepcopy(REPO), "ref": base_ref, "sha": base},
                                  "head": {"repo": copy.deepcopy(head_repo), "ref": head_ref, "sha": head}}}
        return event, env

    def historical(self, profile, head, **kwargs):
        return self.pr(profile, head, head_ref=routing.PROFILES[profile].branch, **kwargs)

    def respond(self, request, timeout):
        self.assertEqual(request.get_method(), "GET")
        self.assertIsNone(request.data)
        self.assertEqual(request.get_header("Authorization"), "Bearer fixture-token")
        url = request.full_url.removeprefix("https://api.github.com/repos/abiggerhammer/phil")
        self.requests.append(url)
        if self.api_failure and self.api_failure in url:
            raise urllib.error.HTTPError(url, 403, "fixture forbidden", {}, io.BytesIO(b"fixture-token"))
        if url.startswith("/git/ref/"):
            self.assertEqual(url, f"/git/ref/heads/coord/fsem-claims/{self.requested_family}")
            if self.missing_ref:
                raise urllib.error.HTTPError(url, 404, "absent", {}, io.BytesIO(b""))
            return io.BytesIO(json.dumps({
                "ref": url.removeprefix("/git").replace("/ref/", "refs/", 1),
                "object": {"sha": self.claim_sha, "type": "commit"},
            }).encode())
        if url.startswith("/contents/"):
            self.assertEqual(url, f"/contents/.fsem-claim.json?ref={self.claim_sha}")
            encoded = base64.b64encode(json.dumps(self.record).encode()).decode()
            return io.BytesIO(json.dumps({"encoding": "base64", "content": encoded}).encode())
        self.assertEqual(url, "/issues/1613/comments?per_page=100&page=1")
        return io.BytesIO(json.dumps(self.comments).encode())

    def fixture_claim(self, profile):
        chosen = routing.PROFILES[profile]
        self.requested_family = chosen.family
        self.record = {"version": 1, "slice": chosen.family, "lane": "formal-semantics",
                       "issue": 1613, "branch": chosen.branch, "actor": chosen.actor,
                       "main_sha": self.root, "claimed_at": "2026-11-26T00:00:00Z"}
        self.comments = [self.issue_comment()]

    def issue_comment(self, *, sha=CLAIM):
        data = dict(self.record, claim_commit=sha)
        return {"body": "<!-- FSEM-SLICE-CLAIM-V1 -->\n"
                        "```json\n" + json.dumps(data) + "\n```\n"}

    def receipt(self, profile, event, env, expected, *, diagnostic=None):
        data = event if isinstance(event, bytes) else json.dumps(event).encode()
        self.event_path.write_bytes(data)
        logs = []
        result = routing.run(profile, env, logs.append)
        self.assertEqual(len(logs), 1)
        self.assertNotIn("fixture-token", logs[0])
        if EVIDENCE:
            print(f"{self._testMethodName} {logs[0]}")
        evidence = json.loads(logs[0])
        self.assertEqual(evidence["route"], expected, evidence)
        self.assertEqual(result, int(expected == "REFUSE"), evidence)
        if diagnostic:
            self.assertIn(diagnostic, evidence["diagnostic"])
        if expected != "APPLICABLE":
            self.assertNotIn("claim_sha", evidence)
        if expected == "N/A":
            self.assertEqual(evidence["diagnostic"], routing.NA)
        return evidence

    def check_old(self, paths):
        return (bool(paths) and set(paths) <= HISTORICAL_05.keys(),
                len(paths) == 5 and paths == HISTORICAL_06)

    def test_exact_historical_fixtures_and_live_controller(self):
        for profile, paths, old in [("fsem05", HISTORICAL_05, (True, False)),
                                    ("fsem06", HISTORICAL_06, (False, True))]:
            with self.subTest(profile=profile):
                self.select(self.root)
                head = self.changes(paths)
                self.assertEqual(self.check_old(paths), old)
                event, env = self.historical(profile, head)
                self.fixture_claim(profile)
                env["GH_TOKEN"] = "fixture-token"
                self.requests.clear()
                proof = self.receipt(profile, event, env, "APPLICABLE")
                self.assertEqual(proof["claim_sha"], CLAIM)
                self.assertEqual(len(self.requests), 3)
                self.assertEqual({p[0]: s for s, p in proof["changes"]}, paths)

    def test_fsem05_strict_subset_empty_and_forbidden(self):
        self.fixture_claim("fsem05")
        for paths, expected in [({"phil-core.cabal": "M"}, "APPLICABLE"),
                                ({}, "REFUSE"), ({"forbidden": "A"}, "REFUSE")]:
            with self.subTest(paths=paths):
                self.select(self.root)
                event, env = self.historical("fsem05", self.changes(paths))
                env["GH_TOKEN"] = "fixture-token"
                self.requests.clear()
                self.receipt("fsem05", event, env, expected)
                self.assertEqual(len(self.requests), 3 if expected == "APPLICABLE" else 0)

    def test_fsem05_name_only_rename_destination_matches_old_git(self):
        target = next(iter(sorted(HISTORICAL_05)))
        self.write("unrelated-old", "same contents")
        start = self.snapshot("rename base")
        Path(target).parent.mkdir(parents=True)
        command("mv", "unrelated-old", target)
        head = self.snapshot("rename")
        event, env = self.historical("fsem05", head, base=start)
        env["GH_TOKEN"] = "fixture-token"
        self.fixture_claim("fsem05")
        result = self.receipt("fsem05", event, env, "APPLICABLE")
        old = command("diff", "--name-only", f"{start}...{head}").decode().splitlines()
        self.assertEqual(old, result["predicate_paths"])
        self.assertEqual([target], old)

    def test_fsem06_missing_extra_modified_deleted_and_renamed(self):
        path = WORKFLOW_06
        for fault in ("missing", "extra", "modified", "deleted", "renamed", "copy"):
            with self.subTest(fault=fault):
                self.select(self.root)
                paths = HISTORICAL_06.copy()
                if fault in {"modified", "deleted"}:
                    self.write(path, "existing")
                    paths[path] = "M" if fault == "modified" else "D"
                if fault in {"renamed", "copy"}:
                    self.write("old", "original content" * 20)
                    del paths[path]
                if fault == "copy":
                    command("config", "diff.renames", "copies")
                else:
                    command("config", "diff.renames", "true")
                base = self.snapshot("base")
                if fault == "missing":
                    del paths[path]
                if fault == "extra":
                    paths["extra"] = "A"
                if fault == "renamed":
                    Path(path).parent.mkdir(parents=True, exist_ok=True)
                    command("mv", "old", path)
                if fault == "copy":
                    self.write(path, Path("old").read_text())
                    paths["old"] = "M"
                event, env = self.historical("fsem06", self.changes(paths), base=base)
                proof = self.receipt("fsem06", event, env, "REFUSE", diagnostic="five unique")
                if fault in {"renamed", "copy"}:
                    self.assertIn("R" if fault == "renamed" else "C",
                                  {status[0] for status, _ in proof["changes"]})
        self.network.assert_not_called()

    def test_status_record_parser_and_duplicate_additions(self):
        def check(raw):
            with patch.object(routing, "git", return_value=raw):
                return routing.status_paths("base", "head")
        for malformed in (b"A\0file", b"A\0\0", b"A\0", b"QQ\0file\0",
                          b"R101\0old\0new\0", b"R100\0old\0"):
            with self.subTest(raw=malformed):
                with self.assertRaises(routing.Refusal):
                    check(malformed)
        self.assertEqual(check(b"A\0a\nb\t\xff\0")[0][1], [os.fsdecode(b"a\nb\t\xff")])
        for duplicate in ([(status, [path]) for path, status in HISTORICAL_06.items()] +
                          [("A", [WORKFLOW_06])],
                          [("A", [WORKFLOW_06])] * 5):
            with self.assertRaisesRegex(routing.Refusal, "five unique"):
                routing.enforce_paths(routing.PROFILES["fsem06"], "", "", duplicate, {})

    def test_claim_faults_fail_applicable_without_na(self):
        profile = "fsem05"
        event, env = self.historical(profile, self.changes(HISTORICAL_05))
        env["GH_TOKEN"] = "fixture-token"
        faults = ["actor", "branch", "slice", "sha", "zero", "missing", "duplicate",
                  "mismatched", "released", "restored-release", "api", "token"]
        for fault in faults:
            with self.subTest(fault=fault):
                self.fixture_claim(profile)
                self.claim_sha, self.api_failure, self.missing_ref = CLAIM, None, False
                current_env = env.copy()
                if fault in {"actor", "branch", "slice"}:
                    self.record[fault] = "formal-semantics/wrong"
                    self.comments = [self.issue_comment()]
                if fault == "sha":
                    self.claim_sha = "d" * 40
                if fault == "zero":
                    self.claim_sha = "0" * 40
                if fault == "missing":
                    self.comments = []
                if fault == "duplicate":
                    self.comments *= 2
                if fault == "mismatched":
                    self.comments = [{"body": self.comments[0]["body"].replace(self.record["actor"], "wrong")}]
                if fault == "released":
                    self.missing_ref = True
                if fault == "restored-release":
                    self.comments += [{"body": "<!-- FSEM-SLICE-RELEASE-V1 -->\n"
                                               f"Released `fsem-05` claim `{CLAIM}` after a PR closed."}]
                if fault == "api":
                    self.api_failure = "/issues/"
                if fault == "token":
                    current_env.pop("GH_TOKEN")
                self.receipt(profile, event, current_env, "REFUSE")

    def test_nonhistorical_matrix_and_old_negative_controls(self):
        branches = {
            "D3": ("formal-semantics/fsem05-doubleping-d3-execution", D3),
            "REC02B": ("formal-semantics/fsem01-rec02b-production", REC02B),
            "repair": ("infra/steveget-scope-routing", REPAIR),
            "Cabal": ("infra/cabal-only", {"phil-core.cabal": "M"}),
            "unrelated": ("infra/unrelated", {"elsewhere": "A"}),
            "helper": ("infra/helper", {routing.HELPER: "A", routing.TEST: "A"}),
            "direct": ("infra/direct", {WORKFLOW_06: "A"}),
            "substring": ("prefix/" + routing.PROFILES["fsem05"].branch, {"elsewhere": "A"}),
        }
        self.assertEqual((len(D3), len(REC02B)), (7, 16))
        for case, (head_ref, paths) in branches.items():
            with self.subTest(case=case):
                self.select(self.root)
                for name, status in paths.items():
                    if status == "M" and not Path(name).is_file():
                        self.write(name, "before")
                base = self.snapshot("base")
                head = self.changes(paths)
                if case in {"D3", "REC02B", "repair"}:
                    self.assertEqual(self.check_old(paths), (False, False))
                for profile in routing.PROFILES:
                    event, env = self.pr(profile, head, base=base, head_ref=head_ref)
                    event["pull_request"].update(labels=[{"name": "lane: formal-semantics"}],
                                                 body="FSEM-Slice: fsem-05\nFSEM-Slice: fsem-06")
                    evidence = self.receipt(profile, event, env, "N/A")
                    self.assertEqual(evidence.get("classification"),
                                     "owner-review-required" if case in {"repair", "helper", "direct"} else None)
                    self.assertEqual({p[0]: s for s, p in evidence["changes"]}, paths)
        self.network.assert_not_called()

    def test_deleted_legacy_and_rename_origin_require_review(self):
        self.write(WORKFLOW_05, "old")
        self.write(WORKFLOW_06, "will be deleted")
        base = self.snapshot("base")
        command("mv", WORKFLOW_05, "outside")
        head = self.changes({WORKFLOW_06: "D"})
        event, env = self.pr("fsem05", head, base=base)
        result = self.receipt("fsem05", event, env, "N/A")
        self.assertEqual(result["direct_paths"], [WORKFLOW_05, WORKFLOW_06])

    def test_fork_and_wrong_base(self):
        head = self.changes({"other": "A"})
        for profile in routing.PROFILES:
            event, env = self.pr(profile, head, head_repo=FORK)
            self.receipt(profile, event, env, "N/A")
            event, env = self.historical(profile, head, head_repo=FORK)
            self.receipt(profile, event, env, "REFUSE", diagnostic="same-repository")
            event, env = self.historical(profile, head, base_ref="dev")
            self.receipt(profile, event, env, "REFUSE", diagnostic="main base")
        self.network.assert_not_called()

    def test_event_schema_ref_repository_and_checkout_fail_closed(self):
        head = self.changes({"other": "A"})
        original, original_env = self.pr("fsem05", head)
        changes = [
            lambda e, v: e.update(action="closed"),
            lambda e, v: e.update(action=[]),
            lambda e, v: e.update(number=True),
            lambda e, v: e["pull_request"].update(number=19),
            lambda e, v: e["pull_request"].update(state="closed"),
            lambda e, v: e["pull_request"]["head"].update(repo=None),
            lambda e, v: e["pull_request"]["head"].update(repo=dict(REPO, id=8)),
            lambda e, v: e["pull_request"]["head"].update(repo=dict(REPO, id=True)),
            lambda e, v: e["pull_request"]["base"].update(repo=FORK),
            lambda e, v: e["pull_request"]["head"].update(sha="0" * 40),
            lambda e, v: e["pull_request"]["head"].update(ref="bad..branch"),
            lambda e, v: e["pull_request"]["head"].update(sha="F" * 40),
            lambda e, v: e["pull_request"]["base"].update(sha=head),
            lambda e, v: e.update(repository=FORK),
            lambda e, v: v.update(GITHUB_REPOSITORY_ID="1"),
            lambda e, v: v.update(GITHUB_REPOSITORY="fork/phil"),
            lambda e, v: v.update(GITHUB_BASE_REF="wrong"),
            lambda e, v: v.update(GITHUB_HEAD_REF="wrong"),
            lambda e, v: v.update(GITHUB_REF="refs/pull/999/merge"),
            lambda e, v: v.update(GITHUB_SHA=self.root),
            lambda e, v: v.update(GITHUB_WORKFLOW_SHA="0" * 40),
            lambda e, v: v.update(GITHUB_WORKFLOW_REF="wrong"),
            lambda e, v: v.update(GITHUB_EVENT_NAME="workflow_dispatch"),
        ]
        for number, mutate in enumerate(changes):
            with self.subTest(case=number):
                event, env = copy.deepcopy(original), original_env.copy()
                mutate(event, env)
                self.receipt("fsem05", event, env, "REFUSE")
        for bad_json in (b"[]", b"null", b"{", b'{"x":1,"x":2}', b'{"x":NaN}'):
            self.receipt("fsem05", bad_json, original_env, "REFUSE")
        self.network.assert_not_called()

    def test_exact_event_comparison_not_synthetic_tree_or_moving_main(self):
        head = self.changes({"only-head": "A"})
        self.select(self.root)
        base = self.changes({"only-base": "A"})
        different_tree = self.changes({"only-synthetic": "A"})
        distinct_main = self.changes({"only-moving": "A"})
        command("update-ref", "refs/remotes/origin/main", distinct_main)
        subject = self.merge_subject(base, head, different_tree)
        event, env = self.pr("fsem05", head, base=base, subject=subject)
        proof = self.receipt("fsem05", event, env, "N/A")
        self.assertEqual((proof["base"], proof["head"], proof["merge_base"], proof["subject"]),
                         (base, head, self.root, subject))
        self.assertEqual(proof["changes"], [["A", ["only-head"]]])

    def test_absent_commit_and_multiple_merge_bases(self):
        absent = "f" * 40
        head = self.changes({"head": "A"})
        raw = (f"tree {command('rev-parse', 'HEAD^{tree}').decode().strip()}\n"
               f"parent {self.root}\nparent {absent}\n"
               "author Fixture <fixture@example.test> 10 +0000\n"
               "committer Fixture <fixture@example.test> 10 +0000\n\ninvalid\n")
        bad = command("hash-object", "-t", "commit", "-w", "--stdin", stdin=raw.encode()).decode().strip()
        event, env = self.pr("fsem05", absent, subject=bad)
        self.receipt("fsem05", event, env, "REFUSE", diagnostic="Git")
        self.select(self.root)
        other = self.changes({"other": "A"})
        a = self.merge_subject(head, other)
        b = self.merge_subject(other, head)
        event, env = self.pr("fsem05", b, base=a)
        self.receipt("fsem05", event, env, "REFUSE", diagnostic="exactly one merge base")

    def push(self, profile, head, before):
        ref = "refs/heads/" + routing.PROFILES[profile].branch
        env = self.inputs(profile, "push", head, ref)
        return {"repository": REPO.copy(), "ref": ref, "deleted": False,
                "before": before, "after": head}, env

    def test_push_cumulative_baseline_is_looked_up_once_per_run(self):
        profile = "fsem06"
        self.fixture_claim(profile)
        paths = list(HISTORICAL_06)
        first = self.changes(dict.fromkeys(paths[:2], "A"))
        second = self.changes(dict.fromkeys(paths[2:], "A"))
        self.select(self.root)
        baseline = self.changes({"only-main": "A"})
        self.select(self.root)
        moving = self.changes({"only-later-main": "A"})
        command("update-ref", "refs/remotes/origin/main", moving)
        calls = []

        def fake_transport(*args):
            if args[:3] == ("remote", "get-url", "origin"):
                return b"https://github.com/abiggerhammer/phil.git\n"
            if args[0] == "ls-remote":
                calls.append(args)
                selected = baseline if len(calls) == 1 else moving
                return f"{selected}\trefs/heads/main\n".encode()
            return actual_git(*args)

        actual_git = routing.git
        with patch.object(routing, "git", side_effect=fake_transport):
            for tip, previous, expected, selected in [(second, first, "APPLICABLE", baseline),
                                                       (first, self.root, "REFUSE", moving)]:
                self.select(tip)
                event, env = self.push(profile, tip, previous)
                env["GH_TOKEN"] = "fixture-token"
                proof = self.receipt(profile, event, env, expected)
                self.assertEqual(proof["base"], selected)
                self.assertEqual(proof["merge_base"], self.root)
        self.assertEqual(calls, [("ls-remote", "--exit-code", "--refs", "origin", "refs/heads/main")] * 2)
        self.assertEqual(len(self.requests), 3)
        self.assertEqual(len(command("diff", "--name-only", first, second).splitlines()), 3)

    def test_push_fetches_only_the_selected_missing_object(self):
        profile = "fsem06"
        head = self.changes(HISTORICAL_06)
        self.fixture_claim(profile)
        with tempfile.TemporaryDirectory() as remote:
            command("clone", "-q", "--bare", ".", remote)
            command("-C", remote, "update-ref", "refs/heads/main", self.root)
            tree = command("-C", remote, "rev-parse", f"{self.root}^{{tree}}").decode().strip()
            base = command("-C", remote, "-c", "user.name=Fixture", "-c",
                           "user.email=fixture@example.test", "commit-tree", tree, "-p", self.root,
                           stdin=b"immutable main on remote only\n").decode().strip()
            command("-C", remote, "update-ref", "refs/heads/main", base)
            command("remote", "add", "origin", remote)
            with self.assertRaises(subprocess.CalledProcessError):
                command("cat-file", "-e", base)

            calls = []
            actual_git = routing.git

            def transport(*args):
                if args == ("remote", "get-url", "origin"):
                    return b"https://github.com/abiggerhammer/phil.git\n"
                if args[0] in {"ls-remote", "fetch"}:
                    calls.append(args)
                return actual_git(*args)

            event, env = self.push(profile, head, self.root)
            env["GH_TOKEN"] = "fixture-token"
            with patch.object(routing, "git", side_effect=transport):
                result = self.receipt(profile, event, env, "APPLICABLE")
            self.assertEqual(result["base"], base)
            self.assertEqual(calls, [
                ("ls-remote", "--exit-code", "--refs", "origin", "refs/heads/main"),
                ("fetch", "--no-tags", "origin", base),
            ])

    def test_command_line_entry_point_emits_receipt_and_exit_status(self):
        head = self.changes({})
        for profile in routing.PROFILES:
            event, env = self.pr(profile, head)
            self.event_path.write_text(json.dumps(event))
            for kind, route, code in [("pull_request", "N/A", 0), ("schedule", "REFUSE", 1)]:
                env["GITHUB_EVENT_NAME"] = kind
                result = subprocess.run([sys.executable, str(CHECKOUT / routing.HELPER), profile],
                                        env=os.environ | env, text=True, capture_output=True)
                self.assertEqual(result.returncode, code, result.stderr)
                self.assertEqual(json.loads(result.stdout)["route"], route)

    def test_push_rejects_bad_identity_before_reading_main(self):
        profile = "fsem06"
        head = self.changes(HISTORICAL_06)
        for field, value in [("deleted", True), ("deleted", 0), ("after", self.root),
                             ("ref", "refs/tags/historical"), ("ref", "refs/heads/unrelated")]:
            event, env = self.push(profile, head, self.root)
            event[field] = value
            if field == "ref":
                env["GITHUB_REF"] = value
            with patch.object(routing, "main_baseline", side_effect=AssertionError("unexpected lookup")):
                self.receipt(profile, event, env, "REFUSE")

    def test_trusted_immutable_controller_ignores_checkout_copy(self):
        self.fixture_claim("fsem05")
        head = self.changes(HISTORICAL_05)
        self.write("scripts/fsem_claim.py", "raise RuntimeError('candidate-only controller')")
        synthetic_tree = self.snapshot("synthetic-only controller")
        subject = self.merge_subject(self.root, head, synthetic_tree)
        event, env = self.historical("fsem05", head, subject=subject)
        env["GH_TOKEN"] = "fixture-token"
        self.receipt("fsem05", event, env, "APPLICABLE")


if __name__ == "__main__":
    unittest.main(verbosity=2)
