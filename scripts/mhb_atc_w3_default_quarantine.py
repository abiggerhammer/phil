#!/usr/bin/env python3
"""Read-only semantic quarantine of CURRENT default-branch workflows for W3 DELETE.

The immutable W3 ref target tree is separate evidence. GitHub selects the
current DEFAULT branch when a branch is deleted. Never execute downloaded
workflows, source files, Git hooks, or candidate scripts.

Uses the already-reviewed strict G1 event parser and W3 push disjointness
predicates, not a second hand-rolled interpretation of Actions YAML.
"""
from __future__ import annotations

from pathlib import Path
import os
import re
import subprocess

from test_mhb_atc_staged_push_ci import (
    parse_workflow_events, excludes_staged_push, excludes_w3_disposable_push,
)

SHA = re.compile(r"[0-9a-f]{40}\Z")
MAX_WORKFLOWS = 2000
MAX_PER_WORKFLOW = 1024 * 1024
MAX_INVENTORY_BYTES = 32 * 1024 * 1024
MIN_WORKFLOWS = 500
READONLY_REMOTE = "https://github.com/abiggerhammer/phil.git"


class DefaultQuarantineError(ValueError):
    """Source-defined error only: never render Git or YAML exception text."""


def insist(value, message):
    if not value:
        raise DefaultQuarantineError(message)


class DefaultWorkflowQuarantine:
    def __init__(self, repo_path: Path):
        self.repo_path = Path(repo_path)
        self.cache = {}

    def _git(self, *args, timeout=30):
        result = subprocess.run(
            ["git", *args], cwd=self.repo_path,
            capture_output=True, timeout=timeout, check=False,
            env={**os.environ, "GIT_TERMINAL_PROMPT": "0"},
        )
        insist(result.returncode == 0, "trusted default Git object read failed")
        return result.stdout

    def _ensure_commit(self, commit_sha):
        if subprocess.run(
                ["git", "cat-file", "-e", commit_sha + "^{commit}"],
                cwd=self.repo_path, capture_output=True, timeout=15,
                check=False).returncode == 0:
            return
        # Recovery can start on a trusted source SHA older than today's main.
        # Fetch only public Git object data, without checkout, credentials,
        # scripts, submodules or repository-configured remotes.
        fetch = subprocess.run([
            "git", "-c", "credential.helper=", "-c", "core.askPass=",
            "fetch", "--no-tags", "--depth=1", READONLY_REMOTE, "refs/heads/main",
        ], cwd=self.repo_path, capture_output=True, timeout=90,
           check=False, env={
               **os.environ, "GIT_TERMINAL_PROMPT": "0",
               "GIT_CONFIG_NOSYSTEM": "1",
           })
        insist(fetch.returncode == 0, "unable to fetch current default Git object")
        fetched = self._git("rev-parse", "--verify", "FETCH_HEAD").decode(
            "ascii", "strict").strip()
        insist(fetched == commit_sha,
               "default main advanced while fetching workflow objects")

    def validate(self, default_sha: str) -> str:
        """Validate EXACT default commit tree; never inspect mutable worktree."""
        insist(isinstance(default_sha, str) and SHA.fullmatch(default_sha),
               "invalid authenticated default SHA")
        if default_sha in self.cache:
            return self.cache[default_sha]

        self._ensure_commit(default_sha)
        tree_sha = self._git("rev-parse", "--verify",
                             default_sha + ":.github/workflows").decode(
            "ascii", "strict").strip()
        insist(SHA.fullmatch(tree_sha) is not None,
               "current default workflow tree missing")
        listing = self._git("ls-tree", "-rz", "--full-tree", default_sha,
                            ".github/workflows", timeout=60)
        items = listing.split(b"\x00")
        insist(items[-1] == b"" and len(items) > MIN_WORKFLOWS,
               "incomplete current default workflow inventory")
        entries = items[:-1]
        insist(MIN_WORKFLOWS <= len(entries) <= MAX_WORKFLOWS,
               "current default workflow inventory out of bounds")
        total = 0
        for entry in entries:
            try:
                header, path = entry.split(b"\t", 1)
                mode, kind, blob_sha = header.decode("ascii").split(" ")
                name = path.decode("utf-8")
            except (ValueError, UnicodeError):
                raise DefaultQuarantineError(
                    "malformed default workflow Git inventory") from None
            insist(mode == "100644" and kind == "blob" and
                   SHA.fullmatch(blob_sha) is not None and
                   name.startswith(".github/workflows/") and
                   name.count("/") == 2 and
                   name.endswith((".yml", ".yaml")),
                   "unreviewed default workflow inventory entry")
            raw = self._git("cat-file", "blob", blob_sha, timeout=30)
            total += len(raw)
            insist(len(raw) <= MAX_PER_WORKFLOW and
                   total <= MAX_INVENTORY_BYTES,
                   "default workflow inventory too large")
            try:
                source = raw.decode("utf-8")
                events = parse_workflow_events(source)
                # A default-branch 'delete' event cannot be restricted by
                # branch selectors. Reject it even if the shared G1 parser
                # eventually admits 'delete' as a recognized event kind.
                safe = ("delete" not in events and
                        excludes_staged_push(source) and
                        excludes_w3_disposable_push(source))
            except (UnicodeError, ValueError):
                safe = False
            # The shared strict G1 parser rejects unsupported events,
            # including 'delete', which cannot be branch-filtered.
            insist(safe, "current default workflow quarantine rejected")
        self.cache[default_sha] = tree_sha
        return tree_sha
