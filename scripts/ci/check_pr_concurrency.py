#!/usr/bin/env python3
"""Check PR-only supersession in the audited CI workflow inventory.

Scope is intentional: global admission/claim and release workflows need
separate review, and cannot be rewritten as ordinary per-PR CI jobs.
Uses only Python standard library; no fragile YAML 1.1 "on" coercion.
"""
from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
MANIFEST = ROOT / "scripts/ci/pr-concurrency-covered.txt"
GROUP = "  group: ${{ github.workflow_ref }}-${{ github.event.pull_request.number || github.run_id }}"
CANCEL = "  cancel-in-progress: ${{ github.event_name == 'pull_request' }}"
EXCLUDED = {
    "fsem-claim-guard.yml",
    "fsem-claim-release.yml",
    "mhb-atc-reconcile.yml",
    "mhb-atc-admit.yml",
    "mhb-atc-stage.yml",
    "mhb-atc-radar.yml",
}


def root_block(text: str, key: str) -> list[str]:
    lines = text.splitlines()
    starts = [i for i, line in enumerate(lines) if line == key + ":"]
    if len(starts) != 1:
        raise ValueError(f"expected exactly one top-level {key}: block")
    end = starts[0] + 1
    while end < len(lines):
        line = lines[end]
        if line and not line[0].isspace() and not line.startswith("#"):
            break
        end += 1
    return lines[starts[0]:end]


def validate_workflow(content: str) -> list[str]:
    errors = []
    try:
        events = root_block(content, "on")
        if not any(re.match(r"^  pull_request:\s*(?:#.*)?$", line)
                   for line in events):
            errors.append("missing pull_request trigger")
    except ValueError as exc:
        errors.append(str(exc))
    try:
        concurrency = root_block(content, "concurrency")
        active = [line.rstrip() for line in concurrency
                  if re.match(r"^  (group|queue|cancel-in-progress):", line)]
        if sorted(active) != sorted([GROUP, CANCEL]):
            errors.append("PR-only workflow_ref/PR-or-run-id group required")
        if concurrency.count(GROUP) != 1 or concurrency.count(CANCEL) != 1:
            errors.append("incorrect or duplicated supersession expression")
    except ValueError as exc:
        errors.append(str(exc))
    return errors


def check_inventory(root: Path = ROOT, manifest: Path = MANIFEST) -> list[str]:
    errors = []
    entries = [line.strip() for line in manifest.read_text().splitlines()
               if line.strip() and not line.startswith("#")]
    if not entries or len(set(entries)) != len(entries):
        errors.append("inventory empty or contains duplicates")
    for entry in entries:
        if entry in EXCLUDED or not re.fullmatch(r"[a-z0-9._-]+\.ya?ml", entry):
            errors.append(f"invalid or excluded workflow inventory entry: {entry}")
            continue
        path = root / ".github/workflows" / entry
        if not path.is_file():
            errors.append(f"missing workflow: {entry}")
            continue
        for error in validate_workflow(path.read_text()):
            errors.append(f"{entry}: {error}")
    return errors


if __name__ == "__main__":
    errors = check_inventory()
    for error in errors:
        print("FAIL:", error, file=sys.stderr)
    if errors:
        raise SystemExit(1)
    print("PASS: covered PR workflows supersede only same-PR runs; "
          "non-PR runs use independent IDs")
