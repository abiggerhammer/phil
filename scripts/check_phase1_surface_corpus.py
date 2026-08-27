#!/usr/bin/env python3
"""Validate the declarative Phase 1 surface parser production corpus."""

from __future__ import annotations

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CORPUS = ROOT / "test" / "fixtures" / "phase1-surface"
MANIFEST = CORPUS / "manifest.json"


def fail(message: str) -> None:
    raise SystemExit(message)


def main() -> None:
    data = json.loads(MANIFEST.read_text(encoding="utf-8"))
    if data.get("authority") != "grammar/phase1-surface.ebnf":
        fail("corpus authority must remain grammar/phase1-surface.ebnf")
    if data.get("entry_rule") != "source_file":
        fail("corpus entry rule must remain source_file")
    if data.get("semantic_acceptance_asserted") is not False:
        fail("surface corpus must not claim semantic acceptance")

    fixtures = data.get("fixtures")
    if not isinstance(fixtures, list) or not fixtures:
        fail("manifest fixtures must be a non-empty list")

    seen_ids: set[str] = set()
    seen_paths: set[str] = set()
    allowed_expectations = {"parse", "reject-syntax"}

    for fixture in fixtures:
        fixture_id = fixture.get("id")
        path_text = fixture.get("path")
        expectation = fixture.get("expect")
        covers = fixture.get("covers")

        if not isinstance(fixture_id, str) or not fixture_id:
            fail("every fixture must have a non-empty string id")
        if fixture_id in seen_ids:
            fail(f"duplicate fixture id: {fixture_id}")
        seen_ids.add(fixture_id)

        if not isinstance(path_text, str) or not path_text.endswith(".phil"):
            fail(f"{fixture_id}: path must name a .phil file")
        if path_text in seen_paths:
            fail(f"duplicate fixture path: {path_text}")
        seen_paths.add(path_text)

        path = CORPUS / path_text
        if not path.is_file():
            fail(f"{fixture_id}: missing fixture file {path_text}")
        if not path.read_text(encoding="utf-8").strip():
            fail(f"{fixture_id}: fixture file is empty")

        if expectation not in allowed_expectations:
            fail(f"{fixture_id}: invalid expectation {expectation!r}")
        if not isinstance(covers, list) or not covers or not all(isinstance(x, str) and x for x in covers):
            fail(f"{fixture_id}: covers must be a non-empty string list")

        if expectation == "parse":
            if fixture.get("semantic") != "deferred":
                fail(f"{fixture_id}: positive parser fixture must defer semantic acceptance")
            if not path_text.startswith("accepted/"):
                fail(f"{fixture_id}: parse fixture must live under accepted/")
        else:
            if fixture.get("required_failure_layer") != "syntax":
                fail(f"{fixture_id}: negative fixture must require syntax-layer failure")
            if not path_text.startswith("rejected/"):
                fail(f"{fixture_id}: syntax-negative fixture must live under rejected/")

    disk_paths = {
        str(path.relative_to(CORPUS))
        for directory in (CORPUS / "accepted", CORPUS / "rejected")
        for path in directory.glob("*.phil")
    }
    if disk_paths != seen_paths:
        missing = sorted(disk_paths - seen_paths)
        stale = sorted(seen_paths - disk_paths)
        fail(f"manifest/file mismatch: unlisted={missing}, missing={stale}")

    print(f"Phase 1 surface corpus: {len(fixtures)} fixtures, manifest integral")


if __name__ == "__main__":
    main()
