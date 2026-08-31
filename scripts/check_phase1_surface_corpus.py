#!/usr/bin/env python3
"""Validate and expose the declarative Phase 1 surface parser corpus."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CORPUS = ROOT / "test" / "fixtures" / "phase1-surface"
MANIFEST = CORPUS / "manifest.json"


def fail(message: str) -> None:
    raise SystemExit(message)


def validate_manifest() -> list[dict[str, object]]:
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
        if not isinstance(fixture, dict):
            fail("every fixture must be a JSON object")
        fixture_id = fixture.get("id")
        path_text = fixture.get("path")
        expectation = fixture.get("expect")
        covers = fixture.get("covers")

        if not isinstance(fixture_id, str) or not fixture_id:
            fail("every fixture must have a non-empty string id")
        if any(separator in fixture_id for separator in ("\t", "\n", "\r")):
            fail(f"{fixture_id!r}: fixture id must be one-line TSV-safe text")
        if fixture_id in seen_ids:
            fail(f"duplicate fixture id: {fixture_id}")
        seen_ids.add(fixture_id)

        if not isinstance(path_text, str) or not path_text.endswith(".phil"):
            fail(f"{fixture_id}: path must name a .phil file")
        if any(separator in path_text for separator in ("\t", "\n", "\r")):
            fail(f"{fixture_id}: path must be one-line TSV-safe text")
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

    return fixtures


def emit_parser_cases(fixtures: list[dict[str, object]]) -> None:
    for fixture in fixtures:
        print(f"{fixture['id']}\t{fixture['path']}\t{fixture['expect']}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--emit-parser-cases",
        action="store_true",
        help="emit validated fixture id/path/expectation rows as TSV for the Haskell parser harness",
    )
    args = parser.parse_args()

    fixtures = validate_manifest()
    if args.emit_parser_cases:
        emit_parser_cases(fixtures)
    else:
        print(f"Phase 1 surface corpus: {len(fixtures)} fixtures, manifest integral")


if __name__ == "__main__":
    main()
