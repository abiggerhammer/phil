#!/usr/bin/env python3
"""Build the complete Phase-1 INT-007 conformance freeze inventory."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
SURFACE_ROOT = ROOT / "test/fixtures/phase1-surface"
NEGATIVE_ROOT = ROOT / "test/fixtures/phase1-negative"

FORMAT = "PHIL-PHASE1-CONFORMANCE-FREEZE-V1"
HEADER = [
    "entry_id",
    "entry_kind",
    "repository_path",
    "sha256",
    "expectation",
    "competent_layer",
    "governing_authority",
]


def sha256(path: Path) -> str:
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def load_surface() -> tuple[list[dict[str, str]], set[str]]:
    manifest_path = SURFACE_ROOT / "manifest.json"
    data = json.loads(manifest_path.read_text(encoding="utf-8"))
    fixtures = data["fixtures"]
    rows: list[dict[str, str]] = []
    seen_ids: set[str] = set()
    seen_paths: set[str] = set()

    for fixture in fixtures:
        fixture_id = fixture["id"]
        path = fixture["path"]
        if fixture_id in seen_ids:
            raise ValueError(f"duplicate surface fixture id: {fixture_id}")
        if path in seen_paths:
            raise ValueError(f"duplicate surface fixture path: {path}")
        seen_ids.add(fixture_id)
        seen_paths.add(path)

        source = SURFACE_ROOT / path
        if not source.is_file():
            raise ValueError(f"surface fixture missing: {path}")

        expect = fixture["expect"]
        if expect == "parse":
            expectation = "accept"
            layer = "syntax"
            authority = "matrix:SURF-002"
        elif expect == "reject-syntax":
            expectation = "reject-syntax"
            layer = fixture.get("required_failure_layer", "")
            if layer != "syntax":
                raise ValueError(
                    f"surface rejection {fixture_id} must name syntax as competent layer"
                )
            authority = "matrix:SURF-003"
        else:
            raise ValueError(f"unknown surface expectation for {fixture_id}: {expect}")

        rows.append(
            {
                "entry_id": fixture_id,
                "entry_kind": "surface-fixture",
                "repository_path": rel(source),
                "sha256": sha256(source),
                "expectation": expectation,
                "competent_layer": layer,
                "governing_authority": authority,
            }
        )

    actual = {
        p.relative_to(SURFACE_ROOT).as_posix()
        for p in SURFACE_ROOT.rglob("*.phil")
        if p.is_file()
    }
    if actual != seen_paths:
        missing = sorted(actual - seen_paths)
        extra = sorted(seen_paths - actual)
        raise ValueError(
            f"surface manifest/file bijection mismatch: unlisted={missing}, missing={extra}"
        )

    return rows, seen_ids


def load_negative() -> tuple[list[dict[str, str]], set[str]]:
    manifest_path = NEGATIVE_ROOT / "manifest.tsv"
    rows: list[dict[str, str]] = []
    seen_ids: set[str] = set()
    seen_paths: set[str] = set()

    with manifest_path.open(encoding="utf-8", newline="") as fh:
        reader = csv.DictReader(fh, delimiter="\t")
        expected = [
            "fixture_id",
            "path",
            "expect",
            "competent_layer",
            "environment_profile",
            "governing_authority",
        ]
        if reader.fieldnames != expected:
            raise ValueError(f"unexpected negative manifest columns: {reader.fieldnames}")
        for fixture in reader:
            fixture_id = fixture["fixture_id"]
            path = fixture["path"]
            if fixture_id in seen_ids:
                raise ValueError(f"duplicate negative fixture id: {fixture_id}")
            if path in seen_paths:
                raise ValueError(f"duplicate negative fixture path: {path}")
            seen_ids.add(fixture_id)
            seen_paths.add(path)

            source = NEGATIVE_ROOT / path
            if not source.is_file():
                raise ValueError(f"negative fixture missing: {path}")

            layer = fixture["competent_layer"]
            authority = fixture["governing_authority"]
            if not layer:
                raise ValueError(f"negative fixture lacks competent layer: {fixture_id}")
            refs = authority.split(";")
            if not refs or any(not ref for ref in refs):
                raise ValueError(f"negative fixture lacks governing authority: {fixture_id}")
            if len(refs) != len(set(refs)):
                raise ValueError(f"negative fixture repeats governing authority: {fixture_id}")
            for ref in refs:
                if not (ref.startswith("matrix:") or ref.startswith("certified:")):
                    raise ValueError(
                        f"negative fixture has untyped governing authority: {fixture_id}: {ref}"
                    )
                if ref == "matrix:INT-004":
                    raise ValueError(
                        f"negative fixture uses meta-level INT-004 as semantic authority: {fixture_id}"
                    )

            rows.append(
                {
                    "entry_id": fixture_id,
                    "entry_kind": "semantic-negative-fixture",
                    "repository_path": rel(source),
                    "sha256": sha256(source),
                    "expectation": "reject:" + fixture["expect"],
                    "competent_layer": layer,
                    "governing_authority": authority,
                }
            )

    actual = {
        p.relative_to(NEGATIVE_ROOT).as_posix()
        for p in NEGATIVE_ROOT.rglob("*.phil")
        if p.is_file()
    }
    if actual != seen_paths:
        missing = sorted(actual - seen_paths)
        extra = sorted(seen_paths - actual)
        raise ValueError(
            f"negative manifest/file bijection mismatch: unlisted={missing}, missing={extra}"
        )

    return rows, seen_ids


def support_rows() -> list[dict[str, str]]:
    rows = [
        {
            "entry_id": "support.surface.manifest",
            "entry_kind": "support",
            "repository_path": rel(SURFACE_ROOT / "manifest.json"),
            "sha256": sha256(SURFACE_ROOT / "manifest.json"),
            "expectation": "metadata",
            "competent_layer": "syntax",
            "governing_authority": "matrix:SURF-002;matrix:SURF-003",
        }
    ]

    for path in sorted(NEGATIVE_ROOT.rglob("*.tsv")):
        suffix = path.relative_to(NEGATIVE_ROOT).as_posix()
        stable = suffix.removesuffix(".tsv").replace("/", ".").replace("_", "-")
        rows.append(
            {
                "entry_id": "support.negative." + stable,
                "entry_kind": "support",
                "repository_path": rel(path),
                "sha256": sha256(path),
                "expectation": "metadata",
                "competent_layer": "conformance-harness",
                "governing_authority": "certified:PHIL-P1-CONFORMANCE-001",
            }
        )
    return rows


def build_rows() -> list[dict[str, str]]:
    surface_rows, surface_ids = load_surface()
    negative_rows, negative_ids = load_negative()
    overlap = surface_ids & negative_ids
    if overlap:
        raise ValueError(f"cross-corpus fixture id collision: {sorted(overlap)}")

    rows = surface_rows + negative_rows + support_rows()
    ids = [row["entry_id"] for row in rows]
    paths = [row["repository_path"] for row in rows]
    if len(ids) != len(set(ids)):
        raise ValueError("duplicate conformance-freeze entry id")
    if len(paths) != len(set(paths)):
        raise ValueError("duplicate conformance-freeze repository path")
    return sorted(rows, key=lambda row: row["entry_id"])


def render(rows: list[dict[str, str]]) -> str:
    out = [FORMAT, "\t".join(HEADER)]
    for row in rows:
        out.append("\t".join(row[column] for column in HEADER))
    return "\n".join(out) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument(
        "--path",
        default="handoff/phase1/conformance-freeze-v1.tsv",
        help="checked-in freeze manifest path, relative to repository root",
    )
    parser.add_argument("--output")
    args = parser.parse_args()

    rendered = render(build_rows())

    if args.output:
        output = ROOT / args.output
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(rendered, encoding="utf-8")

    if args.check:
        checked = ROOT / args.path
        if not checked.is_file():
            print(f"missing checked-in conformance freeze: {checked}", file=sys.stderr)
            return 1
        actual = checked.read_text(encoding="utf-8")
        if actual != rendered:
            print("INT-007 conformance freeze drift", file=sys.stderr)
            return 1

    if not args.output and not args.check:
        sys.stdout.write(rendered)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
