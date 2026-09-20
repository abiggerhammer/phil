#!/usr/bin/env python3
"""Build the complete top-level Phase-1 INT-007 handoff manifest."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "handoff/phase1/manifest-v1.tsv"

FORMAT = "PHIL-PHASE1-HANDOFF-MANIFEST-V1"
HEADER = "artifact_id\tartifact_kind\trepository_path\tsha256\tgoverning_authority"

ADDITIONS = [
    ("realization.upload.v1", "architecture-realization", "handoff/phase1/runtime/upload-realization-v1.tsv", "matrix:VER-010"),
    ("systems.upload.v1", "systems", "handoff/phase1/runtime/upload-systems-v1.tsv", "matrix:SYS-001"),
    ("stage-contract.upload.v1", "stage-contract", "handoff/phase1/runtime/upload-stage-contract-v1.tsv", "matrix:SYS-020"),
    ("lowering.upload.v1", "lowering", "handoff/phase1/runtime/upload-lowering-v1.tsv", "matrix:SYS-001"),
    ("cost.upload.v1", "cost", "handoff/phase1/runtime/upload-cost-v1.tsv", "matrix:SYS-018"),
    ("realization.steve.v1", "architecture-realization", "handoff/phase1/runtime/steve-realization-v1.tsv", "matrix:VER-010"),
    ("systems.steve.v1", "systems", "handoff/phase1/runtime/steve-systems-v1.tsv", "matrix:SYS-001"),
    ("stage-contract.steve.v1", "stage-contract", "handoff/phase1/runtime/steve-stage-contract-v1.tsv", "matrix:SYS-020"),
    ("lowering.steve.v1", "lowering", "handoff/phase1/runtime/steve-lowering-v1.tsv", "matrix:SYS-001"),
    ("cost.steve.v1", "cost", "handoff/phase1/runtime/steve-cost-v1.tsv", "matrix:SYS-018"),
    ("assurance.upload.manifest.v1", "assurance-manifest", "handoff/phase1/witnesses/upload-assurance-manifest-v1.tsv", "matrix:INT-002"),
    ("assurance.steve.manifest.v1", "assurance-manifest", "handoff/phase1/witnesses/steve-assurance-manifest-v1.tsv", "matrix:INT-002"),
    ("tcb.upload.residual.v1", "tcb", "handoff/phase1/witnesses/upload-residual-tcb-v1.tsv", "matrix:INT-005"),
    ("tcb.steve.residual.v1", "tcb", "handoff/phase1/witnesses/steve-residual-tcb-v1.tsv", "matrix:INT-005"),
    ("conformance.freeze.v1", "conformance-manifest", "handoff/phase1/conformance-freeze-v1.tsv", "certified:PHIL-P1-CONFORMANCE-001"),
]


def digest(path: Path) -> str:
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()


def parse_existing() -> list[list[str]]:
    lines = MANIFEST.read_text(encoding="utf-8").splitlines()
    if len(lines) < 2 or lines[0] != FORMAT or lines[1] != HEADER:
        raise ValueError("unexpected top-level handoff manifest header")
    rows = []
    for raw in lines[2:]:
        if not raw.strip() or raw.lstrip().startswith("#"):
            continue
        fields = raw.split("\t")
        if len(fields) != 5:
            raise ValueError(f"malformed top-level manifest row: {raw}")
        rows.append(fields)
    return rows


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--conformance-path",
        default="handoff/phase1/conformance-freeze-v1.tsv",
    )
    parser.add_argument("--output")
    args = parser.parse_args()

    conformance = ROOT / args.conformance_path
    if not conformance.is_file():
        raise ValueError(f"missing conformance freeze: {conformance}")

    rows = parse_existing()
    additions_by_id = {row[0]: row for row in ADDITIONS}
    additions_by_path = {row[2]: row for row in ADDITIONS}
    retained = [
        row for row in rows
        if row[0] not in additions_by_id and row[2] not in additions_by_path
    ]

    generated = []
    for artifact_id, kind, path_text, authority in ADDITIONS:
        source = conformance if artifact_id == "conformance.freeze.v1" else ROOT / path_text
        if not source.is_file():
            raise ValueError(f"missing frozen artifact: {path_text}")
        generated.append(
            [artifact_id, kind, path_text, digest(source), authority]
        )

    final_rows = retained + generated
    ids = [row[0] for row in final_rows]
    paths = [row[2] for row in final_rows]
    if len(ids) != len(set(ids)):
        raise ValueError("duplicate top-level handoff artifact id")
    if len(paths) != len(set(paths)):
        raise ValueError("duplicate top-level handoff repository path")

    rendered = "\n".join(
        [FORMAT, HEADER] + ["\t".join(row) for row in final_rows]
    ) + "\n"

    if args.output:
        output = ROOT / args.output
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(rendered, encoding="utf-8")
    else:
        print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
