#!/usr/bin/env python3
"""Produce Rocq evidence for bounded source-run simulation from real FSEM01 v1 wire.

This is a *test harness*, not a proof of the Haskell producer's semantics.
It independently checks the source bytes, UTF-8 hex, canonical binder names,
and expected run outcome before constructing SourceRun evidence. The compiled
Rocq witness discharges the exact decoder and source-binding premises for
these four specimens, while the theorem remains explicitly conditional for
all other Haskell executions.
"""
from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import sys

from fsem01_observation_wire import (
    SPECIMENS,
    ROCq_ASCII,
    read_frames,
    validate_artifact,
)


def literal(value: str) -> str:
    if not ROCq_ASCII.fullmatch(value):
        raise ValueError("refusing to embed noncanonical or unsafe ASCII as Rocq code")
    return '"' + value + '"'


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifact-dir", required=True, type=Path)
    parser.add_argument(
        "--fixtures", default=Path("test/fixtures/fsem01-observation-v1"),
        type=Path,
    )
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()

    rows = []
    for filename, source_file, root, escapes in SPECIMENS:
        source_path = args.fixtures / source_file
        wire_path = args.artifact_dir / filename
        actual_wire = validate_artifact(wire_path, source_path, root, escapes)
        actual = read_frames(actual_wire)

        digest = hashlib.sha256(source_path.read_bytes()).hexdigest()
        root_hex = root.encode("utf-8").hex()
        owner_ordinal, view_ordinal = actual[4], actual[5]
        owner = f"$phil.local:{len(root)}:{root}:{owner_ordinal}".encode("utf-8").hex()
        view = f"$phil.local:{len(root)}:{root}:{view_ordinal}".encode("utf-8").hex()
        trace = "B10,S11,E11,X11" if escapes else "B10,S11,N11,C10,R00"
        outcome = (
            "ERR:BorrowEscape:shared view escapes its lexical scope"
            if escapes else "OK:Bytes8"
        )
        expected = [
            digest, root_hex, owner, view, owner_ordinal, view_ordinal,
            trace, outcome,
        ]
        if expected != actual:
            raise ValueError(f"{filename}: independent source-run fields disagree")
        rows.append((filename, actual_wire, expected, root_hex, escapes))

    distinct_roots = sorted({r[3] for r in rows})
    # Stable normalized IDs are ONLY within this exact two-root catalog.
    if len(distinct_roots) != 2:
        raise ValueError("this bounded proof requires exactly two unique roots")
    catalog_tokens = "; ".join(map(literal, distinct_roots))
    outputs = [
        "From Stdlib Require Import Strings.String Lists.List.",
        "From Phil.Surface Require Import SurfaceObservationWire",
        "  SurfaceBoundedSourceSimulation SurfaceBorrowStepErrorBridge.",
        "Import ListNotations.",
        "Open Scope string_scope.",
        "",
        "Definition sourceRootCatalog : list string :=",
        f"  [{catalog_tokens}].",
        "",
        "Lemma sourceRootCatalog_nodup : NoDup sourceRootCatalog.",
        "Proof.",
        "  unfold sourceRootCatalog.",
        "  constructor.",
        "  - simpl. intros [H | []]; discriminate.",
        "  - constructor.",
        "    + simpl. intros [].",
        "    + constructor.",
        "Qed.",
        "",
    ]

    for filename, raw, fields, root_hex, escapes in rows:
        stem = filename.removesuffix(".obs").replace("-", "_")
        run_var = f"run_{stem}"
        artifact_var = f"artifact_{stem}"
        wire_var = f"wire_{stem}"
        lemma = f"{stem}_bound_source_run"
        catalog_id = distinct_roots.index(root_hex)
        ordinal = int(fields[4])
        outcome_constructor = (
            "SourceRejectedBorrowEscape" if escapes else "SourceReturnedBytes8"
        )
        serial_fields = " ".join(literal(x) for x in fields)
        run_fields = " ".join(literal(x) for x in fields[:7])
        # We check the real source fingerprint, not a freely chosen model token.
        outputs.extend([
            f"Definition {wire_var} : string := {literal(raw)}.",
            f"Definition {artifact_var} : SurfaceObservationWire.Artifact :=",
            f"  SurfaceObservationWire.mkArtifact {serial_fields}.",
            f"Definition {run_var} : SourceRun :=",
            f"  mkSourceRun {run_fields} {outcome_constructor}.",
            "",
            f"Lemma {lemma} :",
            f"  SurfaceObservationWire.decodeArtifact {wire_var} =",
            f"    Some {artifact_var} /\\",
            f"  SourceBindsArtifact {run_var} {artifact_var} /\\",
            f"  SourceOwnerCatalog sourceRootCatalog",
            f"    ({catalog_id}, {ordinal}) {run_var}.",
            "Proof.",
            "  split.",
            "  - vm_compute. reflexivity.",
            "  - split.",
            "    + vm_compute. repeat split; reflexivity.",
            "    + unfold SourceOwnerCatalog.",
            "      split; [apply sourceRootCatalog_nodup |].",
            "      split; vm_compute; reflexivity.",
            "Qed.",
            "",
            f"Example {stem}_simulates :",
            f"  BoundedSourceSimulation {run_var} ({catalog_id}, {ordinal}).",
            "Proof.",
            f"  destruct {lemma} as [Hdecode [Hbinding Hcatalog]].",
            "  exact (proj1 (decoded_catalog_bound_source_simulates",
            f"    {wire_var} {artifact_var} {run_var}",
            f"    sourceRootCatalog ({catalog_id}, {ordinal})",
            "    Hdecode Hbinding Hcatalog)).",
            "Qed.",
            "",
        ])
        if escapes:
            outputs.extend([
                f"Example {stem}_has_no_continuation :",
                "  forall event suffix,",
                "    SurfaceBorrowStepErrorBridge.replay",
                f"      (modeledFinal ({catalog_id}, {ordinal})",
                f"        (runTerminal {run_var}))",
                "      (event :: suffix) = None.",
                "Proof.",
                "  intros event suffix.",
                f"  destruct {lemma} as [Hdecode [Hbinding _]].",
                "  eapply decoded_source_run_has_no_post_error_continuation.",
                "  - exact Hdecode.",
                "  - exact Hbinding.",
                "  - reflexivity.",
                "Qed.",
                "",
            ])

    outputs.extend([
        "(* An altered source digest is NOT evidence for the same artifact. *)",
        "Theorem forged_source_digest_cannot_bind :",
        "  forall run artifact,",
        "    runSourceDigest run <> SurfaceObservationWire.sourceHash artifact ->",
        "    ~ SourceBindsArtifact run artifact.",
        "Proof.",
        "  intros run artifact Hwrong [Hequal _].",
        "  exact (Hwrong Hequal).",
        "Qed.",
        "",
    ])
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("\n".join(outputs), encoding="ascii")
    print(f"PASS: generated {len(rows)} exact-byte, catalog-bound Rocq source-run witnesses")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        raise SystemExit(1)
