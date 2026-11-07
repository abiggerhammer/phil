#!/usr/bin/env python3
"""Validate FSEM-01 observation wire v1 against independent source bytes.

This Python validator is additional evidence, not the formally proved decoder.
The generated Rocq witness passes the exact ASCII bytes of real artifacts to
SurfaceObservationWire.decodeArtifact for executable proof-assistant checking.
"""
from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import re
import sys

HEADER = "PHIL-FSEM01-OBS-V1|"
FIELD_COUNT = 8
VALID_HEX = re.compile(r"(?:[0-9a-f]{2})*")
HASH_HEX = re.compile(r"[0-9a-f]{64}")
ROCq_ASCII = re.compile(r"[A-Za-z0-9:|,.\- ]+")

SPECIMENS = (
    ("positive-ascii.obs", "positive.phil", "decl.FSEM01ObservationV1", False),
    ("escape-ascii.obs", "escape.phil", "decl.FSEM01ObservationV1", True),
    ("positive-unicode.obs", "positive.phil", "decl.é:猫", False),
    ("escape-unicode.obs", "escape.phil", "decl.é:猫", True),
)


def fail(message: str) -> None:
    raise ValueError(message)


def read_frames(raw: str) -> list[str]:
    if not raw.startswith(HEADER):
        fail("missing/unsupported v1 header")
    rest = raw[len(HEADER):]
    fields = []
    for _ in range(FIELD_COUNT):
        number, sep, remaining = rest.partition(":")
        if not sep or not re.fullmatch(r"0|[1-9][0-9]*", number):
            fail("missing or noncanonical framed decimal length")
        length = int(number)
        if length > len(remaining):
            fail("declared field length exceeds remaining wire")
        fields.append(remaining[:length])
        rest = remaining[length:]
    if rest:
        fail("trailing fields or bytes")
    if encode_fields(fields) != raw:
        fail("noncanonical framing")
    return fields


def encode_fields(fields: list[str]) -> str:
    return HEADER + "".join(f"{len(field)}:{field}" for field in fields)


def validate_artifact(path: Path, source: Path, root: str, escapes: bool) -> str:
    original = path.read_bytes()
    if any(b > 127 for b in original):
        fail(f"{path}: wire must contain ASCII bytes only")
    wire = original.decode("ascii")
    if not ROCq_ASCII.fullmatch(wire):
        fail(f"{path}: unexpected quote, backslash, control or punctuation")
    digest, root_hex, owner_hex, view_hex, owner_ord, view_ord, trace, outcome = read_frames(wire)
    if not HASH_HEX.fullmatch(digest):
        fail(f"{path}: malformed source SHA-256")
    source_digest = hashlib.sha256(source.read_bytes()).hexdigest()
    if digest != source_digest:
        fail(f"{path}: artifact does not bind the exact fixture bytes")
    for label, value in (
        ("root", root_hex), ("owner", owner_hex), ("view", view_hex)
    ):
        if not VALID_HEX.fullmatch(value):
            fail(f"{path}: malformed lowercase UTF-8 hex for {label}")
        try:
            bytes.fromhex(value).decode("utf-8", errors="strict")
        except UnicodeError as error:
            fail(f"{path}: invalid UTF-8 in {label}: {error}")

    if bytes.fromhex(root_hex).decode("utf-8") != root:
        fail(f"{path}: wrong exact declaration root")
    if not re.fullmatch(r"0|[1-9][0-9]*", owner_ord) or \
       not re.fullmatch(r"0|[1-9][0-9]*", view_ord):
        fail(f"{path}: noncanonical owner/view ordinals")
    owner, view = int(owner_ord), int(view_ord)
    if not (0 <= owner < view):
        fail(f"{path}: owner/view ordering invalid")
    def core_name(index: int) -> str:
        return f"$phil.local:{len(root)}:{root}:{index}"
    if bytes.fromhex(owner_hex).decode("utf-8") != core_name(owner):
        fail(f"{path}: owner name does not match root/ordinal encoding")
    if bytes.fromhex(view_hex).decode("utf-8") != core_name(view):
        fail(f"{path}: view name does not match root/ordinal encoding")

    expected_trace = (
        "B10,S11,E11,X11" if escapes else "B10,S11,N11,C10,R00"
    )
    expected_outcome = (
        "ERR:BorrowEscape:shared view escapes its lexical scope"
        if escapes else "OK:Bytes8"
    )
    if trace != expected_trace or outcome != expected_outcome:
        fail(f"{path}: nonterminal trace, invented continuation, or wrong outcome")
    return wire


def write_rocq_witness(wire_by_name: dict[str, str], output: Path) -> None:
    # The only inserted text consists of independently checked ASCII wire
    # characters. There are no quotes, escapes or line breaks to inject Rocq.
    statements = [
        "From Stdlib Require Import Strings.String Bool.Bool.",
        "From Phil.Surface Require Import SurfaceObservationWire.",
        "Open Scope string_scope.",
        "",
    ]
    for filename, wire in wire_by_name.items():
        if not ROCq_ASCII.fullmatch(wire):
            fail("nonliteral-safe artifact refused")
        name = filename.replace(".obs", "").replace("-", "_")
        expected_trace = (
            "B10,S11,E11,X11" if name.startswith("escape")
            else "B10,S11,N11,C10,R00"
        )
        expected_outcome = (
            "ERR:BorrowEscape:shared view escapes its lexical scope"
            if name.startswith("escape") else "OK:Bytes8"
        )
        statements.extend([
            f"Example observed_{name}_decodes :",
            f'  (match decodeArtifact "{wire}" with',
            "   | None => false",
            "   | Some artifact =>",
            f'       String.eqb (traceCodes artifact) "{expected_trace}" &&',
            f'       String.eqb (terminalCode artifact) "{expected_outcome}"',
            "   end) = true.",
            "Proof. vm_compute. reflexivity. Qed.",
            "",
        ])
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("\n".join(statements), encoding="ascii")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifact-dir", required=True, type=Path)
    parser.add_argument(
        "--fixtures", default="test/fixtures/fsem01-observation-v1", type=Path
    )
    parser.add_argument("--rocq-witness", type=Path)
    args = parser.parse_args()
    try:
        observed = {}
        for filename, source_name, root, escapes in SPECIMENS:
            observed[filename] = validate_artifact(
                args.artifact_dir / filename,
                args.fixtures / source_name,
                root,
                escapes,
            )
        actual_files = {path.name for path in args.artifact_dir.iterdir()}
        if actual_files != set(observed):
            fail(f"unexpected/missing artifacts: {actual_files ^ set(observed)}")
        if args.rocq_witness:
            write_rocq_witness(observed, args.rocq_witness)
        print(f"PASS: {len(observed)} source-bound canonical v1 artifacts")
        return 0
    except (OSError, ValueError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
