#!/usr/bin/env python3
"""Independent bounded CORR-5 source/trace-byte validator and Rocq witness emitter.

This checks Haskell-generated transcript bytes against the exact source
fixtures, declaration-root/binder encodings and expected observed category.
It is an independent finite conformance control, not a compiler proof or
authenticated provenance mechanism.
"""
from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import re

HEADER = "PHIL-FSEM01-CORR5-V1|"
ROOT = "decl.fsem01.l2.cycle"
HEX = re.compile(r"(?:[0-9a-f]{2})+")
DIGEST = re.compile(r"[0-9a-f]{64}")
LITERAL_SAFE = re.compile(r"[A-Za-z0-9:|.-]+")
EXPECTED = (
    ("accepted-owner", "linear-loop-transfer-v1/accepted-owner.phil", "OK", "DONE", False),
    ("accepted-same-width-spectator", "linear-loop-transfer-v1/accepted-same-width-spectator.phil", "OK", "DONE", True),
    ("stale-original-owner", "linear-loop-transfer-v1/stale-original-owner.phil", "ST", "MISSING", False),
    ("duplicate-live-header-owner", "linear-loop-transfer-v1/duplicate-live-header-owner.phil", "DU", "DUPLICATE", True),
    ("unproved-invariant", "linear-loop-transfer-v1/unproved-invariant.phil", "GA", "GATED", False),
    ("accepted-closed", "scoped-linear-loop-loan-v1/accepted-closed.phil", "OK", "DONE", False),
    ("live-loan-refusal", "scoped-linear-loop-loan-v1/accepted-closed.phil", "LO", "LOAN", False),
)


def fail(message: str) -> None:
    raise ValueError(message)


def encode(fields: list[str]) -> str:
    return HEADER + "".join(f"{len(v)}:{v}" for v in fields)


def parse(text: str) -> list[str]:
    if not text.startswith(HEADER):
        fail("missing versioned CORR-5 header")
    tail = text[len(HEADER):]
    fields: list[str] = []
    for i in range(8):
        size, colon, rest = tail.partition(":")
        if not colon or not re.fullmatch(r"0|[1-9][0-9]*", size):
            fail(f"noncanonical frame {i}")
        count = int(size)
        if count > len(rest):
            fail(f"truncated frame {i}")
        fields.append(rest[:count])
        tail = rest[count:]
    if tail or encode(fields) != text:
        fail("trailing or noncanonical source trace")
    return fields


def normalize_name(token: str, label: str) -> str:
    if HEX.fullmatch(token) is None:
        fail(f"{label}: invalid canonical lower-case hex")
    try:
        text = bytes.fromhex(token).decode("utf-8", errors="strict")
    except UnicodeError as exc:
        fail(f"{label}: invalid UTF-8: {exc}")
    match = re.fullmatch(r"\$phil\.local:([0-9]+):(.+):([0-9]+)", text)
    if match is None:
        fail(f"{label}: not a declaration-rooted Core.Name")
    size, root, ordinal = match.groups()
    if size != str(len(root)) or root != ROOT or not ordinal.isdecimal():
        fail(f"{label}: source binder identity/ordinal mismatch")
    if str(int(ordinal)) != ordinal:
        fail(f"{label}: noncanonical binder ordinal")
    return text


def check_trace(
    wire: str, source_bytes: bytes, kind: str, expected: str, has_alt: bool
) -> list[str]:
    if LITERAL_SAFE.fullmatch(wire) is None:
        fail("non-ASCII or unsafe literal character in generated wire")
    fields = parse(wire)
    digest, root, flag, old, slot, alt, actual_kind, actual_expected = fields
    if DIGEST.fullmatch(digest) is None or digest != hashlib.sha256(source_bytes).hexdigest():
        fail("source SHA256 differs from actual fixture bytes")
    if HEX.fullmatch(root) is None or bytes.fromhex(root).decode("utf-8") != ROOT:
        fail("wrong source declaration root")
    names = [
        normalize_name(flag, "flag"),
        normalize_name(old, "source Linear owner"),
        normalize_name(slot, "loop header"),
    ]
    if has_alt:
        names.append(normalize_name(alt, "source alternative owner"))
    elif alt != "-":
        fail("invented alternative source owner")
    if len(set(names)) != len(names):
        fail("source owner/header identity aliased")
    # This bounded corpus has source parameters allocated at ordinals 0/1,
    # an optional third source parameter at 2, and one loop header at 2/3.
    # Check these independently of the emitted Haskell field order.
    ordinals = [int(name.rsplit(":", 1)[1]) for name in names]
    expected_ordinals = [0, 1, 3, 2] if has_alt else [0, 1, 2]
    if ordinals != expected_ordinals:
        fail("source binder roles/ordinals swapped or forged")
    if actual_kind != kind or actual_expected != expected:
        fail("source kind, predecessor or outcome was replaced")
    source_text = source_bytes.decode("utf-8", errors="strict")
    if "fn cycle(flag : Bool, payload : Bytes[8]" not in source_text or (
        ("alternate : Bytes[8]" in source_text) != has_alt
    ):
        fail("unrecognized source parameter telescope")
    if (kind == "ST" and "continue(payload)" not in source_text) or (
        kind == "DU" and "continue(alternate)" not in source_text
    ) or (kind == "GA" and "invariant false" not in source_text) or (
        kind == "LO" and "borrow owner as" not in source_text
    ):
        fail("source transition shape does not match declared kind")
    return fields


def reject_mutation(label: str, thunk) -> None:
    try:
        thunk()
    except ValueError:
        return
    fail(f"mutated source transcript accepted: {label}")


def rocq_literal(raw: str) -> str:
    if LITERAL_SAFE.fullmatch(raw) is None:
        fail("attempted nonliteral-safe code generation")
    return '"' + raw + '"'


def write_rocq_witness(rows: list[tuple[str, str]], output: Path) -> None:
    lines = [
        "From Stdlib Require Import Strings.String.",
        "From Phil.Core Require Import Syntax.",
        "From Phil.Surface Require Import SurfaceSourceLinearTraceWireCorr5.",
        "Open Scope string_scope.",
        "",
    ]
    for name, wire in rows:
        stem = name.replace("-", "_")
        lines += [
            f"Definition observed_{stem} : string := {rocq_literal(wire)}.",
            f"Example actual_{stem}_replays :",
            "  forall (boolType bytesType : Syntax.Ty),",
            f"    checkWire boolType bytesType observed_{stem} = true.",
            "Proof. intros boolType bytesType. vm_compute. reflexivity. Qed.",
            "",
        ]
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("\n".join(lines), encoding="ascii")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifact-dir", required=True, type=Path)
    parser.add_argument(
        "--fixtures",
        default=Path("test/fixtures/fsem01-"),
        type=Path,
        help="Prefix preceding linear-loop-transfer-v1 and scoped-linear-loop-loan-v1",
    )
    parser.add_argument("--rocq-witness", type=Path, required=True)
    args = parser.parse_args()
    rows: list[tuple[str, str]] = []
    for name, path, kind, outcome, has_alt in EXPECTED:
        artifact = args.artifact_dir / (name + ".trace")
        source = Path(str(args.fixtures) + path)
        raw = artifact.read_bytes()
        if any(byte > 127 for byte in raw):
            fail(f"{name}: non-ASCII transcript")
        wire = raw.decode("ascii")
        fields = check_trace(wire, source.read_bytes(), kind, outcome, has_alt)
        rows.append((name, wire))
        reject_mutation("wrong version", lambda: parse(wire.replace(HEADER, HEADER + "X", 1)))
        reject_mutation("trailing payload", lambda: parse(wire + "EXTRA"))
        reject_mutation("broken field length", lambda: parse(wire.replace(
            f"{len(fields[0])}:{fields[0]}", f"0{len(fields[0])}:{fields[0]}", 1
        )))
        reject_mutation("swapped source owner and header", lambda: check_trace(
            encode([fields[0], fields[1], fields[2], fields[4], fields[3], *fields[5:]]),
            source.read_bytes(), kind, outcome, has_alt
        ))
        reject_mutation("spoofed source hash", lambda: check_trace(
            encode(["0" * 64, *fields[1:]]),
            source.read_bytes(), kind, outcome, has_alt
        ))
        reject_mutation("wrong failure classification", lambda: check_trace(
            encode([*fields[:7], "DONE" if outcome != "DONE" else "MISSING"]),
            source.read_bytes(), kind, outcome, has_alt
        ))
        reject_mutation("aliased source owner", lambda: check_trace(
            encode([*fields[:4], fields[3], *fields[5:]]),
            source.read_bytes(), kind, outcome, has_alt
        ))
    if set(args.artifact_dir.glob("*.trace")) != {
        args.artifact_dir / (name + ".trace") for name, *_ in EXPECTED
    }:
        fail("missing/extra source trace artifacts")
    write_rocq_witness(rows, args.rocq_witness)
    print(f"PASS CORR-5: independently source-checked {len(rows)} exact transcript bytes, "
          "canonical framing/UTF-8 identity, mutation controls and Rocq witnesses")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
