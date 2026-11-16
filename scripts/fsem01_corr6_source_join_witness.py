#!/usr/bin/env python3
"""CORR-6 independent bounded actual-source affine join wire validator.

The Haskell producer checks the real Grammar-v1 source and its exact Core
before/raw/pruned/join cuts, then emits framed ASCII. This validator checks
the actual source files/roots/binder roles, wire bytes and adversarial cases.
The generated Rocq module replays the SAME source-emitted raw strings.
This does not prove Haskell/compiler SHA or type equality correctness.
"""
from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import re

HEADER = "PHIL-FSEM01-CORR6-V1|"
ROOT = "decl.fsem01.join.choose"
ASCII = re.compile(r"[A-Za-z0-9:|._-]+")
HEXDIGITS = re.compile(r"(?:[0-9a-f]{2})+")
SHA = re.compile(r"[0-9a-f]{64}")
PROFILES = (
    ("accepted-asymmetric", "U1A0L1N0", "U1A1L1N0", "JOIN_EMPTY"),
    ("retained-affine", "U1A1L1N0", "U1A1L1N0", "JOIN_PERMIT"),
    ("both-local-affine", "U1A0L1N0", "U1A0L1N0", "JOIN_EMPTY"),
    ("unrestricted-local", "U1A1L1N0", "U1A1L1N0", "JOIN_PERMIT"),
    ("unreleased-linear-local", "UNREACHED", "UNREACHED", "PREJOIN_LINEAR"),
    ("stale-after-join", "U1A0L1N0", "U1A1L1N0", "POSTJOIN_STALE"),
)


def fail(s: str) -> None:
    raise ValueError(s)


def encode(fields: list[str]) -> str:
    return HEADER + "".join(f"{len(value)}:{value}" for value in fields)


def parse(wire: str) -> list[str]:
    if not wire.startswith(HEADER):
        fail("unknown/missing CORR-6 wire version")
    suffix = wire[len(HEADER):]
    fields: list[str] = []
    for index in range(8):
        digits, colon, data = suffix.partition(":")
        if not colon or not re.fullmatch(r"0|[1-9][0-9]*", digits):
            fail(f"noncanonical decimal length in frame {index}")
        count = int(digits)
        if count > len(data):
            fail(f"length exceeds remaining bytes in frame {index}")
        fields.append(data[:count])
        suffix = data[count:]
    if suffix or wire != encode(fields):
        fail("trailing bytes, fields or noncanonical encoding")
    return fields


def binder(core_hex: str, expected_index: int, label: str) -> None:
    if HEXDIGITS.fullmatch(core_hex) is None:
        fail(f"{label}: malformed lower-case hexadecimal identity")
    try:
        text = bytes.fromhex(core_hex).decode("utf-8", errors="strict")
    except UnicodeError as err:
        fail(f"{label}: invalid UTF-8: {err}")
    required = f"$phil.local:{len(ROOT)}:{ROOT}:{expected_index}"
    if text != required:
        fail(f"{label}: exact persisted-root and binder ordinal mismatch")


def check_source_fields(
    wire: str, source_bytes: bytes, expected: tuple[str, str, str]
) -> list[str]:
    if ASCII.fullmatch(wire) is None:
        fail("noncanonical ASCII or code-injection characters")
    fields = parse(wire)
    digest, root, flag, permit, payload, left, right, disposition = fields
    if SHA.fullmatch(digest) is None or digest != hashlib.sha256(source_bytes).hexdigest():
        fail("wrong source SHA256 or malformed source fingerprint")
    if HEXDIGITS.fullmatch(root) is None or root != ROOT.encode("utf-8").hex():
        fail("wrong exact function declaration root")
    for identity, ordinal, label in (
        (flag, 0, "flag Bool"),
        (permit, 1, "nominal Affine Permit"),
        (payload, 2, "Linear Bytes[8]"),
    ):
        binder(identity, ordinal, label)
    if len({flag,permit,payload}) != 3:
        fail("source binder identity alias")
    if (left,right,disposition) != expected:
        fail("left/right real source cut or observed disposition changed")
    source = source_bytes.decode("utf-8", errors="strict")
    if "data Permit mode affine" not in source or (
        "fn choose(flag : Bool, permit : Permit, payload : Bytes[8])"
        not in source.replace("\n", " ")
        and "fn choose(flag : Bool, permit : Permit, payload : Bytes[8])"
        not in " ".join(source.split())
    ):
        fail("unexpected source data/parameter type profile")
    return fields


def reject(label: str, callback) -> None:
    try:
        callback()
    except ValueError:
        return
    fail(f"mutated source transcript accepted: {label}")


def write_rocq(rows: list[tuple[str,str]], target: Path) -> None:
    statements = [
        "From Stdlib Require Import Strings.String.",
        "From Phil.Core Require Import Syntax.",
        "From Phil.Surface Require Import SurfaceSourceMixedJoinWireCorr6.",
        "Open Scope string_scope.",
        "",
    ]
    for name, raw in rows:
        stem = name.replace("-", "_")
        if ASCII.fullmatch(raw) is None:
            fail("unsafe source wire offered to Rocq code generator")
        statements += [
            f'Definition observed_{stem} : string := "{raw}".',
            f"Example actual_{stem}_replays :",
            "  forall bt pt lt : Syntax.Ty,",
            f"    checkWire bt pt lt observed_{stem} = true.",
            "Proof. intros. vm_compute. reflexivity. Qed.",
            "",
        ]
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text("\n".join(statements), encoding="ascii")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifact-dir", required=True, type=Path)
    parser.add_argument(
        "--fixture-dir",
        type=Path,
        default=Path("test/fixtures/fsem01-affine-join-scope-v1"),
    )
    parser.add_argument("--rocq-witness", required=True, type=Path)
    args = parser.parse_args()
    observed: list[tuple[str,str]] = []
    for name, left, right, outcome in PROFILES:
        source = (args.fixture_dir / (name + ".phil")).read_bytes()
        artifact = args.artifact_dir / (name + ".mix")
        raw = artifact.read_bytes()
        if any(b > 127 for b in raw):
            fail(f"{name}: source wire not ASCII")
        wire = raw.decode("ascii")
        fields = check_source_fields(wire, source, (left,right,outcome))
        observed.append((name,wire))
        reject("wrong version", lambda: parse(wire.replace(HEADER, HEADER+"X", 1)))
        reject("trailing characters", lambda: parse(wire + "extra"))
        reject("noncanonical frame", lambda: parse(wire.replace(
            f"{len(fields[0])}:{fields[0]}",
            f"0{len(fields[0])}:{fields[0]}",1
        )))
        reject("source SHA", lambda: check_source_fields(
            encode(["0"*64,*fields[1:]]),source,(left,right,outcome)
        ))
        reject("swapped source binding roles",lambda: check_source_fields(
            encode([fields[0],fields[1],fields[3],fields[2],*fields[4:]]),
            source,(left,right,outcome)
        ))
        reject("reversed predecessor cut",lambda: check_source_fields(
            encode([*fields[:5],right,left,outcome]),source,(left,right,outcome)
        ) if left != right else check_source_fields(
            encode([*fields[:5],"UNREACHED",right,outcome]),
            source,(left,right,outcome)
        ))
        reject("fabricated result",lambda: check_source_fields(
            encode([*fields[:7],"JOIN_PERMIT" if outcome!="JOIN_PERMIT"
                    else "JOIN_EMPTY"]),source,(left,right,outcome)
        ))
    present = set(args.artifact_dir.glob("*.mix"))
    expected = {args.artifact_dir/(name+".mix") for name,*_ in PROFILES}
    if present != expected:
        fail("missing or unexpected source join artifact files")
    write_rocq(observed,args.rocq_witness)
    print(f"PASS CORR-6: {len(observed)} original source/ABI-independent "
          "canonical mixed-join transcript files, exact binder identity "
          "and adversarial refusal, literal Rocq witness emitted")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
