#!/usr/bin/env python3
"""CORR-7 independent original-source predecessor transcript validator.

Haskell produces the exact verified source-control checkpoints; this
separately checks their real file bytes, source identities, canonical framing,
profile/outcome/refusal mutations and emits literal Rocq replay obligations.
Bounded Grammar-v1 witness evidence, NOT universal Source->Core refinement.
"""
from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import re

HEADER = "PHIL-FSEM01-CORR7-V1|"
ROOT = "decl.fsem01.j1j2.choose"
SHA = re.compile(r"[0-9a-f]{64}")
LOWER_HEX = re.compile(r"(?:[0-9a-f]{2})+")
ASCII = re.compile(r"[A-Za-z0-9:|._-]+")
PROFILES = (
    ("accepted", "CONT", "CONT", "JOIN_OK"),
    ("linear-mismatch", "CONT", "CONT", "JOIN_LINEAR"),
    ("two-local-owners", "CONT", "CONT", "JOIN_LINEAR"),
    ("terminal-excluded", "TERM", "CONT", "JOIN_ONE"),
    ("terminal-stale", "TERM", "CONT", "POST_STALE"),
    ("terminal-both", "TERM", "TERM", "NO_CONT"),
)


def fail(message: str) -> None:
    raise ValueError(message)


def encode(fields: list[str]) -> str:
    return HEADER + "".join(f"{len(field)}:{field}" for field in fields)


def decode(wire: str) -> list[str]:
    if not wire.startswith(HEADER):
        fail("unknown predecessor-wire version")
    rest = wire[len(HEADER):]
    fields: list[str] = []
    for frame in range(8):
        count, separator, payload = rest.partition(":")
        if not separator or re.fullmatch(r"0|[1-9][0-9]*", count) is None:
            fail(f"noncanonical field length: {frame}")
        length = int(count)
        if length > len(payload):
            fail(f"truncated field: {frame}")
        fields.append(payload[:length])
        rest = payload[length:]
    if rest or wire != encode(fields):
        fail("trailing bytes or noncanonical framing")
    return fields


def binder(hex_identity: str, ordinal: int) -> None:
    if LOWER_HEX.fullmatch(hex_identity) is None:
        fail("noncanonical UTF-8 source binder identity")
    try:
        name = bytes.fromhex(hex_identity).decode("utf-8", errors="strict")
    except UnicodeError:
        fail("invalid UTF-8 binder identity")
    if name != f"$phil.local:{len(ROOT)}:{ROOT}:{ordinal}":
        fail("source root/binder ordinal mismatch")


def check(
    wire: str, source_bytes: bytes, expected: tuple[str, str, str, str]
) -> list[str]:
    if ASCII.fullmatch(wire) is None:
        fail("noncanonical ASCII or unsafe source transcript")
    fields = decode(wire)
    digest, root_hex, flag_hex, payload_hex, profile, left, right, result = fields
    if SHA.fullmatch(digest) is None or digest != hashlib.sha256(source_bytes).hexdigest():
        fail("wrong real source SHA256")
    if root_hex != ROOT.encode().hex():
        fail("wrong exact source declaration root")
    binder(flag_hex, 0)
    binder(payload_hex, 1)
    if flag_hex == payload_hex:
        fail("flag/payload source identities conflated")
    if (profile,left,right,result) != expected:
        fail("real source predecessor profile or disposition altered")
    source = source_bytes.decode("utf-8", errors="strict")
    if ("fn choose(flag : Bool, payload : Bytes[8])" not in
            " ".join(source.split())):
        fail("wrong source parameter type profile")
    return fields


def reject(label: str, callback) -> None:
    try:
        callback()
    except ValueError:
        return
    fail(f"hostile predecessor mutation accepted: {label}")


def write_rocq(rows: list[tuple[str, str]], path: Path) -> None:
    statements = [
        "From Stdlib Require Import Strings.String.",
        "From Phil.Core Require Import Syntax.",
        "From Phil.Surface Require Import SurfaceSourcePredecessorWireCorr7.",
        "Open Scope string_scope.",
        "",
    ]
    for profile, wire in rows:
        stem = profile.replace("-", "_")
        if ASCII.fullmatch(wire) is None:
            fail("unsafe source wire offered to Rocq")
        statements.extend([
            f'Definition observed_{stem} : string := "{wire}".',
            f"Example corr7_source_{stem}_replays :",
            "  forall (ty : Syntax.Ty),",
            f"  SurfaceSourcePredecessorWireCorr7.checkWire ty observed_{stem} = true.",
            "Proof. intros ty. vm_compute. reflexivity. Qed.",
            "",
        ])
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(statements), encoding="ascii")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifact-dir", type=Path, required=True)
    parser.add_argument(
        "--fixture-dir", type=Path,
        default=Path("test/fixtures/fsem01-source-branch-join-v1")
    )
    parser.add_argument("--rocq-witness", type=Path, required=True)
    args = parser.parse_args()
    rows: list[tuple[str, str]] = []
    for expected in PROFILES:
        name = expected[0]
        source = (args.fixture_dir / (name + ".phil")).read_bytes()
        wire = (args.artifact_dir / (name + ".pred")).read_bytes().decode("ascii")
        fields = check(wire, source, expected)
        rows.append((name, wire))
        reject("version", lambda: decode(wire.replace(HEADER, HEADER + "X", 1)))
        reject("trailing", lambda: decode(wire + "extra"))
        reject("noncanonical frame", lambda: decode(
            wire.replace(f"{len(fields[0])}:{fields[0]}",
                         f"0{len(fields[0])}:{fields[0]}", 1)
        ))
        reject("source digest", lambda: check(
            encode(["0"*64, *fields[1:]]), source, expected
        ))
        reject("binder role swap", lambda: check(
            encode([fields[0], fields[1], fields[3], fields[2], *fields[4:]]),
            source, expected
        ))
        reject("forged predecessor", lambda: check(
            encode([*fields[:5], "TERM" if fields[5] == "CONT" else "CONT",
                    *fields[6:]]), source, expected
        ))
        reject("invented post-terminal success", lambda: check(
            encode([*fields[:7], "JOIN_OK" if fields[7] != "JOIN_OK"
                    else "NO_CONT"]), source, expected
        ))
        reject("reordered source status", lambda: check(
            encode([*fields[:4], "terminal-both" if name != "terminal-both"
                    else "accepted", *fields[5:]]), source, expected
        ))
    got = set(args.artifact_dir.glob("*.pred"))
    wanted = {args.artifact_dir / (p[0]+".pred") for p in PROFILES}
    if got != wanted:
        fail("missing or unexpected source predecessor transcripts")
    write_rocq(rows, args.rocq_witness)
    print("PASS CORR-7: six independent original-source hashes and scoped binders, "
          "eight canonical fields, source/terminal/rejection adversaries, "
          "and generated literal Rocq replay")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
