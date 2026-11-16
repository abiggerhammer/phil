#!/usr/bin/env python3
"""CORR-8 independent exact-source pre-join failure transcript validator.

Reads original fixture bytes and untrusted Haskell-emitted records. Checks
canonical framing, declaration-rooted owner names, observed phase prefixes,
failure position, exact source error class and no invented successor. Emits a
literal Rocq replay witness. Finite conformance, not general refinement.
"""
from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import re

HEADER = "PHIL-FSEM01-CORR8-V1|"
ROOT = "decl.fsem01.scoped-loan-join.choose"
SHA = re.compile(r"[0-9a-f]{64}")
HEX = re.compile(r"(?:[0-9a-f]{2})+")
ASCII = re.compile(r"[A-Za-z0-9:|._-]+")
PROFILES = (
    ("accepted-left", "BSVC", "-", "1", "1", "JOIN_OK"),
    ("accepted-both", "BSVC", "BSVC", "1", "1", "JOIN_OK"),
    ("escape-left", "BSEX", "-", "0", "0", "SOURCE_BORROW"),
    ("escape-right", "-", "BSEX", "1", "0", "SOURCE_BORROW"),
    ("escape-alias", "BSEX", "-", "0", "0", "SOURCE_BORROW"),
    ("move-while-loaned", "BS", "-", "0", "0", "SOURCE_STRUCTURAL"),
    ("return-inside-borrow", "BS", "-", "0", "0", "SOURCE_LINEAR"),
    ("borrow-unrestricted", "B", "-", "0", "0", "SOURCE_BORROW"),
)


def fail(message: str) -> None:
    raise ValueError(message)


def encode(fields: list[str]) -> str:
    return HEADER + "".join(f"{len(field)}:{field}" for field in fields)


def decode(wire: str) -> list[str]:
    if not wire.startswith(HEADER):
        fail("unknown CORR-8 version")
    rest = wire[len(HEADER):]
    fields: list[str] = []
    for index in range(10):
        count, sep, value = rest.partition(":")
        if not sep or re.fullmatch(r"0|[1-9][0-9]*", count) is None:
            fail(f"noncanonical length prefix {index}")
        length = int(count)
        if length > len(value):
            fail(f"truncated frame {index}")
        fields.append(value[:length])
        rest = value[length:]
    if rest or encode(fields) != wire:
        fail("trailing bytes or noncanonical framing")
    return fields


def checked_binder(identity: str, ordinal: int) -> None:
    if HEX.fullmatch(identity) is None:
        fail("noncanonical source-owner name")
    try:
        actual = bytes.fromhex(identity).decode("utf-8", errors="strict")
    except UnicodeError:
        fail("invalid source owner UTF-8")
    expected = f"$phil.local:{len(ROOT)}:{ROOT}:{ordinal}"
    if actual != expected:
        fail("source owner root/ordinal mismatch")


def check(wire: str, source: bytes, expected: tuple[str, ...]) -> list[str]:
    if ASCII.fullmatch(wire) is None:
        fail("unsafe or non-ASCII CORR-8 witness")
    fields = decode(wire)
    digest, root, flag, owner, profile, left, right, lhs, rhs, result = fields
    if SHA.fullmatch(digest) is None or digest != hashlib.sha256(source).hexdigest():
        fail("original source SHA-256 mismatch")
    if root != ROOT.encode("utf-8").hex():
        fail("wrong source declaration root")
    checked_binder(flag, 0)
    checked_binder(owner, 1)
    if flag == owner:
        fail("flag and owner identities conflated")
    if (profile, left, right, lhs, rhs, result) != expected:
        fail("forged source checkpoint, branch order or outcome class")
    source_text = " ".join(source.decode("utf-8", errors="strict").split())
    if "fn choose(flag : Bool, payload : Bytes[8])" not in source_text:
        fail("original source parameter types changed")
    if result == "JOIN_OK":
        if (lhs, rhs) != ("1", "1") or "C" not in left:
            fail("accepted source did not close loan or produce both states")
    else:
        if rhs != "0" or "C" in left + right:
            fail("failed source produced joined successor or closed loan")
        if result == "SOURCE_BORROW" and profile.startswith("escape-") and "X" not in left + right:
            fail("BorrowEscape missing exact escape refusal checkpoint")
    return fields


def reject(label: str, action) -> None:
    try:
        action()
    except ValueError:
        return
    fail(f"hostile CORR-8 witness accepted: {label}")


def write_rocq(rows: list[tuple[str, str]], path: Path) -> None:
    source = [
        "From Stdlib Require Import Strings.String.",
        "From Phil.Surface Require Import SurfaceSourceFailureWireCorr8.",
        "Open Scope string_scope.",
        "",
    ]
    for name, wire in rows:
        stem = name.replace("-", "_")
        if ASCII.fullmatch(wire) is None:
            fail("unsafe wire rendered as Rocq source")
        source.extend([
            f'Definition observed_{stem} : string := "{wire}".',
            f"Example corr8_exact_source_{stem} :",
            f"  SurfaceSourceFailureWireCorr8.checkWire observed_{stem} = true.",
            "Proof. vm_compute. reflexivity. Qed.",
            "",
        ])
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(source), encoding="ascii")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifact-dir", type=Path, required=True)
    parser.add_argument("--fixture-dir", type=Path,
        default=Path("test/fixtures/fsem01-scoped-borrow-join-v1"))
    parser.add_argument("--rocq-witness", type=Path, required=True)
    args = parser.parse_args()
    rows: list[tuple[str, str]] = []
    for expected in PROFILES:
        name = expected[0]
        original = (args.fixture_dir / (name + ".phil")).read_bytes()
        wire = (args.artifact_dir / (name + ".fail")).read_bytes().decode("ascii")
        fields = check(wire, original, expected)
        rows.append((name, wire))
        reject("unknown version", lambda: decode(wire.replace(HEADER, HEADER+"X", 1)))
        reject("trailing data", lambda: decode(wire+"garbage"))
        reject("noncanonical length", lambda: decode(
            wire.replace(f"{len(fields[0])}:{fields[0]}",
                         f"0{len(fields[0])}:{fields[0]}", 1)))
        reject("source digest", lambda: check(
            encode(["0"*64,*fields[1:]]), original, expected))
        reject("owner swap", lambda: check(
            encode([fields[0],fields[1],fields[3],fields[2],*fields[4:]]),
            original, expected))
        reject("wrong root", lambda: check(
            encode([fields[0],"00",*fields[2:]]), original, expected))
        reject("phase forgery", lambda: check(
            encode([*fields[:5],"BSVC" if fields[5] != "BSVC" else "BSEX",
                    *fields[6:]]), original, expected))
        reject("branch forgery", lambda: check(
            encode([*fields[:6],"BSVC" if fields[6] == "-" else "-",
                    *fields[7:]]), original, expected))
        # Mutations must change the actual source record, including the
        # escape-right case whose left count is already one and right is zero.
        # Exercise each predecessor independently: a former no-op 0 -> 0
        # would falsely report that the validator admitted a forged state.
        reject("forged left predecessor count", lambda: check(
            encode([*fields[:7],
                    "2" if fields[7] == "1" else "1",
                    *fields[8:]]), original, expected))
        reject("forged right predecessor count", lambda: check(
            encode([*fields[:8],
                    "2" if fields[8] == "1" else "1",
                    fields[9]]), original, expected))
        reject("forged result", lambda: check(
            encode([*fields[:9],"JOIN_OK" if fields[9] != "JOIN_OK"
                    else "SOURCE_BORROW"]), original, expected))
    found = set(args.artifact_dir.glob("*.fail"))
    wanted = {args.artifact_dir / (row[0]+".fail") for row in PROFILES}
    if found != wanted:
        fail("missing or unexpected CORR-8 source artifacts")
    accepted = (args.fixture_dir / "accepted-left.phil").read_text()
    escaped = (args.fixture_dir / "escape-left.phil").read_text()
    if accepted.replace("view; unit;", "view;") != escaped:
        fail("escape-left no longer a minimal source-body mutation")
    write_rocq(rows, args.rocq_witness)
    print("PASS CORR-8: eight independent original-source hashes/owner identities, "
          "strict error prefixes, hostile mutations and generated Rocq replay")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
