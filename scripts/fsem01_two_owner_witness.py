#!/usr/bin/env python3
"""Independent exact-byte validator for bounded two-owner CONTEXT2-V1.

The two binder identities are linked to separate, source-derived OBS-V1
specimens (ASCII-root primary, Unicode-root spectator). The two-owner Core
context was assembled and tested by Haskell; this script does not prove the
two-owner source checker or the producer's general correctness.
"""
import argparse
from pathlib import Path
import re

VERSION = b"PHIL-FSEM01-CONTEXT2-V1|"
OBS = b"PHIL-FSEM01-OBS-V1|"
POSITIVE = "OK:Bytes8"
ESCAPE = "ERR:BorrowEscape:shared view escapes its lexical scope"
PAIRS = {
    "positive.ctx2": ("positive-ascii.obs", "positive-unicode.obs", POSITIVE),
    "escape.ctx2": ("escape-ascii.obs", "positive-unicode.obs", ESCAPE),
}


def parse_frames(raw: bytes, header: bytes, count: int) -> list[str]:
    if not raw.startswith(header):
        raise ValueError("unknown two-owner wire header/version")
    data = raw[len(header):]
    values = []
    for _ in range(count):
        offset = data.find(b":")
        if offset < 1 or not re.fullmatch(rb"(0|[1-9][0-9]*)", data[:offset]):
            raise ValueError("noncanonical field length")
        n = int(data[:offset])
        data = data[offset + 1:]
        if len(data) < n:
            raise ValueError("truncated framed field")
        field = data[:n]
        try:
            values.append(field.decode("ascii"))
        except UnicodeDecodeError as exc:
            raise ValueError("non-ASCII state wire") from exc
        data = data[n:]
    if data:
        raise ValueError("trailing wire bytes")
    return values


def render_fields(header: bytes, fields: list[str]) -> bytes:
    return header + b"".join(
        str(len(field)).encode("ascii") + b":" + field.encode("ascii")
        for field in fields)


def canonical_hex(value: str) -> bool:
    return bool(value) and len(value) % 2 == 0 and (
        re.fullmatch(r"[0-9a-f]+", value) is not None)


def word(phase: str, primary: str, spectator: str,
         owner_present: bool, loaned: bool) -> str:
    linear = (primary + "=Bytes8;" if owner_present else "") + spectator + "=Bytes8"
    return "/".join([phase, "-", "-", linear, primary if loaned else "-"])


def expected_trace(primary: str, spectator: str, outcome: str) -> str:
    if outcome == POSITIVE:
        steps = [("B", True, False), ("S", True, True),
                 ("N", True, True), ("C", True, False),
                 ("R", False, False)]
    elif outcome == ESCAPE:
        steps = [("B", True, False), ("S", True, True),
                 ("E", True, True), ("X", True, True)]
    else:
        raise ValueError("unadmitted source outcome")
    return ",".join(word(phase, primary, spectator, present, loan)
                    for phase, present, loan in steps)


def check_pair(ctx: list[str], primary_obs: list[str],
               spectator_obs: list[str], expected: str) -> None:
    if len(ctx) != 8 or len(primary_obs) != 8 or len(spectator_obs) != 8:
        raise ValueError("wrong field count")
    h1, h2, r1, r2, n1, n2, states, outcome = ctx
    if [h1, r1, n1] != [primary_obs[0], primary_obs[1], primary_obs[2]]:
        raise ValueError("primary source root/hash/binder is not OBS-V1-bound")
    if [h2, r2, n2] != [spectator_obs[0], spectator_obs[1], spectator_obs[2]]:
        raise ValueError("spectator source root/hash/binder is not OBS-V1-bound")
    if not all(re.fullmatch(r"[0-9a-f]{64}", h) for h in (h1, h2)):
        raise ValueError("source hash not lowercase sha256")
    if not all(canonical_hex(value) for value in (r1, r2, n1, n2)):
        raise ValueError("noncanonical name/root encoding")
    if n1 == n2 or r1 == r2:
        raise ValueError("two owners are not identity-distinct")
    if outcome != expected or primary_obs[7] != outcome:
        raise ValueError("primary terminal not source-derived")
    if spectator_obs[7] != POSITIVE:
        raise ValueError("spectator source fixture was not accepted")
    if primary_obs[6] != (
        "B10,S11,N11,C10,R00" if outcome == POSITIVE
        else "B10,S11,E11,X11"):
        raise ValueError("primary OBS-V1 trace mismatch")
    if spectator_obs[6] != "B10,S11,N11,C10,R00":
        raise ValueError("spectator OBS-V1 trace mismatch")
    if states != expected_trace(n1, n2, outcome):
        raise ValueError("full two-owner resource context is not canonical")


def rocq_literal(value: str) -> str:
    if (not value.isascii() or '"' in value or "\\" in value or
            any(ord(c) < 32 for c in value)):
        raise ValueError("unsafe Rocq ASCII literal")
    return '"' + value + '"'


def proof(index: int, wire: bytes, fields: list[str]) -> str:
    record = ("SurfaceTwoOwnerContext.mkTwoOwnerArtifact\n      " +
              "\n      ".join(map(rocq_literal, fields)))
    return f"""
Example decoded_two_owner_specimen_{index} :
  SurfaceTwoOwnerContext.decodeTwoOwner {rocq_literal(wire.decode("ascii"))} =
    Some ({record}).
Proof. vm_compute. reflexivity. Qed.
"""


def rejects_mutation(original: list[str], primary: list[str],
                     spectator: list[str], terminal: str,
                     offset: int, value: str) -> bool:
    mutated = original.copy()
    mutated[offset] = value
    try:
        check_pair(mutated, primary, spectator, terminal)
    except ValueError:
        return True
    return False


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--artifact-dir", type=Path, required=True)
    parser.add_argument("--observation-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    files = sorted(args.artifact_dir.glob("*.ctx2"))
    if {p.name for p in files} != set(PAIRS):
        raise ValueError("not exactly the two committed source-bounded specimens")

    examples = []
    for i, path in enumerate(files):
        primary_path, spectator_path, outcome = PAIRS[path.name]
        raw = path.read_bytes()
        fields = parse_frames(raw, VERSION, 8)
        pobs = parse_frames((args.observation_dir / primary_path).read_bytes(), OBS, 8)
        sobs = parse_frames((args.observation_dir / spectator_path).read_bytes(), OBS, 8)
        if raw != render_fields(VERSION, fields):
            raise ValueError("noncanonical two-owner framing")
        check_pair(fields, pobs, sobs, outcome)
        assert rejects_mutation(fields, pobs, sobs, outcome, 4, fields[5]), (
            "swapped owner name gained authority")
        assert rejects_mutation(fields, pobs, sobs, outcome, 5, fields[4]), (
            "swapped spectator name gained authority")
        assert rejects_mutation(fields, pobs, sobs, outcome, 2, fields[3]), (
            "wrong source root gained authority")
        assert rejects_mutation(fields, pobs, sobs, outcome, 6,
                                fields[6] + ";deadbeef=Bytes8"), (
            "foreign binding gained authority")
        assert rejects_mutation(fields, pobs, sobs, outcome, 7,
                                ESCAPE if outcome == POSITIVE else POSITIVE), (
            "forged terminal gained authority")
        for malformed in (raw[:-1], raw + b"x",
                          raw.replace(VERSION, b"PHIL-FSEM01-CONTEXT2-V2|", 1),
                          raw.replace(VERSION, VERSION + b"x", 1)):
            try:
                parse_frames(malformed, VERSION, 8)
            except ValueError:
                pass
            else:
                raise AssertionError("malformed two-owner bytes gained authority")
        examples.append(proof(i, raw, fields))

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        "From Stdlib Require Import Strings.String.\n"
        "From Phil.Surface Require Import SurfaceTwoOwnerContext.\n"
        "Open Scope string_scope.\n" +
        "\n".join(examples), encoding="ascii")
    print("PASS: two exact two-owner source-root/OBS-V1-bound Rocq witnesses")


if __name__ == "__main__":
    main()
