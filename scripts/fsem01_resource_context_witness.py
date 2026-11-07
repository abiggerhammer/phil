#!/usr/bin/env python3
"""Independently check exact source-derived FSEM-01 CONTEXT-V1 bytes.

The wire encodes all four Core.ResourceContext collections for the admitted
one-linear-owner Bytes[8] fragment. It is *not* general Haskell-to-Rocq
refinement. CI also replays real Haskell Core.Context operations separately.
"""
import argparse
from pathlib import Path
import re


CONTEXT_HEADER = b"PHIL-FSEM01-CONTEXT-V1|"
OBS_HEADER = b"PHIL-FSEM01-OBS-V1|"
POSITIVE = "OK:Bytes8"
ESCAPE = "ERR:BorrowEscape:shared view escapes its lexical scope"


def frames(payload: bytes, count: int) -> list[str]:
    result = []
    for _ in range(count):
        colon = payload.find(b":")
        if colon < 1:
            raise ValueError("missing canonical frame length")
        digits = payload[:colon]
        if not re.fullmatch(rb"(0|[1-9][0-9]*)", digits):
            raise ValueError("noncanonical frame length")
        length = int(digits)
        payload = payload[colon + 1:]
        if len(payload) < length:
            raise ValueError("truncated frame")
        field, payload = payload[:length], payload[length:]
        try:
            result.append(field.decode("ascii"))
        except UnicodeDecodeError as exc:
            raise ValueError("state evidence is not ASCII") from exc
    if payload:
        raise ValueError("unexpected trailing bytes")
    return result


def parse(raw: bytes, header: bytes, count: int) -> list[str]:
    if not raw.startswith(header):
        raise ValueError("unknown wire version")
    return frames(raw[len(header):], count)


def state_word(phase: str, owner: str, view: str,
               view_live: bool, present: bool, loaned: bool) -> str:
    return "/".join([
        phase, view + "=SharedBytes" if view_live else "-", "-",
        owner + "=Bytes8" if present else "-", owner if loaned else "-"])


def expected_states(owner: str, view: str, outcome: str) -> str:
    if outcome == POSITIVE:
        states = [("B", False, True, False), ("S", False, True, True),
                  ("N", True, True, True), ("C", False, True, False),
                  ("R", False, False, False)]
    elif outcome == ESCAPE:
        states = [("B", False, True, False), ("S", False, True, True),
                  ("E", True, True, True), ("X", True, True, True)]
    else:
        raise ValueError("unknown terminal outcome")
    return ",".join(state_word(phase, owner, view, view_live, present, loaned)
                    for phase, view_live, present, loaned in states)


def check_pair(ctx: list[str], obs: list[str]) -> None:
    if len(ctx) != 6 or len(obs) != 8:
        raise ValueError("incorrect field count")
    digest, root, owner, view, states, outcome = ctx
    if [digest, root, owner, view] != obs[:4] or outcome != obs[7]:
        raise ValueError("CONTEXT-V1 metadata/outcome not bound to OBS-V1")
    if not re.fullmatch(r"[0-9a-f]{64}", digest):
        raise ValueError("invalid source digest")
    if any(len(s) % 2 != 0 or re.fullmatch("[0-9a-f]*", s) is None
           for s in (root, owner, view)):
        raise ValueError("noncanonical hex identity")
    if states != expected_states(owner, view, outcome):
        raise ValueError("unexpected resource maps, loans, phases or sequence")
    if obs[6] != ("B10,S11,N11,C10,R00" if outcome == POSITIVE
                  else "B10,S11,E11,X11"):
        raise ValueError("CONTEXT-V1 disagrees with observed membership bits")


def rocq(s: str) -> str:
    if not s.isascii() or '"' in s or "\\" in s:
        raise ValueError("unrepresentable Rocq ASCII literal")
    return '"' + s + '"'


def witness_example(index: int, raw: bytes, ctx: list[str],
                    obs: list[str]) -> str:
    context_literal = rocq(raw.decode("ascii"))
    ctx_record = ("SurfaceResourceContextWire.mkStateArtifact\n"
                  "    " + "\n    ".join(rocq(s) for s in ctx))
    obs_record = ("SurfaceObservationWire.mkArtifact\n"
                  "    " + "\n    ".join(rocq(s) for s in obs))
    return f"""
Example exact_context_state_{index} :
  SurfaceResourceContextWire.decodeState {context_literal} =
    Some ({ctx_record}).
Proof. vm_compute. reflexivity. Qed.

Example context_state_binds_observation_{index} :
  SurfaceResourceContextWire.bindsObservation
    ({ctx_record})
    ({obs_record}) = true.
Proof. vm_compute. reflexivity. Qed.
"""


def main() -> None:
    cli = argparse.ArgumentParser()
    cli.add_argument("--artifact-dir", required=True, type=Path)
    cli.add_argument("--observation-dir", required=True, type=Path)
    cli.add_argument("--output", required=True, type=Path)
    args = cli.parse_args()

    contexts = sorted(args.artifact_dir.glob("*.ctx"))
    if len(contexts) != 4:
        raise ValueError("expected four exactly source-derived context artifacts")
    names = {p.name for p in contexts}
    expected = {"positive-ascii.ctx", "escape-ascii.ctx",
                "positive-unicode.ctx", "escape-unicode.ctx"}
    if names != expected:
        raise ValueError("wrong source specimen set")

    examples = []
    for index, path in enumerate(contexts):
        raw = path.read_bytes()
        ctx = parse(raw, CONTEXT_HEADER, 6)
        obs_path = args.observation_dir / (path.stem + ".obs")
        obs = parse(obs_path.read_bytes(), OBS_HEADER, 8)
        check_pair(ctx, obs)
        examples.append(witness_example(index, raw, ctx, obs))

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        "From Stdlib Require Import Strings.String.\n"
        "From Phil.Surface Require Import "
        "SurfaceResourceContextWire SurfaceObservationWire.\n"
        "Open Scope string_scope.\n"
        + "\n".join(examples), encoding="ascii")
    print("PASS: four independently decoded full-state context witnesses")


if __name__ == "__main__":
    main()
