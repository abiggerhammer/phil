#!/usr/bin/env python3
"""Derive the exact Rocq Phase 1 surface-overlap certificate from canonical EBNF.

The canonical authority remains grammar/phase1-surface.ebnf.  This generator
reuses the executable nullable/FIRST/FOLLOW audit to reflect the complete local
overlap inventory into a typed Rocq value.  The generated value is evidence for
later mechanized checking; it is not itself the universal determinacy proof.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

from check_phase1_surface_determinacy import EOF, EPSILON, findings
from derive_phase1_surface_grammar import load

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SOURCE = ROOT / "grammar" / "phase1-surface.ebnf"
DEFAULT_TARGET = ROOT / "proof" / "Phil" / "Surface" / "GrammarDeterminacyCertificate.v"

KIND_CONSTRUCTORS = {
    "alternative-first-overlap": "AlternativeFirstOverlap",
    "optional-follow-overlap": "OptionalFollowOverlap",
    "repeat-follow-overlap": "RepeatFollowOverlap",
    "nullable-repetition": "NullableRepetition",
}


def rocq_string(value: str) -> str:
    if '"' in value:
        raise ValueError(
            "generated Rocq certificate renderer does not support quote characters "
            "inside strings"
        )
    return f'"{value}"'


def render_token(token: str) -> str:
    if token == EOF:
        return "OverlapEof"
    if token == EPSILON:
        return "OverlapEpsilon"
    if token.startswith("literal:"):
        value = json.loads(token[len("literal:") :])
        if not isinstance(value, str):
            raise ValueError(f"invalid literal overlap token {token!r}")
        return f"OverlapLiteral {rocq_string(value)}"
    if token.startswith("class:<") and token.endswith(">"):
        return f"OverlapLexicalClass {rocq_string(token[len('class:<'):-1])}"
    raise ValueError(f"unsupported overlap token {token!r}")


def render_tokens(tokens: tuple[str, ...]) -> str:
    return "[" + "; ".join(render_token(token) for token in tokens) + "]"


def render_site(site: object) -> str:
    kind = KIND_CONSTRUCTORS.get(site.kind)
    if kind is None:
        raise ValueError(f"unsupported overlap kind {site.kind!r}")
    return "\n".join(
        [
            "  {| overlap_kind := " + kind + ";",
            "     overlap_rule := " + rocq_string(site.rule) + ";",
            "     overlap_path := " + rocq_string(site.path) + ";",
            "     overlap_tokens := " + render_tokens(site.tokens) + ";",
            "     overlap_detail := " + rocq_string(site.detail) + " |}",
        ]
    )


def render_rocq(source_text: str, rules: list[tuple[str, object]]) -> str:
    digest = hashlib.sha256(source_text.encode("utf-8")).hexdigest()
    actual = findings(rules)

    lines = [
        "From Stdlib Require Import Lists.List Strings.String.",
        "From Phil.Surface Require Import Grammar.",
        "",
        "Import ListNotations.",
        "Open Scope string_scope.",
        "",
        "(* GENERATED FILE. DO NOT EDIT.",
        "   Source: grammar/phase1-surface.ebnf",
        f"   Source SHA-256: {digest}",
        "   Generator: scripts/derive_phase1_surface_determinacy_certificate.py",
        "",
        "   This reflects the complete local-overlap inventory computed from the",
        "   canonical EBNF by the audited nullable/FIRST/FOLLOW analysis.  It is a",
        "   proof input, not a proof that the analysis itself is complete. *)",
        "",
        "Inductive OverlapKind : Type :=",
        "| AlternativeFirstOverlap : OverlapKind",
        "| OptionalFollowOverlap : OverlapKind",
        "| RepeatFollowOverlap : OverlapKind",
        "| NullableRepetition : OverlapKind.",
        "",
        "Inductive OverlapToken : Type :=",
        "| OverlapLiteral : string -> OverlapToken",
        "| OverlapLexicalClass : string -> OverlapToken",
        "| OverlapEof : OverlapToken",
        "| OverlapEpsilon : OverlapToken.",
        "",
        "Record OverlapSite : Type := {",
        "  overlap_kind : OverlapKind;",
        "  overlap_rule : string;",
        "  overlap_path : string;",
        "  overlap_tokens : list OverlapToken;",
        "  overlap_detail : string",
        "}.",
        "",
        "Definition phase1_surface_determinacy_certificate_source_sha256 : string :=",
        "  " + rocq_string(digest) + ".",
        "",
        "Definition phase1_surface_determinacy_certificate : list OverlapSite := [",
    ]
    for index, site in enumerate(actual):
        rendered = render_site(site)
        if index != len(actual) - 1:
            rendered += ";"
        lines.append(rendered)
    lines.extend(["].", ""])
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--write", action="store_true")
    group.add_argument("--check", action="store_true")
    parser.add_argument("--source", type=Path, default=DEFAULT_SOURCE)
    parser.add_argument("--target", type=Path, default=DEFAULT_TARGET)
    args = parser.parse_args()

    try:
        source_text, rules = load(args.source)
        rendered = render_rocq(source_text, rules)
    except (OSError, ValueError, json.JSONDecodeError) as error:
        print(f"phase1 determinacy certificate error: {error}", file=sys.stderr)
        return 2

    if args.write:
        args.target.parent.mkdir(parents=True, exist_ok=True)
        args.target.write_text(rendered, encoding="utf-8")
        print(
            f"wrote {args.target.relative_to(ROOT)} from "
            f"{args.source.relative_to(ROOT)}"
        )
        return 0

    try:
        existing = args.target.read_text(encoding="utf-8")
    except OSError as error:
        print(f"phase1 determinacy certificate check: {error}", file=sys.stderr)
        return 2
    if existing != rendered:
        print(
            "phase1 determinacy certificate drift: generated Rocq certificate does not "
            "match grammar/phase1-surface.ebnf",
            file=sys.stderr,
        )
        print(
            "run: python3 scripts/derive_phase1_surface_determinacy_certificate.py --write",
            file=sys.stderr,
        )
        return 1

    print("phase1 surface determinacy certificate: canonical EBNF and Rocq certificate agree")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
