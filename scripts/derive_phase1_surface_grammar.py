#!/usr/bin/env python3
"""Derive the Rocq Phase 1 surface grammar from canonical EBNF.

The canonical authority is grammar/phase1-surface.ebnf. This script accepts a
small, documented EBNF dialect and emits a Rocq value representing that grammar
as a typed EBNF syntax tree. The checked-in Rocq file is generated output; edit
the EBNF, not the Rocq grammar.
"""

from __future__ import annotations

import argparse
import dataclasses
import hashlib
import re
import sys
from pathlib import Path
from typing import Iterable

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SOURCE = ROOT / "grammar" / "phase1-surface.ebnf"
DEFAULT_TARGET = ROOT / "proof" / "Phil" / "Surface" / "Grammar.v"

NAME_RE = re.compile(r"[a-z][a-z0-9_]*\Z")
KEYWORD_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*\Z")


@dataclasses.dataclass(frozen=True)
class Token:
    kind: str
    value: str
    offset: int


class Node:
    pass


@dataclasses.dataclass(frozen=True)
class Literal(Node):
    value: str


@dataclasses.dataclass(frozen=True)
class LexicalClass(Node):
    name: str


@dataclasses.dataclass(frozen=True)
class Reference(Node):
    name: str


@dataclasses.dataclass(frozen=True)
class Sequence(Node):
    items: tuple[Node, ...]


@dataclasses.dataclass(frozen=True)
class Alternative(Node):
    items: tuple[Node, ...]


@dataclasses.dataclass(frozen=True)
class OptionalNode(Node):
    item: Node


@dataclasses.dataclass(frozen=True)
class Repeat(Node):
    item: Node


def strip_comments(text: str) -> str:
    return "\n".join(
        "" if line.lstrip().startswith("#") else line
        for line in text.splitlines()
    )


def tokenize(text: str) -> list[Token]:
    text = strip_comments(text)
    tokens: list[Token] = []
    i = 0
    punctuation = set("=;|,()[]{}")
    while i < len(text):
        ch = text[i]
        if ch.isspace():
            i += 1
            continue
        if ch in punctuation:
            tokens.append(Token(ch, ch, i))
            i += 1
            continue
        if ch == '"':
            start = i
            i += 1
            out: list[str] = []
            while i < len(text):
                if text[i] == '"':
                    i += 1
                    tokens.append(Token("LITERAL", "".join(out), start))
                    break
                if text[i] == "\\":
                    i += 1
                    if i >= len(text):
                        raise ValueError(f"unterminated escape at offset {start}")
                    escaped = text[i]
                    escapes = {
                        '"': '"',
                        "\\": "\\",
                        "n": "\n",
                        "r": "\r",
                        "t": "\t",
                    }
                    if escaped not in escapes:
                        raise ValueError(
                            f"unsupported string escape \\{escaped} at offset {i - 1}"
                        )
                    out.append(escapes[escaped])
                    i += 1
                    continue
                out.append(text[i])
                i += 1
            else:
                raise ValueError(f"unterminated literal at offset {start}")
            continue
        if ch == "<":
            start = i
            end = text.find(">", i + 1)
            if end < 0:
                raise ValueError(f"unterminated lexical class at offset {start}")
            name = text[i + 1 : end]
            if not re.fullmatch(r"[A-Z][A-Z0-9_]*", name):
                raise ValueError(f"invalid lexical class <{name}> at offset {start}")
            tokens.append(Token("CLASS", name, start))
            i = end + 1
            continue
        if ch.isalpha() or ch == "_":
            start = i
            i += 1
            while i < len(text) and (text[i].isalnum() or text[i] == "_"):
                i += 1
            name = text[start:i]
            if not NAME_RE.fullmatch(name):
                raise ValueError(
                    f"nonterminal {name!r} must be lowercase snake_case at offset {start}"
                )
            tokens.append(Token("NAME", name, start))
            continue
        raise ValueError(f"unexpected character {ch!r} at offset {i}")
    tokens.append(Token("EOF", "", len(text)))
    return tokens


class Parser:
    def __init__(self, tokens: list[Token]) -> None:
        self.tokens = tokens
        self.index = 0

    @property
    def current(self) -> Token:
        return self.tokens[self.index]

    def accept(self, kind: str) -> Token | None:
        if self.current.kind == kind:
            token = self.current
            self.index += 1
            return token
        return None

    def expect(self, kind: str) -> Token:
        token = self.accept(kind)
        if token is None:
            cur = self.current
            raise ValueError(
                f"expected {kind}, found {cur.kind} {cur.value!r} at offset {cur.offset}"
            )
        return token

    def parse_grammar(self) -> list[tuple[str, Node]]:
        rules: list[tuple[str, Node]] = []
        seen: set[str] = set()
        while self.current.kind != "EOF":
            name = self.expect("NAME").value
            if name in seen:
                raise ValueError(f"duplicate grammar rule {name}")
            seen.add(name)
            self.expect("=")
            expression = self.parse_alternative(stop={";"})
            self.expect(";")
            rules.append((name, expression))
        return rules

    def parse_alternative(self, stop: set[str]) -> Node:
        items = [self.parse_sequence(stop | {"|"})]
        while self.accept("|") is not None:
            items.append(self.parse_sequence(stop | {"|"}))
        if len(items) == 1:
            return items[0]
        return Alternative(tuple(items))

    def parse_sequence(self, stop: set[str]) -> Node:
        items = [self.parse_atom()]
        while self.accept(",") is not None:
            items.append(self.parse_atom())
        if self.current.kind not in stop:
            cur = self.current
            raise ValueError(
                f"expected sequence separator or one of {sorted(stop)}, "
                f"found {cur.kind} {cur.value!r} at offset {cur.offset}"
            )
        if len(items) == 1:
            return items[0]
        return Sequence(tuple(items))

    def parse_atom(self) -> Node:
        token = self.current
        if self.accept("NAME") is not None:
            return Reference(token.value)
        if self.accept("LITERAL") is not None:
            return Literal(token.value)
        if self.accept("CLASS") is not None:
            return LexicalClass(token.value)
        if self.accept("(") is not None:
            item = self.parse_alternative(stop={")"})
            self.expect(")")
            return item
        if self.accept("[") is not None:
            item = self.parse_alternative(stop={"]"})
            self.expect("]")
            return OptionalNode(item)
        if self.accept("{") is not None:
            item = self.parse_alternative(stop={"}"})
            self.expect("}")
            return Repeat(item)
        raise ValueError(
            f"expected grammar atom, found {token.kind} {token.value!r} "
            f"at offset {token.offset}"
        )


def references(node: Node) -> Iterable[str]:
    if isinstance(node, Reference):
        yield node.name
    elif isinstance(node, (Sequence, Alternative)):
        for item in node.items:
            yield from references(item)
    elif isinstance(node, (OptionalNode, Repeat)):
        yield from references(node.item)


def literals(node: Node) -> Iterable[str]:
    if isinstance(node, Literal):
        yield node.value
    elif isinstance(node, (Sequence, Alternative)):
        for item in node.items:
            yield from literals(item)
    elif isinstance(node, (OptionalNode, Repeat)):
        yield from literals(node.item)


def validate(rules: list[tuple[str, Node]]) -> None:
    names = {name for name, _ in rules}
    if "source_file" not in names:
        raise ValueError("grammar must define source_file")
    unknown = sorted(
        {ref for _, node in rules for ref in references(node) if ref not in names}
    )
    if unknown:
        raise ValueError(f"undefined nonterminals: {', '.join(unknown)}")

    graph = {name: set(references(node)) for name, node in rules}
    reachable = {"source_file"}
    pending = ["source_file"]
    while pending:
        name = pending.pop()
        for target in graph[name]:
            if target not in reachable:
                reachable.add(target)
                pending.append(target)
    unreachable = sorted(names - reachable)
    if unreachable:
        raise ValueError(f"unreachable nonterminals: {', '.join(unreachable)}")


def coq_string(value: str) -> str:
    if '"' in value:
        raise ValueError(
            "generated Rocq renderer does not support literal quote characters; "
            "use a lexical token class for quoted strings"
        )
    return f'"{value}"'


def render_list(items: list[str]) -> str:
    return "[" + "; ".join(items) + "]"


def render_node(node: Node) -> str:
    if isinstance(node, Literal):
        return f"ELiteral {coq_string(node.value)}"
    if isinstance(node, LexicalClass):
        return f"ELexicalClass {coq_string(node.name)}"
    if isinstance(node, Reference):
        return f"ENonterminal {coq_string(node.name)}"
    if isinstance(node, Sequence):
        return "ESequence " + render_list([render_node(item) for item in node.items])
    if isinstance(node, Alternative):
        return "EAlternative " + render_list([render_node(item) for item in node.items])
    if isinstance(node, OptionalNode):
        return f"EOptional ({render_node(node.item)})"
    if isinstance(node, Repeat):
        return f"ERepetition ({render_node(node.item)})"
    raise TypeError(f"unsupported grammar node {node!r}")


def render_rocq(source_text: str, rules: list[tuple[str, Node]]) -> str:
    keywords = sorted(
        {
            literal
            for _, node in rules
            for literal in literals(node)
            if KEYWORD_RE.fullmatch(literal)
        }
    )
    digest = hashlib.sha256(source_text.encode("utf-8")).hexdigest()

    lines = [
        "From Stdlib Require Import Lists.List Strings.String.",
        "Import ListNotations.",
        "Open Scope string_scope.",
        "",
        "(* GENERATED FILE. DO NOT EDIT.",
        "   Source: grammar/phase1-surface.ebnf",
        f"   Source SHA-256: {digest}",
        "   Regenerate with: python3 scripts/derive_phase1_surface_grammar.py --write",
        "",
        "   This is the mechanically derived typed EBNF representation of the",
        "   canonical Phase 1 concrete grammar. Semantic acceptance remains",
        "   governed by the checked Phil declaration/Core contracts. *)",
        "",
        "Inductive EbnfExpression : Type :=",
        "| ELiteral : string -> EbnfExpression",
        "| ELexicalClass : string -> EbnfExpression",
        "| ENonterminal : string -> EbnfExpression",
        "| ESequence : list EbnfExpression -> EbnfExpression",
        "| EAlternative : list EbnfExpression -> EbnfExpression",
        "| EOptional : EbnfExpression -> EbnfExpression",
        "| ERepetition : EbnfExpression -> EbnfExpression.",
        "",
        "Definition GrammarRule : Type := (string * EbnfExpression)%type.",
        "",
        f"Definition phase1_surface_grammar_source_sha256 : string := {coq_string(digest)}.",
        'Definition phase1_surface_start : string := "source_file".',
        "",
        "Definition phase1_surface_keywords : list string :=",
        "  " + render_list([coq_string(keyword) for keyword in keywords]) + ".",
        "",
        "Definition phase1_surface_rules : list GrammarRule := [",
    ]
    for index, (name, node) in enumerate(rules):
        separator = ";" if index != len(rules) - 1 else ""
        lines.append(
            f"  ({coq_string(name)}, {render_node(node)}){separator}"
        )
    lines.extend(["].", ""])
    return "\n".join(lines)


def load(source: Path) -> tuple[str, list[tuple[str, Node]]]:
    source_text = source.read_text(encoding="utf-8")
    rules = Parser(tokenize(source_text)).parse_grammar()
    validate(rules)
    return source_text, rules


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
    except (OSError, ValueError) as error:
        print(f"phase1 grammar error: {error}", file=sys.stderr)
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
        print(f"phase1 grammar check: {error}", file=sys.stderr)
        return 2
    if existing != rendered:
        print(
            "phase1 grammar drift: generated Rocq artifact does not match "
            "grammar/phase1-surface.ebnf",
            file=sys.stderr,
        )
        print(
            "run: python3 scripts/derive_phase1_surface_grammar.py --write",
            file=sys.stderr,
        )
        return 1

    print("phase1 surface grammar: canonical EBNF and Rocq grammar agree")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
