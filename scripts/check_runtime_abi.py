#!/usr/bin/env python3
"""Compare Phil LLVM declarations with runtime-provider LLVM definitions.

LLVM's linker may legally reconcile incompatible global function types, so a
successful llvm-link is not by itself evidence that a runtime provider exactly
matches Phil's declared ABI.  This checker compares the LLVM function *types*
before linking.  It intentionally ignores linkage and parameter/return
attributes; the current Phase 0 contract here is exact result/argument type and
arity under the default calling convention.
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path


FUNCTION_RE = re.compile(r"@(?P<name>phil_[A-Za-z0-9_.$-]+)\((?P<args>.*)\)")
SCALAR_TYPE_RE = re.compile(r"\b(?:void|ptr|i[0-9]+)\b")


@dataclass(frozen=True)
class Signature:
    result: str
    arguments: tuple[str, ...]

    def render(self) -> str:
        return f"{self.result}({', '.join(self.arguments)})"


def canonical_type(text: str) -> str:
    return re.sub(r"\s+", "", text)


def aggregate_suffix(prefix: str) -> str | None:
    prefix = prefix.rstrip()
    if not prefix.endswith("}"):
        return None
    depth = 0
    for index in range(len(prefix) - 1, -1, -1):
        char = prefix[index]
        if char == "}":
            depth += 1
        elif char == "{":
            depth -= 1
            if depth == 0:
                return canonical_type(prefix[index:])
    raise ValueError(f"unbalanced aggregate return type: {prefix!r}")


def result_type(prefix: str) -> str:
    aggregate = aggregate_suffix(prefix)
    if aggregate is not None:
        return aggregate
    candidates = SCALAR_TYPE_RE.findall(prefix)
    if not candidates:
        raise ValueError(f"cannot identify LLVM result type in: {prefix!r}")
    return candidates[-1]


def split_arguments(text: str) -> list[str]:
    if not text.strip():
        return []
    pieces: list[str] = []
    start = 0
    braces = brackets = angles = parentheses = 0
    for index, char in enumerate(text):
        if char == "{":
            braces += 1
        elif char == "}":
            braces -= 1
        elif char == "[":
            brackets += 1
        elif char == "]":
            brackets -= 1
        elif char == "<":
            angles += 1
        elif char == ">":
            angles -= 1
        elif char == "(":
            parentheses += 1
        elif char == ")":
            parentheses -= 1
        elif char == "," and not any((braces, brackets, angles, parentheses)):
            pieces.append(text[start:index].strip())
            start = index + 1
    pieces.append(text[start:].strip())
    return pieces


def argument_type(argument: str) -> str:
    argument = argument.strip()
    if argument == "...":
        return argument
    if argument.startswith("{"):
        depth = 0
        for index, char in enumerate(argument):
            if char == "{":
                depth += 1
            elif char == "}":
                depth -= 1
                if depth == 0:
                    return canonical_type(argument[: index + 1])
        raise ValueError(f"unbalanced aggregate argument type: {argument!r}")
    match = re.match(r"(?:ptr|i[0-9]+)\b", argument)
    if match is None:
        raise ValueError(f"cannot identify LLVM argument type in: {argument!r}")
    return match.group(0)


def parse_functions(path: Path, keyword: str) -> dict[str, Signature]:
    functions: dict[str, Signature] = {}
    for line_number, raw_line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        line = raw_line.strip()
        if not line.startswith(keyword + " "):
            continue
        match = FUNCTION_RE.search(line)
        if match is None:
            continue
        name = match.group("name")
        prefix = line[: match.start()]
        signature = Signature(
            result=result_type(prefix),
            arguments=tuple(argument_type(piece) for piece in split_arguments(match.group("args"))),
        )
        if name in functions:
            raise ValueError(f"{path}:{line_number}: duplicate {keyword} for @{name}")
        functions[name] = signature
    return functions


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--partial", action="store_true",
                        help="compare only phil_* symbols defined by the provider")
    parser.add_argument("phil_ir", type=Path)
    parser.add_argument("provider_ir", type=Path)
    args = parser.parse_args()

    expected = parse_functions(args.phil_ir, "declare")
    actual = parse_functions(args.provider_ir, "define")

    if not expected:
        print(f"no phil_* declarations found in {args.phil_ir}", file=sys.stderr)
        return 2

    names = sorted(set(actual) & set(expected)) if args.partial else sorted(expected)
    if args.partial and not names:
        print("provider defines no Phil ABI symbols to compare", file=sys.stderr)
        return 2

    failures: list[str] = []
    for name in names:
        if name not in actual:
            failures.append(f"@{name}: missing provider definition; expected {expected[name].render()}")
            continue
        if actual[name] != expected[name]:
            failures.append(
                f"@{name}: expected {expected[name].render()}, provider defines {actual[name].render()}"
            )

    if failures:
        print("runtime ABI signature mismatch:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        return 1

    print(f"PASS: runtime provider matches {len(names)} Phil LLVM ABI signature(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
