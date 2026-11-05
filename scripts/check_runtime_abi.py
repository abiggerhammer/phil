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


# Recognize quoted and unquoted LLVM global identifiers. Preserve the actual
# address space in opaque-pointer types rather than reducing all pointers to ptr.
FUNCTION_RE = re.compile(r'@(?:"(?P<quoted>[^"]+)"|(?P<plain>[A-Za-z0-9_.$-]+))\s*\(')
SCALAR_TYPE_RE = re.compile(r'\b(?:void|ptr(?:\s+addrspace\(\d+\))?|i[0-9]+)(?!\w)')
ARGUMENT_TYPE_RE = re.compile(r'^(?:ptr(?:\s+addrspace\(\d+\))?|i[0-9]+)(?!\w)')
NONDEFAULT_CC_RE = re.compile(r'\b(?:[A-Za-z_][A-Za-z0-9_]*cc|cc\s+[0-9]+)\b')


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
    match = ARGUMENT_TYPE_RE.match(argument)
    if match is None:
        raise ValueError(f"cannot identify LLVM argument type in: {argument!r}")
    if match.group(0) == "ptr" and re.match(r"^ptr\s+addrspace\b", argument):
        raise ValueError(f"malformed pointer address space in: {argument!r}")
    return canonical_type(match.group(0))


def matching_close_parenthesis(text: str, opening: int) -> int | None:
    depth = 0
    for index in range(opening, len(text)):
        if text[index] == "(":
            depth += 1
        elif text[index] == ")":
            depth -= 1
            if depth == 0:
                return index
    return None


def required_function_header(header: str, path: Path, line_number: int) -> tuple[str, Signature] | None:
    match = FUNCTION_RE.search(header)
    if match is None:
        if "phil_" in header:
            raise ValueError(
                f"{path}:{line_number}: cannot parse required Phil ABI declaration/definition: {header!r}"
            )
        return None

    name = match.group("quoted") or match.group("plain")
    if not name.startswith("phil_"):
        return None
    if not re.fullmatch(r"phil_[A-Za-z0-9_.$-]+", name):
        raise ValueError(f"{path}:{line_number}: unsupported Phil ABI symbol spelling: {name!r}")

    prefix = header[:match.start()]
    # The only supported calling convention at this boundary is the default
    # C calling convention (implicit or explicit ccc). Attributes remain outside
    # the exact signature comparison by the documented Phase 0 contract.
    conventions = NONDEFAULT_CC_RE.findall(prefix)
    if any(convention != "ccc" for convention in conventions):
        raise ValueError(
            f"{path}:{line_number}: unsupported calling convention for @{name}: {conventions}"
        )
    closing = matching_close_parenthesis(header, match.end() - 1)
    if closing is None:
        raise ValueError(f"{path}:{line_number}: incomplete Phil ABI parameters for @{name}")
    arguments = header[match.end():closing]
    signature = Signature(
        result=result_type(prefix),
        arguments=tuple(argument_type(piece) for piece in split_arguments(arguments)),
    )
    return name, signature


def parse_functions(path: Path, keyword: str) -> dict[str, Signature]:
    functions: dict[str, Signature] = {}
    lines = path.read_text(encoding="utf-8").splitlines()
    index = 0
    while index < len(lines):
        line_number = index + 1
        line = lines[index].strip()
        index += 1
        if not re.match(rf"^{keyword}\s+", line):
            continue

        # LLVM permits line wrapping in declarations and in function headers.
        # Collect the header only through the parameter-closing parenthesis;
        # never consume the function body or unrelated following declarations.
        header = line
        while True:
            found = FUNCTION_RE.search(header)
            if found is not None and matching_close_parenthesis(header, found.end() - 1) is not None:
                break
            if index >= len(lines):
                break
            next_line = lines[index].strip()
            if re.match(r"^(?:declare|define)\s+", next_line) or next_line.startswith("}"):
                break
            header += " " + next_line
            index += 1
            if index - line_number >= 100:
                raise ValueError(f"{path}:{line_number}: oversized or malformed LLVM function header")

        parsed = required_function_header(header, path, line_number)
        if parsed is None:
            continue
        name, signature = parsed
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

    try:
        expected = parse_functions(args.phil_ir, "declare")
        actual = parse_functions(args.provider_ir, "define")
    except ValueError as error:
        print(f"runtime ABI parse error: {error}", file=sys.stderr)
        return 2

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
