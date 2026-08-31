#!/usr/bin/env python3
"""Audit local concrete-choice determinacy in the canonical Phase 1 EBNF.

This is an executable SURF-005 review boundary, not a parser soundness proof.
It derives nullable/FIRST/FOLLOW facts from the normative EBNF and inventories
exactly those alternatives or optional/repeated boundaries whose next-token
languages overlap and therefore require an explicit reviewed disposition.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

from derive_phase1_surface_grammar import (
    Alternative,
    LexicalClass,
    Literal,
    Node,
    OptionalNode,
    Reference,
    Repeat,
    Sequence,
    load,
)

ROOT = Path(__file__).resolve().parents[1]
GRAMMAR = ROOT / "grammar" / "phase1-surface.ebnf"
INVENTORY = ROOT / "grammar" / "phase1-surface-determinacy.json"
EOF = "<EOF>"
EPSILON = "<epsilon>"
FINDING_FIELDS = ("kind", "rule", "path", "tokens", "detail")


def atom_key(node: Node) -> str | None:
    if isinstance(node, Literal):
        return "literal:" + json.dumps(node.value, ensure_ascii=False)
    if isinstance(node, LexicalClass):
        return f"class:<{node.name}>"
    return None


def nullable(node: Node, nullable_rules: dict[str, bool]) -> bool:
    if isinstance(node, (Literal, LexicalClass)):
        return False
    if isinstance(node, Reference):
        return nullable_rules[node.name]
    if isinstance(node, Sequence):
        return all(nullable(item, nullable_rules) for item in node.items)
    if isinstance(node, Alternative):
        return any(nullable(item, nullable_rules) for item in node.items)
    if isinstance(node, (OptionalNode, Repeat)):
        return True
    raise TypeError(node)


def first(
    node: Node,
    first_rules: dict[str, set[str]],
    nullable_rules: dict[str, bool],
) -> set[str]:
    atom = atom_key(node)
    if atom is not None:
        return {atom}
    if isinstance(node, Reference):
        return set(first_rules[node.name])
    if isinstance(node, Sequence):
        out: set[str] = set()
        for item in node.items:
            out.update(first(item, first_rules, nullable_rules))
            if not nullable(item, nullable_rules):
                break
        return out
    if isinstance(node, Alternative):
        out: set[str] = set()
        for item in node.items:
            out.update(first(item, first_rules, nullable_rules))
        return out
    if isinstance(node, (OptionalNode, Repeat)):
        return first(node.item, first_rules, nullable_rules)
    raise TypeError(node)


def derive_nullable_first(
    rules: list[tuple[str, Node]],
) -> tuple[dict[str, bool], dict[str, set[str]]]:
    nullable_rules = {name: False for name, _ in rules}
    first_rules = {name: set() for name, _ in rules}

    changed = True
    while changed:
        changed = False
        for name, node in rules:
            value = nullable(node, nullable_rules)
            if value and not nullable_rules[name]:
                nullable_rules[name] = True
                changed = True
            values = first(node, first_rules, nullable_rules)
            if not values.issubset(first_rules[name]):
                first_rules[name].update(values)
                changed = True
    return nullable_rules, first_rules


def suffix_first_nullable(
    items: tuple[Node, ...],
    start: int,
    first_rules: dict[str, set[str]],
    nullable_rules: dict[str, bool],
) -> tuple[set[str], bool]:
    out: set[str] = set()
    all_nullable = True
    for item in items[start:]:
        out.update(first(item, first_rules, nullable_rules))
        if not nullable(item, nullable_rules):
            all_nullable = False
            break
    return out, all_nullable


def propagate_follow(
    node: Node,
    outer_follow: set[str],
    follow_rules: dict[str, set[str]],
    first_rules: dict[str, set[str]],
    nullable_rules: dict[str, bool],
) -> bool:
    changed = False
    if isinstance(node, Reference):
        before = len(follow_rules[node.name])
        follow_rules[node.name].update(outer_follow)
        return len(follow_rules[node.name]) != before
    if isinstance(node, Sequence):
        for index, item in enumerate(node.items):
            local_follow, suffix_nullable = suffix_first_nullable(
                node.items, index + 1, first_rules, nullable_rules
            )
            if suffix_nullable:
                local_follow.update(outer_follow)
            changed |= propagate_follow(
                item, local_follow, follow_rules, first_rules, nullable_rules
            )
        return changed
    if isinstance(node, Alternative):
        for item in node.items:
            changed |= propagate_follow(
                item, outer_follow, follow_rules, first_rules, nullable_rules
            )
        return changed
    if isinstance(node, OptionalNode):
        return propagate_follow(
            node.item, outer_follow, follow_rules, first_rules, nullable_rules
        )
    if isinstance(node, Repeat):
        repeated_follow = set(outer_follow)
        repeated_follow.update(first(node.item, first_rules, nullable_rules))
        return propagate_follow(
            node.item, repeated_follow, follow_rules, first_rules, nullable_rules
        )
    return False


def derive_follow(
    rules: list[tuple[str, Node]],
    first_rules: dict[str, set[str]],
    nullable_rules: dict[str, bool],
) -> dict[str, set[str]]:
    follow_rules = {name: set() for name, _ in rules}
    follow_rules["source_file"].add(EOF)
    changed = True
    while changed:
        changed = False
        for name, node in rules:
            changed |= propagate_follow(
                node,
                follow_rules[name],
                follow_rules,
                first_rules,
                nullable_rules,
            )
    return follow_rules


@dataclass(frozen=True, order=True)
class Finding:
    kind: str
    rule: str
    path: str
    tokens: tuple[str, ...]
    detail: str

    def as_json(self) -> dict[str, object]:
        return {
            "kind": self.kind,
            "rule": self.rule,
            "path": self.path,
            "tokens": list(self.tokens),
            "detail": self.detail,
        }


def audit_node(
    node: Node,
    rule: str,
    path: str,
    outer_follow: set[str],
    first_rules: dict[str, set[str]],
    nullable_rules: dict[str, bool],
) -> Iterable[Finding]:
    if isinstance(node, Alternative):
        for left_index, left in enumerate(node.items):
            for right_index in range(left_index + 1, len(node.items)):
                right = node.items[right_index]
                overlap = first(left, first_rules, nullable_rules) & first(
                    right, first_rules, nullable_rules
                )
                tokens = set(overlap)
                if nullable(left, nullable_rules) and nullable(right, nullable_rules):
                    tokens.add(EPSILON)
                if tokens:
                    yield Finding(
                        "alternative-first-overlap",
                        rule,
                        path,
                        tuple(sorted(tokens)),
                        f"branches {left_index} and {right_index}",
                    )
        for index, item in enumerate(node.items):
            yield from audit_node(
                item,
                rule,
                f"{path}/alt[{index}]",
                outer_follow,
                first_rules,
                nullable_rules,
            )
        return

    if isinstance(node, Sequence):
        for index, item in enumerate(node.items):
            local_follow, suffix_nullable = suffix_first_nullable(
                node.items, index + 1, first_rules, nullable_rules
            )
            if suffix_nullable:
                local_follow.update(outer_follow)
            yield from audit_node(
                item,
                rule,
                f"{path}/seq[{index}]",
                local_follow,
                first_rules,
                nullable_rules,
            )
        return

    if isinstance(node, OptionalNode):
        overlap = first(node.item, first_rules, nullable_rules) & outer_follow
        if nullable(node.item, nullable_rules):
            overlap = set(overlap)
            overlap.add(EPSILON)
        if overlap:
            yield Finding(
                "optional-follow-overlap",
                rule,
                path,
                tuple(sorted(overlap)),
                "optional body can begin with a token that can also follow the optional",
            )
        yield from audit_node(
            node.item,
            rule,
            f"{path}/optional",
            outer_follow,
            first_rules,
            nullable_rules,
        )
        return

    if isinstance(node, Repeat):
        if nullable(node.item, nullable_rules):
            yield Finding(
                "nullable-repetition",
                rule,
                path,
                (EPSILON,),
                "repetition body is nullable",
            )
        overlap = first(node.item, first_rules, nullable_rules) & outer_follow
        if overlap:
            yield Finding(
                "repeat-follow-overlap",
                rule,
                path,
                tuple(sorted(overlap)),
                "another repetition can begin with a token that can also follow the repetition",
            )
        repeated_follow = set(outer_follow)
        repeated_follow.update(first(node.item, first_rules, nullable_rules))
        yield from audit_node(
            node.item,
            rule,
            f"{path}/repeat",
            repeated_follow,
            first_rules,
            nullable_rules,
        )


def findings(rules: list[tuple[str, Node]]) -> list[Finding]:
    nullable_rules, first_rules = derive_nullable_first(rules)
    follow_rules = derive_follow(rules, first_rules, nullable_rules)
    out: set[Finding] = set()
    for name, node in rules:
        out.update(
            audit_node(
                node,
                name,
                name,
                follow_rules[name],
                first_rules,
                nullable_rules,
            )
        )
    return sorted(out)


def finding_projection(entry: object) -> dict[str, object]:
    if not isinstance(entry, dict):
        raise ValueError("every determinacy overlap must be a JSON object")
    missing = [field for field in FINDING_FIELDS if field not in entry]
    if missing:
        raise ValueError(f"determinacy overlap missing finding fields: {missing}")
    return {field: entry[field] for field in FINDING_FIELDS}


def validate_reviewed_entries(entries: object) -> list[dict[str, object]]:
    if not isinstance(entries, list):
        raise ValueError("reviewed_overlaps must be a JSON list")
    projected: list[dict[str, object]] = []
    for index, entry in enumerate(entries):
        finding = finding_projection(entry)
        disposition = entry.get("disposition") if isinstance(entry, dict) else None
        pressure = entry.get("pressure") if isinstance(entry, dict) else None
        if not isinstance(disposition, str) or not disposition.strip():
            raise ValueError(f"reviewed overlap {index} needs a nonempty disposition")
        if (
            not isinstance(pressure, list)
            or not pressure
            or not all(isinstance(value, str) and value.strip() for value in pressure)
        ):
            raise ValueError(f"reviewed overlap {index} needs nonempty parser-pressure references")
        projected.append(finding)
    return projected


def review_template(digest: str, actual: list[dict[str, object]]) -> dict[str, object]:
    return {
        "authority": "grammar/phase1-surface.ebnf",
        "grammar_sha256": digest,
        "reviewed_overlaps": [
            {
                **finding,
                "disposition": "REVIEW REQUIRED",
                "pressure": [],
            }
            for finding in actual
        ],
    }


def main() -> int:
    source_text, rules = load(GRAMMAR)
    digest = hashlib.sha256(source_text.encode("utf-8")).hexdigest()
    actual = [finding.as_json() for finding in findings(rules)]
    inventory = json.loads(INVENTORY.read_text(encoding="utf-8"))

    try:
        if inventory.get("authority") != "grammar/phase1-surface.ebnf":
            raise ValueError("determinacy inventory authority must remain grammar/phase1-surface.ebnf")
        expected = validate_reviewed_entries(inventory.get("reviewed_overlaps"))
    except ValueError as error:
        print(f"Phase 1 surface determinacy inventory error: {error}")
        print(json.dumps(review_template(digest, actual), ensure_ascii=False, indent=2, sort_keys=True))
        return 1

    expected_digest = inventory.get("grammar_sha256")
    if expected_digest == digest and expected == actual:
        print(
            f"Phase 1 surface determinacy: {len(actual)} reviewed local overlap(s), inventory exact"
        )
        return 0

    print("Phase 1 surface determinacy inventory drift.")
    print("Review every overlap, then replace grammar/phase1-surface-determinacy.json with:")
    print(json.dumps(review_template(digest, actual), ensure_ascii=False, indent=2, sort_keys=True))
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
