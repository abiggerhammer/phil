#!/usr/bin/env python3
"""Exact runtime ABI checker regressions for historical ABI-01/ABI-02."""
from __future__ import annotations

import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

CHECKER = Path(os.environ.get("PHIL_ABI_CHECKER", str(Path(__file__).resolve().parents[1] / "check_runtime_abi.py")) )


class ABICompletenessTests(unittest.TestCase):
    def check_pair(
        self, declarations: str, definitions: str, expected: int,
        *, contains: str = "", partial: bool = False,
    ) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            phil = root / "phil.ll"
            provider = root / "provider.ll"
            phil.write_text(declarations, encoding="utf-8")
            provider.write_text(definitions, encoding="utf-8")
            command = [sys.executable, str(CHECKER)]
            if partial:
                command.append("--partial")
            result = subprocess.run(
                [*command, str(phil), str(provider)],
                capture_output=True, text=True, check=False,
            )
            self.assertEqual(
                expected, result.returncode,
                f"{command}: stdout={result.stdout!r}; stderr={result.stderr!r}",
            )
            if contains:
                self.assertIn(contains, result.stderr)

    def test_matching_default_scalar_and_pointer(self) -> None:
        self.check_pair(
            "declare i32 @phil_ping(ptr, i64)\n",
            "define i32 @phil_ping(ptr %p, i64 %n) { ret i32 0 }\n", 0,
        )

    def test_matching_aggregate_and_attribute(self) -> None:
        self.check_pair(
            "declare dso_local { i32, ptr } @phil_pair(ptr nocapture, i64)\n",
            "define dso_local { i32, ptr } @phil_pair(ptr %p, i64 %n) { ret { i32, ptr } zeroinitializer }\n", 0,
        )

    def test_abi01_pointer_argument_address_space(self) -> None:
        self.check_pair(
            "declare i32 @phil_ping(ptr addrspace(1))\n",
            "define i32 @phil_ping(ptr %p) { ret i32 0 }\n", 1,
            contains="phil_ping",
        )

    def test_abi01_pointer_result_address_space(self) -> None:
        self.check_pair(
            "declare ptr addrspace(3) @phil_ping(i32)\n",
            "define ptr @phil_ping(i32 %n) { ret ptr null }\n", 1,
            contains="phil_ping",
        )

    def test_abi01_matching_address_spaces(self) -> None:
        self.check_pair(
            "declare ptr addrspace(3) @phil_ping(ptr addrspace(1))\n",
            "define ptr addrspace(3) @phil_ping(ptr addrspace(1) %p) { ret ptr addrspace(3) null }\n", 0,
        )

    def test_abi02_quoted_required_name_is_not_skipped(self) -> None:
        self.check_pair(
            'declare void @phil_anchor()\ndeclare i32 @"phil_hidden"(i32)\n',
            "define void @phil_anchor() { ret void }\n", 1,
            contains="phil_hidden",
        )

    def test_abi02_multiline_required_name_is_not_skipped(self) -> None:
        self.check_pair(
            "declare void @phil_anchor()\ndeclare i32\n  @phil_multiline(\n    ptr,\n    i32\n  )\n",
            "define void @phil_anchor() { ret void }\n", 1,
            contains="phil_multiline",
        )

    def test_abi02_quoted_multiline_matching(self) -> None:
        self.check_pair(
            'declare i32\n  @"phil_hidden"(\n    ptr addrspace(2), i32\n  )\n',
            'define i32 @"phil_hidden"(ptr addrspace(2) %p, i32 %n) { ret i32 0 }\n', 0,
        )

    def test_unparseable_required_header_fails_closed(self) -> None:
        self.check_pair(
            "declare void @phil_anchor()\ndeclare i32 @phil_unparseable\n",
            "define void @phil_anchor() { ret void }\n", 2,
            contains="phil_unparseable",
        )

    def test_nondefault_fastcc_is_rejected(self) -> None:
        self.check_pair(
            "declare fastcc i32 @phil_ping(i32)\n",
            "define fastcc i32 @phil_ping(i32 %n) { ret i32 0 }\n", 2,
            contains="calling convention",
        )

    def test_nondefault_numeric_cc_is_rejected(self) -> None:
        self.check_pair(
            "declare cc 10 i32 @phil_ping(i32)\n",
            "define cc 10 i32 @phil_ping(i32 %n) { ret i32 0 }\n", 2,
            contains="calling convention",
        )

    def test_explicit_default_cc_is_allowed(self) -> None:
        self.check_pair(
            "declare ccc i32 @phil_ping(i32)\n",
            "define ccc i32 @phil_ping(i32 %n) { ret i32 0 }\n", 0,
        )

    def test_partial_provider_still_excludes_unprovided_names(self) -> None:
        self.check_pair(
            "declare void @phil_one()\ndeclare void @phil_two()\n",
            "define void @phil_one() { ret void }\n", 0, partial=True,
        )

    def test_partial_still_rejects_mismatched_present_name(self) -> None:
        self.check_pair(
            "declare i32 @phil_one(i32)\ndeclare void @phil_two()\n",
            "define i32 @phil_one(i64 %x) { ret i32 0 }\n", 1, partial=True,
            contains="phil_one",
        )


if __name__ == "__main__":
    unittest.main(verbosity=2)
