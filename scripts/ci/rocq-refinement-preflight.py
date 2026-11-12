#!/usr/bin/env python3
"""Rocq 9.2 prepublication preflight: replay CI's exact proof targets and gates."""
from __future__ import annotations

from pathlib import Path
import hashlib
import os
import re
import subprocess

WORKFLOW = Path(".github/workflows/phase1-surface-grammar-rocq-source-spine-correspondence.yml")
STEPS = (
    "Derive exact Grammar-v1 inputs",
    "Compile source correspondence, representation bridges, and grouping consumers",
    "Compile new generic-requirement modules with all warnings enabled",
    "Check recursive grouping and carrier composition theorem assumptions",
)
MODULES = (
    "GrammarAstGenericRequirementRecursiveGroupingSpine",
    "GrammarAstGenericRequirementRecursiveGroupingSpineTotality",
    "GrammarAstGenericRequirementRecursiveGroupingExamples",
)


def step_script(lines: list[str], name: str) -> str:
    marker = "      - name: " + name
    if lines.count(marker) != 1:
        raise RuntimeError(f"CI step not uniquely present: {name}")
    start = lines.index(marker) + 1
    run_marker = "        run: |"
    if run_marker not in lines[start:start + 8]:
        raise RuntimeError(f"CI step lacks bash script: {name}")
    start = lines.index(run_marker, start, start + 8) + 1
    output: list[str] = []
    for line in lines[start:]:
        if line and not line.startswith("          "):
            break
        output.append(line[10:] if line else "")
    if not output or output[0] != "set -euo pipefail":
        raise RuntimeError(f"CI step is empty or lacks strict execution: {name}")
    script = "\n".join(output)
    if name.startswith("Compile source correspondence"):
        for required in (
            "rocq makefile -f _CoqProject.surface-source-spine",
            "GrammarAstGenericRequirementRecursiveGroupingExamples.vo",
        ):
            if required not in script:
                raise RuntimeError(f"authoritative CI target missing: {required}")
    return script


def main() -> None:
    compiler = os.environ.get("COMPILER")
    if compiler:
        os.environ["PATH"] = f"/home/rocq/.opam/{compiler}/bin:" + os.environ["PATH"]
    version = subprocess.run(["rocq", "-v"], check=True, text=True,
                             capture_output=True)
    info = (version.stdout + version.stderr).strip()
    print(f"Compiler: {info}", flush=True)
    # The pinned 9.2.0 image advertises ROCQ_VERSION=9.2.0 but its
    # CLI prints "The Rocq Prover, version 9.2". Accept that exact
    # shortened presentation; do not mistake 9.2.1 or 9.20 for it.
    pinned = os.environ.get("ROCQ_VERSION")
    if pinned != "9.2.0":
        raise RuntimeError(f"expected pinned container ROCQ_VERSION=9.2.0, got {pinned!r}")
    if not re.search(r"(?<![\d.])9\.2(?:\.0)?(?![\d.])", info):
        raise RuntimeError("Rocq 9.2.0 (CLI 9.2) required; refusing other toolchain")
    source_sha = subprocess.run(["git", "rev-parse", "--verify", "HEAD"],
                                check=True, capture_output=True, text=True).stdout.strip()
    if not re.fullmatch(r"[0-9a-f]{40}", source_sha):
        raise RuntimeError(f"invalid checked-out source SHA: {source_sha!r}")
    expected_sha = os.environ.get("GITHUB_SHA")
    if expected_sha is not None and expected_sha != source_sha:
        raise RuntimeError(f"Actions/source SHA mismatch: {expected_sha} != {source_sha}")
    print(f"Source SHA: {source_sha}", flush=True)
    lines = WORKFLOW.read_text(encoding="utf-8").splitlines()
    for name in STEPS:
        print(f"CI-exact preflight: {name}", flush=True)
        subprocess.run(["bash", "-euo", "pipefail", "-c", step_script(lines, name)],
                       check=True)
    for name in MODULES:
        path = Path("proof/Phil/Surface") / (name + ".v")
        data = path.read_bytes()
        if re.search(rb"(?m)^\s*(?:Admitted\s*\.|Axiom\s|Parameter\s)", data):
            raise RuntimeError(f"new proof admission forbidden: {path}")
        print(f"sha256={hashlib.sha256(data).hexdigest()} {path}", flush=True)
    print("PASS: version-pinned CI-exact make targets, -w +all and Print Assumptions",
          flush=True)


if __name__ == "__main__":
    main()
