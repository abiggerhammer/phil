#!/usr/bin/env python3
"""Deterministic shell-policy linter for Mecha Hamster Ball snapshots."""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass
from typing import Any

SUPPORTED_LANES = {
    "auto-pr": {"proof-audit", "rocq-refinement", "impl-audit"},
    "merge": {"proof-audit", "rocq-refinement", "impl-audit"},
    "refresh": {"impl-audit"},
}

PHASE1_INT007_ALLOWED = re.compile(
    r"^(handoff/phase1/manifest-v1\.tsv|"
    r"handoff/phase1/witnesses/(upload|steve)-"
    r"(verification-bundle|assurance-manifest|residual-tcb)-v1\.tsv)$"
)


@dataclass(frozen=True)
class Diagnostic:
    rule_id: str
    severity: str
    name: str
    message: str
    details: dict[str, Any]


def diagnostic(
    rule_id: str,
    name: str,
    message: str,
    **details: Any,
) -> Diagnostic:
    return Diagnostic(
        rule_id=rule_id,
        severity="error",
        name=name,
        message=message,
        details=details,
    )


def lint_snapshot(snapshot: dict[str, Any]) -> list[Diagnostic]:
    """Return stable diagnostics for one repository/GitHub state snapshot."""

    out: list[Diagnostic] = []

    operation = str(snapshot.get("operation", ""))
    lane = str(snapshot.get("lane", ""))
    supported = SUPPORTED_LANES.get(operation, set())
    if lane not in supported:
        out.append(
            diagnostic(
                "MHB001",
                "unsupported-lane",
                f"lane {lane!r} is unsupported for operation {operation!r}",
                lane=lane,
                operation=operation,
                supported_lanes=sorted(supported),
            )
        )

    pr = snapshot.get("pr")
    if not isinstance(pr, dict):
        pr = {}

    labels = sorted(str(label) for label in pr.get("labels", []))
    expected_label = f"lane: {lane}"
    lane_labels = sorted(label for label in labels if label.startswith("lane: "))
    if expected_label not in lane_labels or any(
        label != expected_label for label in lane_labels
    ):
        out.append(
            diagnostic(
                "MHB002",
                "lane-label-mismatch",
                "native PR lane label does not exactly match the authorized lane",
                lane=lane,
                expected_label=expected_label,
                observed_lane_labels=lane_labels,
            )
        )

    head_ref = str(pr.get("head_ref", ""))
    expected_prefix = f"hamster/{lane}/"
    if not head_ref.startswith(expected_prefix):
        out.append(
            diagnostic(
                "MHB003",
                "lane-head-ownership-mismatch",
                "PR head branch is not owned by the authorized lane",
                lane=lane,
                head_ref=head_ref,
                expected_prefix=expected_prefix,
            )
        )

    expected_head = str(snapshot.get("expected_head", ""))
    live_head = str(pr.get("head_sha", ""))
    if not expected_head or live_head != expected_head:
        out.append(
            diagnostic(
                "MHB004",
                "stale-exact-head",
                "live PR head does not match the exact authorized revision",
                expected_head=expected_head,
                live_head=live_head,
            )
        )

    checks = snapshot.get("checks")
    if not isinstance(checks, dict):
        checks = {}
    runs = checks.get("runs", [])
    if not isinstance(runs, list):
        runs = []
    try:
        total_count = int(checks.get("total_count", 0))
    except (TypeError, ValueError):
        total_count = 0

    if total_count <= 0 or len(runs) != total_count:
        out.append(
            diagnostic(
                "MHB005",
                "incomplete-check-census",
                "exact-head check-run census is empty or incomplete",
                total_count=total_count,
                returned_count=len(runs),
            )
        )

    bad_checks: list[dict[str, str]] = []
    for run in runs:
        if not isinstance(run, dict):
            bad_checks.append(
                {"name": "<malformed>", "status": "", "conclusion": ""}
            )
            continue
        status = str(run.get("status", ""))
        conclusion = str(run.get("conclusion", ""))
        if status != "completed" or conclusion != "success":
            bad_checks.append(
                {
                    "name": str(run.get("name", "")),
                    "status": status,
                    "conclusion": conclusion,
                }
            )
    bad_checks.sort(key=lambda item: (item["name"], item["status"], item["conclusion"]))
    if bad_checks:
        out.append(
            diagnostic(
                "MHB006",
                "unsuccessful-exact-head-check",
                "one or more exact-head checks are not completed successfully",
                checks=bad_checks,
            )
        )

    base_sha = str(pr.get("base_sha", ""))
    main_sha = str(snapshot.get("main_sha", ""))
    if base_sha and main_sha and base_sha != main_sha:
        pr_files = {str(path) for path in pr.get("changed_files", [])}
        intervening_files = {
            str(path) for path in snapshot.get("intervening_main_files", [])
        }
        overlap = sorted(pr_files & intervening_files)
        if overlap:
            out.append(
                diagnostic(
                    "MHB007",
                    "intervening-main-overlap",
                    "intervening main changes overlap files changed by the PR",
                    base_sha=base_sha,
                    main_sha=main_sha,
                    overlapping_paths=overlap,
                )
            )

    if operation == "refresh":
        family = str(snapshot.get("refresh_family", ""))
        changed_paths = sorted(
            str(path) for path in snapshot.get("generated_changed_paths", [])
        )
        if family == "phase1-int007":
            unauthorized = [
                path for path in changed_paths if PHASE1_INT007_ALLOWED.fullmatch(path) is None
            ]
        else:
            unauthorized = changed_paths
        if unauthorized:
            out.append(
                diagnostic(
                    "MHB008",
                    "unauthorized-generated-path",
                    "generated refresh attempts to modify a path outside its authorized family",
                    refresh_family=family,
                    unauthorized_paths=unauthorized,
                )
            )

    return sorted(
        out,
        key=lambda item: (
            item.rule_id,
            item.name,
            json.dumps(item.details, sort_keys=True, separators=(",", ":")),
        ),
    )


def render_text(diags: list[Diagnostic]) -> str:
    lines = []
    for item in diags:
        details = json.dumps(item.details, sort_keys=True, separators=(",", ":"))
        lines.append(
            f"{item.rule_id} {item.severity} {item.name}: {item.message} {details}"
        )
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "snapshot",
        nargs="?",
        default="-",
        help="JSON snapshot path, or - for stdin",
    )
    parser.add_argument(
        "--format",
        choices=("text", "json"),
        default="text",
        help="diagnostic output format",
    )
    args = parser.parse_args(argv)

    if args.snapshot == "-":
        snapshot = json.load(sys.stdin)
    else:
        with open(args.snapshot, "r", encoding="utf-8") as handle:
            snapshot = json.load(handle)

    if not isinstance(snapshot, dict):
        raise SystemExit("snapshot root must be a JSON object")

    diags = lint_snapshot(snapshot)
    if args.format == "json":
        json.dump(
            [asdict(item) for item in diags],
            sys.stdout,
            sort_keys=True,
            separators=(",", ":"),
        )
        sys.stdout.write("\n")
    else:
        rendered = render_text(diags)
        if rendered:
            sys.stdout.write(rendered + "\n")

    return 1 if diags else 0


if __name__ == "__main__":
    raise SystemExit(main())
