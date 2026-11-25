"""Offline G2-1 inventory and deny-by-default candidate policy.

No provider calls, credential handling, or repository mutations. The caller
must authenticate the exact source before using an eligibility decision.
"""
from __future__ import annotations

import fnmatch
import hashlib
import itertools
import json
from pathlib import Path
import re
from typing import Any

import yaml

from test_mhb_atc_staged_push_ci import StrictWorkflowLoader

EVENTS = frozenset({
    "push", "pull_request", "pull_request_target", "workflow_run",
    "repository_dispatch", "workflow_dispatch", "schedule", "release",
    "workflow_call",
})
CANDIDATE_EVENTS = {"pull_request", "push"}
EXPRESSION = re.compile(r"\$\{\{\s*(.*?)\s*\}\}", re.DOTALL)
SECRET_CONTEXT = re.compile(r"\bsecrets\b", re.IGNORECASE)
PUBLIC_CONTEXT = frozenset({
    "github.sha", "github.ref", "github.repository",
    "github.run_id", "github.run_attempt",
})
CHECKOUT = "actions/checkout@11d5960a326750d5838078e36cf38b85af677262"
HOSTED = {"ubuntu-24.04", "ubuntu-latest", "macos-26", "windows-latest"}
POLICY = Path(__file__).with_name("mhb_atc_g2_policy_v1.json")


def workflow(source: str) -> tuple[dict, dict]:
    doc = yaml.load(source, Loader=StrictWorkflowLoader)
    if not isinstance(doc, dict):
        raise ValueError("WORKFLOW_SCHEMA")
    events = doc.get("on")
    if isinstance(events, str):
        events = {events: ""}
    elif isinstance(events, list) and all(isinstance(item, str) for item in events):
        if len(set(events)) != len(events):
            raise ValueError("EVENT_DUPLICATE")
        events = dict.fromkeys(events, "")
    jobs = doc.get("jobs")
    if not isinstance(events, dict) or not events or set(events) - EVENTS:
        raise ValueError("EVENT_SCHEMA")
    if not isinstance(jobs, dict) or not jobs or any(not isinstance(j, dict) for j in jobs.values()):
        raise ValueError("JOB_SCHEMA")
    return doc, events


def strings(node: Any):
    if isinstance(node, str):
        yield node
    elif isinstance(node, list):
        for item in node:
            yield from strings(item)
    elif isinstance(node, dict):
        for key, value in node.items():
            yield str(key)
            yield from strings(value)


def expression_problem(node: Any) -> str | None:
    for value in strings(node):
        for expr in EXPRESSION.findall(value):
            if SECRET_CONTEXT.search(expr):
                return "SECRET_CONTEXT"
            if expr not in PUBLIC_CONTEXT:
                return "EXPRESSION_UNKNOWN"
        if "${{" in EXPRESSION.sub("", value):
            return "EXPRESSION_UNKNOWN"
    return None


def candidate_policy(source: str, job_name: str, event: str, *, selected_source: str) -> str:
    """Return ELIGIBLE or an exact rule. Provenance labels are caller premises.

    Only hosted, direct candidate PR/branch jobs in the reviewed subset can
    pass. Other event types, off-pin selection, reusable and transitive
    execution routes need a separate authority decision and are denied here.
    """
    try:
        doc, events = workflow(source)
    except (ValueError, yaml.YAMLError, RecursionError):
        return "WORKFLOW_SCHEMA"
    return policy_for_document(doc, events, job_name, event, selected_source)


def policy_for_document(doc: dict, events: dict, job_name: str, event: str,
                        selected_source: str) -> str:
    if event not in events or event not in CANDIDATE_EVENTS:
        return "EVENT_AUTHORITY"
    if event == "push":
        filters = events[event]
        if not isinstance(filters, dict) or not filters.get("branches") or any(
            key in filters for key in ("tags", "tags-ignore")
        ):
            return "EVENT_AUTHORITY"
    if selected_source != "reviewed-exact":
        return "SOURCE_AUTHORITY"
    job = doc["jobs"].get(job_name)
    if job is None:
        return "JOB_UNKNOWN"
    permissions = job.get("permissions", doc.get("permissions"))
    if permissions is None:
        return "PERMISSIONS_ABSENT"
    if not isinstance(permissions, dict) or any(
        key != "contents" or value not in ("read", "none")
        for key, value in permissions.items()
    ):
        return "PERMISSIONS_UNSAFE"
    problem = expression_problem({k: v for k, v in doc.items() if k != "jobs"} | {"job": job})
    if problem:
        return problem
    if set(doc) - {
        "name", "run-name", "on", "permissions", "jobs", "env",
    } or set(job) - {
        "name", "permissions", "runs-on", "steps", "env", "timeout-minutes",
    }:
        return "INDIRECT_AUTHORITY"
    if not isinstance(job.get("runs-on"), str) or job["runs-on"] not in HOSTED:
        return "RUNNER_AUTHORITY"
    if not isinstance(job.get("steps"), list) or not job["steps"]:
        return "STEP_SCHEMA"
    for step in job["steps"]:
        if not isinstance(step, dict) or set(step) - {"name", "id", "uses", "with", "run", "shell", "env"}:
            return "STEP_SCHEMA"
        if "uses" in step:
            if not isinstance(step["uses"], str) or not step["uses"].startswith("actions/checkout@"):
                return "ACTION_AUTHORITY"
            options = step.get("with", {})
            if not isinstance(options, dict) or options.get("persist-credentials") != "false":
                return "CHECKOUT_PERSISTENCE"
            if set(options) - {"persist-credentials", "fetch-depth"}:
                return "CHECKOUT_SOURCE"
            if step["uses"] != CHECKOUT:
                return "ACTION_AUTHORITY"
            if "run" in step:
                return "STEP_SCHEMA"
        elif not isinstance(step.get("run"), str) or "with" in step:
            return "STEP_SCHEMA"
    return "ELIGIBLE"


def definitions(root: Path) -> list[dict]:
    rows = []
    for path in sorted((*root.glob("*.yml"), *root.glob("*.yaml"))):
        raw = path.read_bytes()
        doc, events = workflow(raw.decode())
        blob = hashlib.sha1(f"blob {len(raw)}\0".encode() + raw).hexdigest()
        for job in doc["jobs"]:
            for event in events:
                rows.append(dict(workflow=path.name, blob=blob, job=job, event=event,
                                 decision=policy_for_document(doc, events, job, event,
                                                              "reviewed-exact")))
    return sorted(rows, key=lambda r: (r["workflow"], r["job"], r["event"]))


def verify_inventory(expected: list[dict], actual: list[dict]) -> None:
    def index(rows):
        mapped = {(r["workflow"], r["job"], r["event"]): r for r in rows}
        if len(mapped) != len(rows):
            raise ValueError("INVENTORY_DUPLICATE")
        return mapped
    before, after = index(expected), index(actual)
    if before.keys() != after.keys():
        raise ValueError("INVENTORY_IDENTITIES")
    if before != after:
        raise ValueError("INVENTORY_STALE")


def variants(matrix: Any) -> dict:
    """Expand only finite literal scalar matrices; unresolved is explicit."""
    unresolved = {"state": "unresolved", "variants": []}
    if matrix is None:
        return {"state": "expanded", "variants": [{}]}
    if not isinstance(matrix, dict):
        return unresolved
    axes = {k: v for k, v in matrix.items() if k not in ("include", "exclude")}
    def valid(value):
        return isinstance(value, str) and not any(s in value for s in ("$", "{", "}"))
    if any(not isinstance(v, list) or not v or not all(valid(x) for x in v) for v in axes.values()):
        return unresolved
    includes, excludes = matrix.get("include", []), matrix.get("exclude", [])
    if any(not isinstance(items, list) or any(
        not isinstance(x, dict) or not x or not all(valid(v) for v in x.values()) for x in items
    ) for items in (includes, excludes)):
        return unresolved
    size = 1
    for axis in axes.values():
        size *= len(axis)
    if size + len(includes) > 256:
        return unresolved
    originals = []
    if axes:
        for product in itertools.product(*axes.values()):
            value = dict(zip(axes, product))
            if not any(all(value.get(k) == v for k, v in rule.items()) for rule in excludes):
                originals.append(value)
    result = [dict(x) for x in originals]
    for inc in includes:
        targets = [i for i, row in enumerate(originals)
                   if all(key not in row or row[key] == value for key, value in inc.items())]
        if not targets:
            result.append(dict(inc))
        for i in targets:
            result[i].update(inc)
    return {"state": "expanded", "variants": result if axes or includes else [{}]}


def execution(record: dict | None) -> str:
    if record is None:
        return "absent"
    status = record.get("status")
    if status in ("queued", "pending", "waiting", "in_progress", "requested"):
        return "pending"
    if status == "completed" and record.get("conclusion") in (
        "skipped", "cancelled", "success", "failure", "timed_out", "neutral",
    ):
        return record["conclusion"]
    return "unknown"


def artifact_identity(expected: dict, actual: dict) -> str:
    for key in ("principal", "repository", "run", "attempt", "job", "artifact_id", "digest"):
        if not expected.get(key) or expected[key] != actual.get(key):
            return "ARTIFACT_" + key.upper()
    return "MATCH"


def artifact_inventory(root: Path) -> list[dict]:
    policy = json.loads(POLICY.read_text())
    result = []
    for path in sorted((*root.glob("*.yml"), *root.glob("*.yaml"))):
        raw = path.read_text()
        doc, events = workflow(raw)
        local = []
        for job, data in doc["jobs"].items():
            for index, step in enumerate(data.get("steps", []), 1):
                action = step.get("uses", "")
                if not action.startswith(("actions/upload-artifact@", "actions/download-artifact@")):
                    continue
                kind = "upload" if "/upload-" in action else "download"
                spec = policy["actions"][kind]
                options = step.get("with", {})
                reviewed = action in (spec["tag"], spec["revision"])
                effective = spec["defaults"] | options if reviewed else None
                if kind == "upload" and effective is not None:
                    patterns = effective.get("path", "").splitlines()
                    inclusion = {
                        "include": [line for line in patterns if line and not line.startswith("!")],
                        "exclude": [line[1:] for line in patterns if line.startswith("!")],
                        "filesystem_match": "unresolved candidate workspace and action glob root",
                    }
                else:
                    inclusion = None
                local.append(dict(
                    workflow=path.name, job=job, step=index, kind=kind,
                    action=action, reviewed_revision=spec["revision"] if reviewed else None,
                    declared=options, effective=effective, inclusion=inclusion,
                    job_if=data.get("if"), step_if=step.get("if"), needs=data.get("needs", []),
                    variants=variants(data.get("strategy", {}).get("matrix")),
                    definition_authority={e: policy_for_document(doc, events, job, e, "reviewed-exact") for e in events},
                    runtime_provenance="unresolved",
                ))
        for row in local:
            if row["kind"] == "download":
                expand_download(row, local)
        result.extend(local)
    return result


def expand_download(row: dict, local: list[dict]) -> None:
    row["possible_producers"] = []
    row["unresolved"] = ["provider artifact ID, digest, producer job/attempt and effective principal"]
    options = row["effective"]
    if options is None:
        row["unresolved"].append("unreviewed action revision")
        return
    token = options.get("github-token")
    run = options.get("run-id")
    repository = options.get("repository")
    path = options["path"]
    row["authentication"] = (
        "same-run service" if not token else
        "job token; scope unverified" if token in ("${{ github.token }}", "${{ secrets.GITHUB_TOKEN }}")
        else "unknown supplied principal"
    )
    row["extraction"] = {
        "path": path,
        "merge_multiple": options["merge-multiple"],
        "layout": "explicit single artifact at path; multiple artifacts in named directories unless merged",
    }
    same_repo = repository == "${{ github.repository }}"
    same_run = not token or run == "${{ github.run_id }}"
    if token and not same_repo:
        row["unresolved"].append("external or unresolved repository selector")
        return
    conditional = run == "${{ inputs.mode == 'cleanup' && inputs.original_run_id || github.run_id }}"
    if not same_run:
        row["unresolved"].append("historical or unresolved run selector")
        if not conditional:
            return
    name, pattern, ids = (options.get(key) for key in ("name", "pattern", "artifact-ids"))
    if ids:
        row["unresolved"].append("artifact IDs require provider evidence")
        return
    if not name and pattern and not re.fullmatch(r"[A-Za-z0-9_.-]+\*", pattern):
        row["unresolved"].append("unreviewed glob semantics; producer list is partial")
        return
    for upload in local:
        if upload["kind"] != "upload":
            continue
        source = upload["effective"]
        upload_name = source["name"] if source else "${{ unknown }}"
        symbolic = any("${{" in val for val in (name or "", pattern or "", upload_name))
        if symbolic or (name == upload_name if name else not pattern or fnmatch.fnmatchcase(upload_name, pattern)):
            row["possible_producers"].append({
                "job": upload["job"], "step": upload["step"],
                "arm": "current-run only" if conditional else "current-run",
                "authority": upload["definition_authority"],
            })
    row["unresolved"].append("event, variant, condition and runtime inclusion")
    if len(row["possible_producers"]) > 1:
        row["unresolved"].append("multiple producer candidates; collision or broad selection requires adjudication")


def report(root: Path) -> dict:
    definition_rows = definitions(root)
    workflow_count = len({row["workflow"] for row in definition_rows})
    job_count = len({(row["workflow"], row["job"]) for row in definition_rows})
    matrices = []
    for path in sorted((*root.glob("*.yaml"), *root.glob("*.yml"))):
        doc, _ = workflow(path.read_text())
        for job, value in doc["jobs"].items():
            if "strategy" in value:
                matrices.append({"workflow": path.name, "job": job,
                                 **variants(value["strategy"].get("matrix"))})
    return {"schema": 1, "workflow_count": workflow_count, "job_count": job_count,
            "definitions": definition_rows, "matrix_definitions": matrices,
            "artifact_definitions": artifact_inventory(root)}


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("workflows", type=Path)
    args = parser.parse_args()
    print(json.dumps(report(args.workflows), sort_keys=True, separators=(",", ":")))
