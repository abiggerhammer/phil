"""Route the two legacy scope jobs on validated GitHub event identities."""
import argparse
from dataclasses import dataclass
import json
import os
from pathlib import Path
import re
import subprocess
import types

REPOSITORY = (1341890518, "abiggerhammer/phil")
HELPER = "scripts/ci/steveget_scope_routing.py"
TEST = "scripts/ci/test_steveget_scope_routing.py"
DOCUMENT = "docs/phase-1/steveget-scope-routing-v1.md"
SHARED = "phil-core.cabal"


@dataclass(frozen=True)
class Profile:
    family: str
    branch: str
    actor: str
    workflow: str
    paths: frozenset


PROFILES = {
    "fsem05": Profile(
        "fsem-05", "formal-semantics/fsem05-steveget-qualified-source-events",
        "hamster:fsem-05-source", "fsem05-steveget-selected-source-event.yml",
        frozenset({
            "src/Phil/Surface/SelectedSteveGetExecution.hs", SHARED,
            "test/FSEM05SteveGetSelectedSourceEventMain.hs",
            "proof/Phil/Verification/FSEM05SteveGetSelectedSourceEvents.v",
            "docs/phase-1/fsem05-steveget-qualified-source-event-v1.md",
            ".github/workflows/fsem05-steveget-selected-source-event.yml",
        }),
    ),
    "fsem06": Profile(
        "fsem-06", "formal-semantics/fsem06-steveget-core-payload-refinement",
        "hamster:fsem-06-core", "fsem06-steveget-core-payload-refinement.yml",
        frozenset({
            "src/Phil/Compiler/SelectedSteveGetCoreExecution.hs",
            "test/FSEM06SteveGetSelectedCorePayloadMain.hs",
            "proof/Phil/Verification/FSEM06SteveGetSelectedCorePayloadRefinement.v",
            "docs/phase-1/fsem06-steveget-core-payload-execution-v1.md",
            ".github/workflows/fsem06-steveget-core-payload-refinement.yml",
        }),
    ),
}
DIRECT = frozenset().union(*(p.paths for p in PROFILES.values()), {HELPER, TEST, DOCUMENT}) - {SHARED}
NA = ("historical scope NOT APPLICABLE; historical predicate and claim not evaluated; "
      "no changed-file authorization or claim ownership supplied")


class Refusal(Exception):
    """An identity, comparison, scope or claim check failed."""


def require(condition, reason):
    if not condition:
        raise Refusal(reason)


def run_git(*args):
    env = os.environ.copy()
    env.pop("GH_TOKEN", None)
    env.pop("GITHUB_TOKEN", None)
    return subprocess.run(["git", "--no-replace-objects", *args], check=False, env=env,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def git(*args):
    result = run_git(*args)
    require(result.returncode == 0,
            f"Git {args[0]} failed: {result.stderr.decode(errors='replace').strip()}")
    return result.stdout


def sha(value, name):
    require(isinstance(value, str) and re.fullmatch("[a-f0-9]{40}", value)
            and value != "0" * 40, f"invalid {name} SHA")
    return value


def fields(value, name):
    require(isinstance(value, dict), f"missing or invalid {name} object")
    return value


def identity(value, name):
    repo = fields(value, name)
    number, full_name = repo.get("id"), repo.get("full_name")
    require(type(number) is int and number > 0 and isinstance(full_name, str)
            and re.fullmatch(r"[A-Za-z0-9]+(?:-[A-Za-z0-9]+)*/[A-Za-z0-9_.-]+", full_name)
            and full_name.split("/")[1] not in {".", ".."},
            f"invalid {name} identity")
    require((number == REPOSITORY[0]) == (full_name.casefold() == REPOSITORY[1])
            and (number != REPOSITORY[0] or full_name == REPOSITORY[1]),
            f"contradictory {name} identity")
    return number, full_name


def branch(value, name):
    require(isinstance(value, str) and value and not value.startswith("-"),
            f"invalid {name} branch")
    git("check-ref-format", f"refs/heads/{value}")
    return value


def commit(value):
    require(git("cat-file", "-t", value) == b"commit\n", f"{value} is not a commit")


def main_baseline():
    url = git("remote", "get-url", "origin").decode().rstrip("\n")
    require(url in {"https://github.com/abiggerhammer/phil",
                    "https://github.com/abiggerhammer/phil.git"}, "untrusted origin URL")
    rows = git("ls-remote", "--exit-code", "--refs", "origin", "refs/heads/main").splitlines()
    require(len(rows) == 1, "origin main lookup did not return exactly one ref")
    columns = rows[0].decode().split("\t")
    require(len(columns) == 2 and columns[1] == "refs/heads/main", "invalid origin main reply")
    base = sha(columns[0], "origin main")
    if run_git("cat-file", "-e", base).returncode:
        git("fetch", "--no-tags", "origin", base)
    return base


def event_comparison(profile, event, env, evidence):
    kind, ref = env.get("GITHUB_EVENT_NAME"), env.get("GITHUB_REF")
    evidence.update(event=kind, ref=ref)
    subject = sha(env.get("GITHUB_SHA"), "event subject")
    workflow_sha = sha(env.get("GITHUB_WORKFLOW_SHA"), "workflow")
    workflow_ref = env.get("GITHUB_WORKFLOW_REF")
    prefix = f"{REPOSITORY[1]}/.github/workflows/{profile.workflow}@refs/"
    require(isinstance(workflow_ref, str) and workflow_ref.startswith(prefix),
            "invalid workflow ref")
    git("check-ref-format", "refs/" + workflow_ref[len(prefix):])
    evidence.update(subject=subject, workflow_sha=workflow_sha, workflow_ref=workflow_ref)
    require(env.get("GITHUB_REPOSITORY_ID") == str(REPOSITORY[0])
            and env.get("GITHUB_REPOSITORY") == REPOSITORY[1]
            and identity(event.get("repository"), "event repository") == REPOSITORY,
            "unexpected event or runner repository")
    require(git("rev-parse", "HEAD").decode().rstrip("\n") == subject,
            "checkout HEAD disagrees with GITHUB_SHA")
    commit(subject)
    require(git("rev-parse", "--is-shallow-repository") == b"false\n", "shallow checkout")
    evidence["repository"] = REPOSITORY

    if kind == "pull_request":
        require(event.get("action") in {"opened", "synchronize", "reopened"},
                "unsupported PR action")
        pr = fields(event.get("pull_request"), "pull_request")
        number = event.get("number")
        require(type(number) is int and number > 0 and type(pr.get("number")) is int
                and pr["number"] == number and pr.get("state") == "open",
                "invalid PR number or state")
        require(ref == f"refs/pull/{number}/merge", "invalid PR merge ref")
        base = fields(pr.get("base"), "PR base")
        head = fields(pr.get("head"), "PR head")
        base_repo = identity(base.get("repo"), "base repository")
        head_repo = identity(head.get("repo"), "head repository")
        base_ref = branch(base.get("ref"), "base")
        head_ref = branch(head.get("ref"), "head")
        evidence.update(pr=number, base_repo=base_repo, head_repo=head_repo,
                        base_ref=base_ref, head_ref=head_ref)
        require(base_repo == REPOSITORY and env.get("GITHUB_BASE_REF") == base_ref
                and env.get("GITHUB_HEAD_REF") == head_ref, "PR base repository or ref mismatch")
        base_sha = sha(base.get("sha"), "PR base")
        head_sha = sha(head.get("sha"), "PR head")
        evidence.update(base=base_sha, head=head_sha)
        headers = git("cat-file", "commit", subject).partition(b"\n\n")[0]
        parents = [line for line in headers.split(b"\n") if line.startswith(b"parent ")]
        expected = [f"parent {value}".encode() for value in (base_sha, head_sha)]
        require(base_sha != head_sha and parents == expected,
                "synthetic merge parents disagree with event base and head")
        applicable = head_ref == profile.branch
        require(not applicable or (head_repo == REPOSITORY and base_ref == "main"),
                "historical PR requires same-repository head and main base")
        return applicable, base_sha, head_sha

    require(kind == "push", "unsupported event")
    require(event.get("deleted") is False, "deleted or malformed push")
    require(ref == event.get("ref") == f"refs/heads/{profile.branch}"
            and env.get("GITHUB_BASE_REF") in (None, "") and env.get("GITHUB_HEAD_REF") in (None, ""),
            "push ref is not the exact historical branch")
    head_sha = sha(event.get("after"), "push after")
    require(head_sha == subject, "push after disagrees with GITHUB_SHA")
    evidence.update(base_ref="refs/heads/main", head_ref=ref, head=head_sha)
    base_sha = main_baseline()
    evidence["base"] = base_sha
    return True, base_sha, head_sha


def nul_fields(raw):
    if not raw:
        return []
    require(raw.endswith(b"\0"), "unterminated Git path record")
    items = raw[:-1].split(b"\0")
    require(all(items), "empty Git path or status")
    return [os.fsdecode(item) for item in items]


def status_paths(base, head, *, no_renames=False):
    flags = ["--no-renames"] if no_renames else []
    items = iter(nul_fields(git("diff", "--name-status", "-z", *flags, base, head, "--")))
    records = []
    for status in items:
        require(re.fullmatch(r"(?:[ADMTUXB]|[RC][0-9]{1,3}|M[0-9]{1,3})", status),
                "malformed Git diff status")
        scored = len(status) > 1
        require(not scored or int(status[1:]) <= 100, "invalid Git diff score")
        path = next(items, None)
        require(path is not None, "missing Git diff path")
        paths = [path]
        if status[0] in "RC":
            require(not no_renames, "unexpected rename or copy after --no-renames")
            target = next(items, None)
            require(target is not None, "missing Git diff destination")
            paths.append(target)
        records.append((status, paths))
    return records


def enforce_paths(profile, base, head, changes, evidence):
    if profile.family == "fsem-05":
        paths = nul_fields(git("diff", "--name-only", "-z", base, head, "--"))
        evidence["predicate_paths"] = paths
        require(bool(paths) and set(paths) <= profile.paths,
                "FSEM-05 requires a nonempty subset of the historical allowlist")
    else:
        paths = [paths[0] for status, paths in changes if status == "A"]
        require(len(changes) == len(paths) == len(profile.paths)
                and set(paths) == profile.paths, "FSEM-06 requires five unique exact additions")


def verify_claim(profile, base, token):
    path = "scripts/fsem_claim.py"
    controller = types.ModuleType("trusted_fsem_claim")
    exec(compile(git("show", f"{base}:{path}"), f"{base}:{path}", "exec"),
         controller.__dict__)
    require(bool(token), "historical claim lookup requires GH_TOKEN")
    class ReadOnlyGitHub(controller.GitHub):
        claim_sha = None

        def request(self, method, endpoint, payload=None):
            require(method == "GET" and payload is None, "claim controller attempted a write")
            result = super().request(method, endpoint)
            if endpoint == f"/git/ref/heads/coord/fsem-claims/{profile.family}":
                require(isinstance(result, dict)
                        and result.get("ref") == f"refs/heads/coord/fsem-claims/{profile.family}"
                        and isinstance(result.get("object"), dict)
                        and result["object"].get("type") == "commit",
                        "unexpected live claim ref identity")
            return result

        def pages(self, endpoint):
            for comment in super().pages(endpoint):
                body = fields(comment, "issue comment").get("body")
                require(body is None or isinstance(body, str), "invalid issue comment body")
                if body and body.startswith(controller.RELEASE_MARKER):
                    require(f"`{self.claim_sha}`" not in body, "historical claim has been released")
                yield comment

    try:
        api = ReadOnlyGitHub(token=token)
        record, claim_sha = controller.live_claim(api, profile.family)
        api.claim_sha = sha(claim_sha, "live claim")
        require(record["slice"] == profile.family and record["branch"] == profile.branch
                and record["actor"] == profile.actor, "wrong historical claim family, branch or actor")
        controller.require_issue_record(api, record, claim_sha)
    except controller.ClaimFailure as exc:
        raise Refusal(str(exc)) from exc
    return claim_sha


def unique_object(pairs):
    result = {}
    for name, value in pairs:
        require(name not in result, f"duplicate event JSON field {name!r}")
        result[name] = value
    return result


def invalid_constant(value):
    raise Refusal(f"invalid event JSON constant {value}")


def run(profile_key, env, output=print):
    profile = PROFILES[profile_key]
    evidence = {"profile": profile_key}
    try:
        event_path = env.get("GITHUB_EVENT_PATH")
        require(bool(event_path), "missing GITHUB_EVENT_PATH")
        event = fields(json.loads(Path(event_path).read_bytes(),
                                  object_pairs_hook=unique_object,
                                  parse_constant=invalid_constant), "event")
        applicable, base, head = event_comparison(profile, event, env, evidence)
        commit(base)
        commit(head)
        bases = git("merge-base", "--all", base, head).decode().splitlines()
        require(len(bases) == 1, "comparison requires exactly one merge base")
        merge_base = sha(bases[0], "merge base")
        commit(merge_base)
        changes = status_paths(merge_base, head, no_renames=not applicable)
        evidence.update(merge_base=merge_base, changes=changes)
        if applicable:
            enforce_paths(profile, merge_base, head, changes, evidence)
            evidence["claim_sha"] = verify_claim(profile, base, env.get("GH_TOKEN"))
            evidence.update(route="APPLICABLE", diagnostic="historical paths and exact live claim passed")
        else:
            direct = DIRECT.intersection(path for _, paths in changes for path in paths)
            evidence.update(route="N/A", diagnostic=NA)
            if direct:
                evidence.update(classification="owner-review-required", direct_paths=sorted(direct))
    except (Refusal, OSError, ValueError, KeyError, TypeError, AttributeError,
            SyntaxError, RecursionError) as exc:
        diagnostic = str(exc)
        token = env.get("GH_TOKEN")
        if token:
            diagnostic = diagnostic.replace(token, "[redacted]")
        evidence.update(route="REFUSE", diagnostic=diagnostic)
        output(json.dumps(evidence, sort_keys=True))
        return 1
    output(json.dumps(evidence, sort_keys=True))
    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("profile", choices=PROFILES)
    raise SystemExit(run(parser.parse_args().profile, os.environ))
