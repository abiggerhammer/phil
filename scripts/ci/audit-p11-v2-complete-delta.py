#!/usr/bin/env python3
"""P11 audit-only, untruncated historical-source to fixed-checkpoint inventory.

No release, tag, signing, or origin-certificate operation is performed.
"""
import argparse
import hashlib
import json
import pathlib
import subprocess
import sys

PIN = "9c7d48bc7c5f85b241df9343136c104c3af7a22b"
TREE = "575abbe2f916c37775e7baba9a35a8235ca0b6da"
PARENTS = ["3d01a717dac361aba0b0eacd4bde1058b9793937", "b90d1c1a2ca54d110200a4129dc55ff08cd8a755"]
BASES = {
    "phil": "a9f2c745686d8ae1b923e21045554f4864956e76",
    "steve": "e7421fd1207af70833e6142979bf70d7fba3e8bf",
    "rejected-checkpoint": "13808408f9de0f67cefd6fa744f87d81a2d22fbb",
}


def git(repo, *args):
    return subprocess.check_output(["git", "-C", str(repo), *args])


def identity(actual_commit, actual_tree, actual_parents):
    if (actual_commit, actual_tree, actual_parents) != (PIN, TREE, PARENTS):
        raise ValueError("P11 provisional checkpoint commit/tree/parent mismatch")


def snapshot(repo):
    commit = git(repo, "rev-parse", "HEAD").decode().strip()
    tree = git(repo, "rev-parse", "HEAD^{tree}").decode().strip()
    parents = git(repo, "rev-list", "--parents", "-n", "1", "HEAD").decode().strip().split()[1:]
    identity(commit, tree, parents)
    for tag, base in BASES.items():
        if git(repo, "cat-file", "-t", base).strip() != b"commit":
            raise ValueError("invalid historical base: " + tag)
        if subprocess.run(["git", "-C", str(repo), "merge-base", "--is-ancestor", base, PIN]).returncode:
            raise ValueError("historical base is not ancestor: " + tag)
    return {"commit": commit, "tree": tree, "parents": parents}


def classify(path):
    labels = []
    if path.startswith(("src/Phil/Verification/", "src/Phil/Handoff/", "runtime/",
                        "src/Phil/Runtime/")) or path in ("phil-core.cabal", "cabal.project", "cabal.project.ci"):
        labels.append("TCB-or-native-assurance")
    if path.startswith(("audit/", "handoff/", "src/Phil/Verification/",
                        "src/Phil/Handoff/")):
        labels.append("assurance-or-audit")
    if path.endswith(".v") or path.startswith(("rocq/", "proofs/", "theories/")):
        labels.append("Rocq-representation-or-proof")
    if path.startswith("scripts/release/") or path.startswith(".github/workflows/") and any(
        word in path for word in ("release", "int011", "p11")
    ):
        labels.append("release-pipeline")
    if path.startswith(".github/workflows/") or path.startswith("scripts/ci/"):
        labels.append("CI-or-toolchain")
    if path.startswith(("src/Phil/Compiler/", "src/Phil/Systems/")):
        labels.append("native-compiler-or-systems")
    return labels or ["other"]


def entries(raw):
    if not raw or raw[-1:] != b"\0":
        raise ValueError("empty or unterminated complete NUL diff")
    fields = raw[:-1].split(b"\0")
    i = 0
    result = []
    while i < len(fields):
        status = fields[i].decode("ascii")
        i += 1
        if not status or status[0] not in "ACDMRTUXB":
            raise ValueError("unexpected git diff status: " + status)
        npaths = 2 if status.startswith(("R", "C")) else 1
        if i + npaths > len(fields):
            raise ValueError("truncated git diff status")
        names = [x.decode("utf-8", "surrogateescape") for x in fields[i:i+npaths]]
        i += npaths
        if any(not name for name in names):
            raise ValueError("empty diff path")
        result.append({"status": status, "paths": names,
                       "review_classes": sorted(set(label for name in names for label in classify(name)))})
    return result


def sha_file(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def run_delta(repo, out):
    out.mkdir(parents=True, exist_ok=True)
    pin = snapshot(repo)
    summary = {
        "purpose": "P11 complete pinned source-review delta; no released-byte or independent signoff",
        "checkpoint": pin,
        "historical_sources": BASES,
        "git_version": git(repo, "--version").decode().strip(),
        "comparisons": {},
    }
    for name, base in BASES.items():
        stem = name + "-to-p11-review-v2"
        raw = git(repo, "diff", "--no-ext-diff", "--no-textconv",
                  "--find-renames=50%", "--name-status", "-z", base, PIN)
        change_rows = entries(raw)
        raw_path = out / (stem + ".name-status.z")
        raw_path.write_bytes(raw)
        readable = out / (stem + ".paths.jsonl")
        with readable.open("w", encoding="ascii", newline="\n") as fh:
            for row in change_rows:
                fh.write(json.dumps(row, sort_keys=True, ensure_ascii=True, separators=(",", ":")) + "\n")
        patch = out / (stem + ".full-binary.patch")
        with patch.open("wb") as fh:
            subprocess.run(["git", "-C", str(repo), "diff", "--no-ext-diff", "--no-textconv",
                            "--binary", "--full-index", base, PIN], stdout=fh, check=True)
        commit_list = out / (stem + ".commits.txt")
        with commit_list.open("wb") as fh:
            subprocess.run(["git", "-C", str(repo), "log", "--reverse",
                            "--format=%H %P %s", base + ".." + PIN],
                           stdout=fh, check=True)
        counts = {}
        for row in change_rows:
            for category in row["review_classes"]:
                counts[category] = counts.get(category, 0) + 1
        summary["comparisons"][name] = {
            "base": base, "checkpoint": PIN,
            "commands": [
                "git diff --no-ext-diff --no-textconv --find-renames=50% --name-status -z " + base + " " + PIN,
                "git diff --no-ext-diff --no-textconv --binary --full-index " + base + " " + PIN,
                "git log --reverse --format='%H %P %s' " + base + ".." + PIN,
            ],
            "commit_count": int(git(repo, "rev-list", "--count", base + ".." + PIN).strip()),
            "changed_records": len(change_rows),
            "classification_counts_nonexclusive": counts,
            "files": {
                p.name: {"size": p.stat().st_size, "sha256": sha_file(p)}
                for p in (raw_path, readable, patch, commit_list)
            },
        }
    output = out / "p11-v2-complete-delta-summary.json"
    output.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print("P11_V2_CHECKPOINT=" + PIN)
    print("P11_V2_TREE=" + TREE)
    print("P11_V2_PARENTS=" + " ".join(PARENTS))
    for name, record in summary["comparisons"].items():
        print("P11_V2_DELTA=%s commits=%d paths=%d inventory_sha256=%s" %
              (name, record["commit_count"], record["changed_records"],
               record["files"][name + "-to-p11-review-v2.name-status.z"]["sha256"]))
    print("P11_V2_DELTA_SUMMARY_SHA256=" + sha_file(output))
    print("P11_FINAL_RELEASE_BYTES=ABSENT; INDEPENDENT_SIGNOFF=PENDING")


def test():
    identity(PIN, TREE, PARENTS)
    for bad in ((BASES["phil"], TREE, PARENTS), (PIN, BASES["steve"], PARENTS),
                (PIN, TREE, []), (PIN, TREE, list(reversed(PARENTS)))):
        try:
            identity(*bad)
        except ValueError:
            pass
        else:
            raise AssertionError("inadequate snapshot rejection")
    assert entries(b"M\0a/b\0R100\0old\0new\0")[1]["paths"] == ["old", "new"]
    for bad in (b"", b"M\0x", b"R100\0x\0"):
        try:
            entries(bad)
        except ValueError:
            pass
        else:
            raise AssertionError("truncated inventory accepted")
    assert "release-pipeline" in classify("scripts/release/old.sh")
    assert "Rocq-representation-or-proof" in classify("rocq/Test.v")
    print("P11_V2_DELTA_NEGATIVE_CONTROLS=PASS")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--repo", type=pathlib.Path)
    parser.add_argument("--out", type=pathlib.Path)
    args = parser.parse_args()
    try:
        if args.self_test:
            test()
        else:
            if args.repo is None or args.out is None:
                parser.error("--repo and --out are required")
            run_delta(args.repo.resolve(), args.out.resolve())
    except (ValueError, subprocess.CalledProcessError) as exc:
        sys.exit("P11_CHECKPOINT_REJECTED: " + str(exc))


if __name__ == "__main__":
    main()
