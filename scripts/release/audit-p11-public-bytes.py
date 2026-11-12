#!/usr/bin/env python3
"""P11: check exact *downloaded* public Phase-1 release assets, not API digests alone.

This is an audit of the historical September releases. It does not certify a
November P2/P6/P7 source occurrence, the signed Darwin executable identity,
or the independent final candidate/delta.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import stat
import tarfile
import urllib.request
import zipfile

REPO = "abiggerhammer/phil"
API = "https://api.github.com/repos/" + REPO
EXPECTED = {
    "phil-v0.1.0-phase1": {
        "commit": "a9f2c745686d8ae1b923e21045554f4864956e76",
        "assets": {
            "phil-0.1.0-phase1-aarch64-apple-darwin.zip": ("7946de209f0724ea54bd19376a12e5bfa7497bcfbbc1fa9eef064ec330ade113", 8446689),
            "phil-0.1.0-phase1-aarch64-apple-darwin.zip.notary-info.json": ("f51cdf64bc164fe5fdc5f904193ff337633e5e3b2316fa1b39f7f32eef08872d", 209),
            "phil-0.1.0-phase1-aarch64-apple-darwin.zip.release": ("8618ef0f20760e4cdd0de82985633547f1ab5f29d6ec147073ffae5c4e83e69c", 496),
            "phil-0.1.0-phase1-aarch64-apple-darwin.zip.release.sha256": ("211fad87fc65072bb4f0dc93e4eaaba4af3a76f6f61234d27da29d4fb2fe1e5e", 117),
            "phil-0.1.0-phase1-aarch64-apple-darwin.zip.sha256": ("275d601116720c5c4875b1a243508aa1d981b5173f0511badae933960f2140cf", 109),
            "phil-0.1.0-phase1-x86_64-linux.tar.gz": ("2db589b68cbfb315d97f27e475411e554866031750b0c4f48e41d546a32c3e64", 2441691),
            "phil-0.1.0-phase1-x86_64-linux.tar.gz.release": ("d93fcf54105996b91148e61f8c25dc77e7e9da8959a4b8c72f07326511675de0", 491),
            "phil-0.1.0-phase1-x86_64-linux.tar.gz.release.sha256": ("6a613fd44419188c422f05b3c922e910ebbe570ad10d6b42e0faa27e362d51cd", 112),
            "phil-0.1.0-phase1-x86_64-linux.tar.gz.sha256": ("52b7870a8bf93d6b9489230232f2acae2f1e6ea690fe71b92a2bd1ac52b47758", 104),
            "phil-0.1.0-phase1.release-bundle": ("df4152b2d319be2d78b896c484263ab5e847f9e91800b6879958b2b47b45fd40", 1882),
            "phil-0.1.0-phase1.release-bundle.sha256": ("14fc9ff8e5d6746c3dc5ccfd1b75d916c89366df0d67344436f068efdeed5c0d", 99),
        },
    },
    "steve-v0.1.1-phase1": {
        "commit": "e7421fd1207af70833e6142979bf70d7fba3e8bf",
        "assets": {
            "phil-steve-0.1.1-phase1-aarch64-apple-darwin.zip": ("c823dc792134261c879bb0c2f11eb1e0fb1ee904447f967cee809c35d3841979", 16009681),
            "phil-steve-0.1.1-phase1-aarch64-apple-darwin.zip.sha256": ("049977d91883a0f03343e29186d2e50a869d7923033ab67f4de1b2df6cb283f6", 115),
            "phil-steve-0.1.1-phase1-x86_64-linux.tar.gz": ("eeddcb09f543bb56574b89a577ae93cc0a1a379e003551eb45ae37a6a96bd0e7", 3035720),
            "phil-steve-0.1.1-phase1-x86_64-linux.tar.gz.sha256": ("31ecf8d9aeb90d501d109bdd88696165143b0dc5659b1835c8ae668a3752d21a", 110),
        },
    },
}
TARGETS = {
    "x86_64-linux.tar.gz": "x86_64-unknown-linux-gnu",
    "aarch64-apple-darwin.zip": "aarch64-apple-darwin",
}
STEVE_MEMBERS = {
    "LICENSE", "README.md", "TCB.txt", "SHA256SUMS", "smoke-test.sh",
    "bin/philc", "bin/steve",
    "share/phil-steve/steve.release-package",
    "share/phil-steve/docs/provider-put-get.md",
    "share/phil-steve/source/put.phil",
    "share/phil-steve/source/get.phil",
    "share/phil-steve/source/put-cli.phil",
    "share/phil-steve/source/get-cli.phil",
}
SCRIPT = Path(__file__).with_name("compose-phil-phase1-release-bundle.py")
SPEC = importlib.util.spec_from_file_location("phase1_bundle_for_p11", SCRIPT)
assert SPEC and SPEC.loader
bundle = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(bundle)


class AuditError(ValueError):
    pass


def require(ok: bool, reason: str) -> None:
    if not ok:
        raise AuditError(reason)


def sha_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def request(url: str):
    return urllib.request.urlopen(urllib.request.Request(
        url, headers={"User-Agent": "phil-p11-independent-byte-audit/1",
                      "Accept": "application/vnd.github+json"}), timeout=90)


def get_json(url: str) -> dict:
    with request(url) as response:
        return json.load(response)


def check_metadata(tag: str, release: dict, tag_ref: dict) -> None:
    spec = EXPECTED[tag]
    require(release.get("tag_name") == tag, f"{tag}: release tag changed")
    require(release.get("target_commitish") == spec["commit"], f"{tag}: release target changed")
    require(tag_ref.get("ref") == "refs/tags/" + tag, f"{tag}: tag ref changed")
    require(tag_ref.get("object", {}).get("type") == "commit"
            and tag_ref["object"]["sha"] == spec["commit"], f"{tag}: resolved source commit changed")
    assets = release.get("assets")
    require(isinstance(assets, list), f"{tag}: assets missing")
    names = [a.get("name") for a in assets]
    require(len(names) == len(set(names)) and set(names) == set(spec["assets"]),
            f"{tag}: unexpected/missing/duplicate asset names")
    for asset in assets:
        name = asset["name"]
        expected_hash, size = spec["assets"][name]
        expected_url = f"https://github.com/{REPO}/releases/download/{tag}/{name}"
        require(asset.get("browser_download_url") == expected_url,
                f"{tag}: unexpected browser URL for {name}")
        require(asset.get("size") == size, f"{tag}: metadata size changed for {name}")
        require(asset.get("digest") == "sha256:" + expected_hash,
                f"{tag}: metadata digest changed for {name}")


def download(tag: str, directory: Path) -> None:
    directory.mkdir(parents=True, exist_ok=True)
    for name, (expected, size) in EXPECTED[tag]["assets"].items():
        url = f"https://github.com/{REPO}/releases/download/{tag}/{name}"
        path = directory / name
        temp = directory / (name + ".partial")
        h = hashlib.sha256()
        count = 0
        try:
            with request(url) as response, temp.open("wb") as out:
                for chunk in iter(lambda: response.read(1024 * 1024), b""):
                    count += len(chunk)
                    require(count <= size, f"{tag}/{name}: download too large")
                    h.update(chunk)
                    out.write(chunk)
            require(count == size and h.hexdigest() == expected,
                    f"{tag}/{name}: downloaded bytes differ from pinned metadata baseline")
            temp.replace(path)
        finally:
            temp.unlink(missing_ok=True)
        print(f"PUBLIC_BROWSER_BYTES tag={tag} asset={name} size={count} sha256={h.hexdigest()}", flush=True)


def check_executable_modes(archive: Path) -> None:
    seen: set[str] = set()
    if archive.name.endswith(".tar.gz"):
        with tarfile.open(archive, "r:gz") as tf:
            entries = [(m.name, m.mode, m.isfile()) for m in tf.getmembers()]
    else:
        with zipfile.ZipFile(archive) as zf:
            entries = [(m.filename, (m.external_attr >> 16) & 0xFFFF,
                        not m.is_dir()) for m in zf.infolist()]
    for name, mode, regular in entries:
        path = bundle.canonical_archive_name(name, is_dir=not regular)
        if path.endswith("/bin/steve") or path.endswith("/bin/philc") or path.endswith("/smoke-test.sh"):
            require(regular and (mode & 0o111) != 0,
                    f"{archive.name}: required executable lacks execute mode: {path}")
            seen.add(path.rsplit("/", 1)[1])
    require(seen == {"steve", "philc", "smoke-test.sh"},
            f"{archive.name}: missing required executable members")


def verify_steve_archive(archive: Path, target: str) -> dict:
    try:
        root, tree = bundle.read_archive_tree(archive)
        require(root == archive.name.removesuffix(".tar.gz").removesuffix(".zip"),
                f"{archive.name}: unexpected package root")
        require(set(tree) == STEVE_MEMBERS,
                f"{archive.name}: package member mismatch missing={sorted(STEVE_MEMBERS - set(tree))} extra={sorted(set(tree) - STEVE_MEMBERS)}")
        bundle.verify_package_manifest(archive, tree["SHA256SUMS"])
        check_executable_modes(archive)
    except bundle.BundleError as exc:
        raise AuditError(f"{archive.name}: {exc}") from exc
    release = tree["share/phil-steve/steve.release-package"].decode("utf-8")
    lines = release.splitlines()
    require(lines and lines[0].startswith("package\tid="),
            f"{archive.name}: missing structural package id")
    require(any(x.startswith("manifest\t") for x in lines),
            f"{archive.name}: missing package manifest")
    require(any(x.startswith("llvm\t") and "target-triple=" + target in x for x in lines),
            f"{archive.name}: wrong LLVM target")
    require(not any(x.startswith("verified-origin\t") for x in lines),
            f"{archive.name}: fabricated P7 verified origin in historical structural sidecar")
    tcb = [x for x in lines if x.startswith("tcb\t")]
    require(len(tcb) == 6 and len(set(tcb)) == 6,
            f"{archive.name}: incomplete/duplicate TCB rows")
    require(any("id=target-assumptions" in x for x in tcb),
            f"{archive.name}: target TCB missing")
    tcb_txt = tree["TCB.txt"].decode("utf-8").splitlines()
    require([x for x in tcb_txt if x.startswith("tcb\t")] == tcb,
            f"{archive.name}: TCB.txt differs from machine-readable sidecar")
    return {"target": target, "archive_sha256": sha_file(archive),
            "structural_release_package_sha256":
                hashlib.sha256(tree["share/phil-steve/steve.release-package"]).hexdigest(),
            "tcb_sha256": hashlib.sha256(tree["TCB.txt"]).hexdigest(),
            "source_files": {p: hashlib.sha256(tree[p]).hexdigest()
                             for p in sorted(STEVE_MEMBERS) if p.startswith("share/phil-steve/source/")}}


def verify_steve(directory: Path) -> dict:
    rows = []
    for suffix, target in TARGETS.items():
        name = f"phil-steve-0.1.1-phase1-{suffix}"
        try:
            bundle.verify_checksum_sidecar(directory / (name + ".sha256"), directory / name)
        except bundle.BundleError as exc:
            raise AuditError(str(exc)) from exc
        rows.append(verify_steve_archive(directory / name, target))
    require(rows[0]["source_files"] == rows[1]["source_files"],
            "Steve Linux/Darwin source inputs differ")
    return {"platforms": rows, "provenance": "STRUCTURAL_ONLY; no P7 checked K/I or public executable linkage"}


def verify_snapshot(directory: Path, *, expected=EXPECTED) -> dict:
    verified = {}
    require(set(p.name for p in directory.iterdir() if p.is_dir()) == set(expected),
            "missing/extra release tag directories")
    for tag, spec in expected.items():
        path = directory / tag
        require(path.is_dir(), f"{tag}: missing release directory")
        require(set(x.name for x in path.iterdir()) == set(spec["assets"]),
                f"{tag}: missing, extra or renamed downloaded asset")
        verified[tag] = {"source_commit": spec["commit"], "assets": {}}
        for name, (digest, size) in spec["assets"].items():
            file = path / name
            require(file.is_file() and not file.is_symlink(), f"{tag}/{name}: not an ordinary file")
            actual = sha_file(file)
            require(file.stat().st_size == size and actual == digest,
                    f"{tag}/{name}: independent downloaded SHA256/size mismatch")
            verified[tag]["assets"][name] = {"sha256": actual, "size": size}
        if tag == "phil-v0.1.0-phase1":
            try:
                bundle.verify_existing_release(path, source_commit=spec["commit"],
                                               version="0.1.0-phase1")
            except bundle.BundleError as exc:
                raise AuditError(str(exc)) from exc
            verified[tag]["bundle"] = "reconstructed and byte-exact"
        elif tag == "steve-v0.1.1-phase1":
            verified[tag]["steve"] = verify_steve(path)
    return verified


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--download-dir", type=Path, required=True)
    ap.add_argument("--offline", action="store_true",
                    help="verify previously downloaded bytes, without any network calls")
    ap.add_argument("--evidence", type=Path, required=True)
    args = ap.parse_args()
    if not args.offline:
        for tag in EXPECTED:
            release = get_json(API + "/releases/tags/" + tag)
            tag_ref = get_json(API + "/git/ref/tags/" + tag)
            check_metadata(tag, release, tag_ref)
            download(tag, args.download_dir / tag)
    verified = verify_snapshot(args.download_dir)
    result = {"status": "HISTORICAL_PUBLIC_BYTES_CHECKED" if not args.offline
              else "OFFLINE_SUPPLIED_BYTES_CHECKED",
              "checked_at_utc": datetime.now(timezone.utc).isoformat(),
              "verification": verified,
              "source": "GitHub browser_download_url" if not args.offline else "supplied local files",
              "independent_external_auditor_signoff": "PENDING",
              "november_final_candidate": "UNPINNED",
              "p7_checked_occurrence_provenance": "NOT CLAIMED",
              "phase1_freeze": "NOT YET"}
    args.evidence.parent.mkdir(parents=True, exist_ok=True)
    args.evidence.write_text(json.dumps(result, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    print("P11_HISTORICAL_BYTES_VERIFIED=YES; INDEPENDENT_SIGNOFF=PENDING; FINAL_CANDIDATE=UNPINNED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
