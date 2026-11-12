#!/usr/bin/env python3
"""Offline fail-closed P11 adversarial tests; NOT public-download evidence."""
from __future__ import annotations

import hashlib
import importlib.util
import io
from pathlib import Path
import stat
import tarfile
import tempfile
import zipfile

SCRIPT = Path(__file__).with_name("audit-p11-public-bytes.py")
SPEC = importlib.util.spec_from_file_location("p11_public_bytes", SCRIPT)
assert SPEC and SPEC.loader
p11 = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(p11)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def expect_reject(label: str, action) -> None:
    try:
        action()
    except (p11.AuditError, p11.bundle.BundleError):
        print("PASS: " + label)
        return
    raise AssertionError("accepted malformed " + label)


def files_for(target: str, *, source=b"ordinary source\n") -> dict[str, bytes]:
    tcb = [
        "tcb\tid=" + name + "\tkind=example\tname=stub\trevision=1\tbasis=stub"
        for name in ("compiler-checker", "llvm-toolchain", "runtime",
                     "providers", "external-checkers", "target-assumptions")
    ]
    release = ("package\tid=" + "a" * 64 + "\n"
               + "manifest\tid=" + "b" * 64 + "\n"
               + "llvm\ttarget-triple=" + target + "\n"
               + "\n".join(tcb) + "\n").encode()
    result = {x: b"test fixture\n" for x in p11.STEVE_MEMBERS if x != "SHA256SUMS"}
    result["share/phil-steve/steve.release-package"] = release
    result["TCB.txt"] = ("Phase-1 structural TCB\n" + "\n".join(tcb) + "\n").encode()
    for x in result:
        if x.startswith("share/phil-steve/source/"):
            result[x] = source
    rebuild_manifest(result)
    return result


def rebuild_manifest(files: dict[str, bytes]) -> None:
    files["SHA256SUMS"] = ("".join(
        digest(data) + "  ./" + path + "\n"
        for path, data in sorted(files.items()) if path != "SHA256SUMS"
    )).encode()


def archive_file(path: Path, files: dict[str, bytes], *,
                 bad_mode: bool = False, symlink: bool = False,
                 traversal: bool = False) -> None:
    root = path.name.removesuffix(".tar.gz").removesuffix(".zip")
    if path.name.endswith(".tar.gz"):
        with tarfile.open(path, "w:gz") as tf:
            for name, data in files.items():
                info = tarfile.TarInfo(root + "/" + name)
                info.size = len(data)
                info.mode = 0o644 if bad_mode and name == "bin/steve" else (
                    0o755 if name in {"bin/steve", "bin/philc", "smoke-test.sh"} else 0o644)
                tf.addfile(info, io.BytesIO(data))
            if symlink:
                link = tarfile.TarInfo(root + "/bin/steve")
                link.type = tarfile.SYMTYPE
                link.linkname = "../../outside"
                tf.addfile(link)
            if traversal:
                info = tarfile.TarInfo(root + "/../outside")
                info.size = 1
                tf.addfile(info, io.BytesIO(b"x"))
    else:
        with zipfile.ZipFile(path, "w") as zf:
            for name, data in files.items():
                info = zipfile.ZipInfo(root + "/" + name)
                mode = 0o644 if bad_mode and name == "bin/steve" else (
                    0o755 if name in {"bin/steve", "bin/philc", "smoke-test.sh"} else 0o644)
                info.create_system = 3
                info.external_attr = (stat.S_IFREG | mode) << 16
                zf.writestr(info, data)
            if symlink:
                info = zipfile.ZipInfo(root + "/bin/steve")
                info.create_system = 3
                info.external_attr = (stat.S_IFLNK | 0o777) << 16
                zf.writestr(info, "../outside")
            if traversal:
                zf.writestr(root + "/../outside", b"x")


def steve_controls(tmp: Path) -> None:
    for suffix, target in p11.TARGETS.items():
        name = "phil-steve-0.1.1-phase1-" + suffix
        archive = tmp / name
        normal = files_for(target)
        archive_file(archive, normal)
        assert p11.verify_steve_archive(archive, target)["target"] == target
        print("PASS: synthetic " + suffix + " package accepted")
        bad = dict(normal)
        bad["bin/steve"] = b"corrupt file"
        archive_file(archive, bad)
        expect_reject("changed member checksum " + suffix,
                      lambda: p11.verify_steve_archive(archive, target))
        bad = dict(normal)
        del bad["README.md"]
        rebuild_manifest(bad)
        archive_file(archive, bad)
        expect_reject("missing archive member", lambda: p11.verify_steve_archive(archive, target))
        bad = dict(normal)
        bad["foreign"] = b"foreign"
        rebuild_manifest(bad)
        archive_file(archive, bad)
        expect_reject("extra archive member", lambda: p11.verify_steve_archive(archive, target))
        bad = dict(normal)
        bad["share/phil-steve/steve.release-package"] = bad["share/phil-steve/steve.release-package"].replace(
            target.encode(), b"wrong-target"
        )
        rebuild_manifest(bad)
        archive_file(archive, bad)
        expect_reject("wrong LLVM target", lambda: p11.verify_steve_archive(archive, target))
        bad = dict(normal)
        bad["TCB.txt"] = b"fabricated TCB"
        rebuild_manifest(bad)
        archive_file(archive, bad)
        expect_reject("wrong human TCB copy", lambda: p11.verify_steve_archive(archive, target))
        bad = dict(normal)
        bad["share/phil-steve/steve.release-package"] += b"verified-origin\tinstance-key=fake\n"
        rebuild_manifest(bad)
        archive_file(archive, bad)
        expect_reject("fake P7 origin", lambda: p11.verify_steve_archive(archive, target))
        archive_file(archive, normal, bad_mode=True)
        expect_reject("nonexecutable Steve", lambda: p11.verify_steve_archive(archive, target))
        archive_file(archive, normal, symlink=True)
        expect_reject("symlink replacement", lambda: p11.verify_steve_archive(archive, target))
        archive_file(archive, normal, traversal=True)
        expect_reject("archive traversal", lambda: p11.verify_steve_archive(archive, target))
        archive_file(archive, normal)


def cross_platform_and_sidecars(tmp: Path) -> None:
    directory = tmp / "steve"
    directory.mkdir()
    for suffix, target in p11.TARGETS.items():
        name = "phil-steve-0.1.1-phase1-" + suffix
        archive = directory / name
        archive_file(archive, files_for(target))
        (directory / (name + ".sha256")).write_text(p11.sha_file(archive) + "  " + name + "\n")
    p11.verify_steve(directory)
    print("PASS: synthetic cross-platform Steve sources and sidecars")
    linux = directory / "phil-steve-0.1.1-phase1-x86_64-linux.tar.gz"
    sha = directory / (linux.name + ".sha256")
    sha.write_text("0" * 64 + "  " + linux.name + "\n")
    expect_reject("wrong published archive sidecar", lambda: p11.verify_steve(directory))
    sha.write_text(p11.sha_file(linux) + "  " + linux.name + "\n")
    archive_file(linux, files_for(p11.TARGETS["x86_64-linux.tar.gz"], source=b"different\n"))
    sha.write_text(p11.sha_file(linux) + "  " + linux.name + "\n")
    expect_reject("cross-platform source mismatch", lambda: p11.verify_steve(directory))


def metadata_and_snapshot(tmp: Path) -> None:
    tag = "steve-v0.1.1-phase1"
    spec = p11.EXPECTED[tag]
    assets = [
        {"name": name, "size": size, "digest": "sha256:" + sha,
         "browser_download_url": f"https://github.com/{p11.REPO}/releases/download/{tag}/{name}"}
        for name, (sha, size) in spec["assets"].items()
    ]
    release = {"tag_name": tag, "target_commitish": spec["commit"], "assets": assets}
    tagref = {"ref": "refs/tags/" + tag, "object": {"type": "commit", "sha": spec["commit"]}}
    p11.check_metadata(tag, release, tagref)
    print("PASS: pinned API tag and enumeration metadata")
    expect_reject("wrong source commit", lambda: p11.check_metadata(
        tag, {**release, "target_commitish": "f" * 40}, tagref))
    expect_reject("moved tag", lambda: p11.check_metadata(
        tag, release, {**tagref, "object": {"type": "commit", "sha": "f" * 40}}))
    expect_reject("missing asset", lambda: p11.check_metadata(
        tag, {**release, "assets": assets[:-1]}, tagref))
    expect_reject("wrong notarization/asset digest", lambda: p11.check_metadata(
        tag, {**release, "assets": [{**assets[0], "digest": "sha256:" + "0" * 64}] + assets[1:]}, tagref))
    snap = tmp / "snapshot"
    snap.mkdir()
    (snap / "baseline").mkdir()
    (snap / "baseline" / "archive").write_bytes(b"public bytes")
    expected = {"baseline": {"commit": "a" * 40,
                "assets": {"archive": (digest(b"public bytes"), len(b"public bytes"))}}}
    p11.verify_snapshot(snap, expected=expected)
    (snap / "baseline" / "archive").write_bytes(b"wrong bytes")
    expect_reject("real byte corruption mismatches independent digest",
                  lambda: p11.verify_snapshot(snap, expected=expected))
    (snap / "baseline" / "archive").unlink()
    expect_reject("missing downloaded asset", lambda: p11.verify_snapshot(snap, expected=expected))


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="phil-p11-negative-") as raw:
        tmp = Path(raw)
        steve_controls(tmp)
        cross_platform_and_sidecars(tmp)
        metadata_and_snapshot(tmp)
    print("PASS: P11 synthetic adversarial controls; no public download credited")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
