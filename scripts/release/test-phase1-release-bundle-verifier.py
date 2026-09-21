#!/usr/bin/env python3
"""Regression probes for the Phase-1 release archive verifier."""

from __future__ import annotations

import importlib.util
import io
from pathlib import Path
import stat
import tarfile
import tempfile
import zipfile

SCRIPT = Path(__file__).with_name("compose-phil-phase1-release-bundle.py")
SPEC = importlib.util.spec_from_file_location("phase1_release_bundle", SCRIPT)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load {SCRIPT}")
bundle = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(bundle)


def expect_error(label: str, action, needle: str) -> None:
    try:
        action()
    except bundle.BundleError as exc:
        detail = str(exc)
        if needle not in detail:
            raise AssertionError(f"{label}: wrong error: {detail}") from exc
        print(f"PASS: {label}")
        return
    raise AssertionError(f"{label}: verifier accepted malformed archive")


def add_tar_file(
    tf: tarfile.TarFile,
    name: str,
    data: bytes,
    *,
    mode: int = 0o644,
) -> None:
    info = tarfile.TarInfo(name)
    info.size = len(data)
    info.mode = mode
    tf.addfile(info, io.BytesIO(data))


def make_baseline_tar(path: Path) -> None:
    with tarfile.open(path, "w:gz") as tf:
        root = tarfile.TarInfo("pkg")
        root.type = tarfile.DIRTYPE
        root.mode = 0o755
        tf.addfile(root)
        bin_dir = tarfile.TarInfo("pkg/bin")
        bin_dir.type = tarfile.DIRTYPE
        bin_dir.mode = 0o755
        tf.addfile(bin_dir)
        add_tar_file(tf, "pkg/README.md", b"readme\n")
        add_tar_file(tf, "pkg/bin/philc", b"compiler\n", mode=0o755)


def baseline_accepts(tmp: Path) -> None:
    archive = tmp / "baseline.tar.gz"
    make_baseline_tar(archive)
    root, tree = bundle.read_archive_tree(archive)
    assert root == "pkg"
    assert tree == {
        "README.md": b"readme\n",
        "bin/philc": b"compiler\n",
    }
    print("PASS: baseline regular tar tree accepts")


def non_executable_compiler_rejects(tmp: Path) -> None:
    archive = tmp / "non-executable.tar.gz"
    with tarfile.open(archive, "w:gz") as tf:
        add_tar_file(tf, "pkg/bin/philc", b"compiler\n", mode=0o644)
    expect_error(
        "non-executable compiler member rejects",
        lambda: bundle.read_archive_tree(archive),
        "compiler member is not executable",
    )


def hardlink_replacement_rejects(tmp: Path) -> None:
    archive = tmp / "hardlink.tar.gz"
    with tarfile.open(archive, "w:gz") as tf:
        add_tar_file(tf, "pkg/README.md", b"readme\n")
        add_tar_file(tf, "pkg/bin/philc", b"compiler\n", mode=0o755)
        link = tarfile.TarInfo("pkg/bin/philc")
        link.type = tarfile.LNKTYPE
        link.linkname = "pkg/README.md"
        tf.addfile(link)
    expect_error(
        "tar hardlink replacement rejects",
        lambda: bundle.read_archive_tree(archive),
        "unsupported tar member",
    )


def tar_duplicate_regular_rejects(tmp: Path) -> None:
    archive = tmp / "duplicate.tar.gz"
    with tarfile.open(archive, "w:gz") as tf:
        add_tar_file(tf, "pkg/README.md", b"one")
        add_tar_file(tf, "pkg/README.md", b"two")
    expect_error(
        "duplicate canonical tar path rejects",
        lambda: bundle.read_archive_tree(archive),
        "duplicate canonical member",
    )


def tar_traversal_rejects(tmp: Path) -> None:
    archive = tmp / "traversal.tar.gz"
    with tarfile.open(archive, "w:gz") as tf:
        add_tar_file(tf, "pkg/../escape", b"nope")
    expect_error(
        "tar traversal path rejects",
        lambda: bundle.read_archive_tree(archive),
        "non-canonical archive member path",
    )


def zip_symlink_rejects(tmp: Path) -> None:
    archive = tmp / "symlink.zip"
    with zipfile.ZipFile(archive, "w") as zf:
        info = zipfile.ZipInfo("pkg/bin/philc")
        info.create_system = 3
        info.external_attr = (stat.S_IFLNK | 0o777) << 16
        zf.writestr(info, "README.md")
    expect_error(
        "zip symlink rejects",
        lambda: bundle.read_archive_tree(archive),
        "unsupported zip member",
    )


def zip_duplicate_rejects(tmp: Path) -> None:
    archive = tmp / "duplicate.zip"
    with zipfile.ZipFile(archive, "w") as zf:
        zf.writestr("pkg/README.md", b"one")
        zf.writestr("pkg/README.md", b"two")
    expect_error(
        "duplicate canonical zip path rejects",
        lambda: bundle.read_archive_tree(archive),
        "duplicate canonical member",
    )


def zip_traversal_rejects(tmp: Path) -> None:
    archive = tmp / "traversal.zip"
    with zipfile.ZipFile(archive, "w") as zf:
        zf.writestr("pkg/../escape", b"nope")
    expect_error(
        "zip traversal path rejects",
        lambda: bundle.read_archive_tree(archive),
        "non-canonical archive member path",
    )


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="phil-release-verifier-") as raw:
        tmp = Path(raw)
        baseline_accepts(tmp)
        non_executable_compiler_rejects(tmp)
        hardlink_replacement_rejects(tmp)
        tar_duplicate_regular_rejects(tmp)
        tar_traversal_rejects(tmp)
        zip_symlink_rejects(tmp)
        zip_duplicate_rejects(tmp)
        zip_traversal_rejects(tmp)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
