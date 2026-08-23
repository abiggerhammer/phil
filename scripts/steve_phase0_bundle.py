#!/usr/bin/env python3
"""Build and verify deterministic Phil Phase 0 evidence bundles in a Steve CAS.

This is a host-side reference tool for the branch-only Steve architecture sketch.
It is not part of Phil's TCB and does not create proof authority. It only preserves
already content-bound artifacts and a deterministic manifest that names them.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import tempfile
from pathlib import Path
from typing import Any

FORMAT = "phil-steve-phase0-evidence-v1"
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")


class BundleError(RuntimeError):
    pass


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> tuple[str, int]:
    h = hashlib.sha256()
    size = 0
    with path.open("rb") as f:
        while chunk := f.read(1024 * 1024):
            h.update(chunk)
            size += len(chunk)
    return h.hexdigest(), size


def object_path(store: Path, digest: str) -> Path:
    if not SHA256_RE.fullmatch(digest):
        raise BundleError(f"invalid sha256 digest: {digest!r}")
    return store / "objects" / "sha256" / digest[:2] / digest[2:]


def same_file_bytes(left: Path, right: Path) -> bool:
    if left.stat().st_size != right.stat().st_size:
        return False
    with left.open("rb") as a, right.open("rb") as b:
        while True:
            ca = a.read(1024 * 1024)
            cb = b.read(1024 * 1024)
            if ca != cb:
                return False
            if not ca:
                return True


def install_file_if_absent(store: Path, source: Path, digest: str) -> Path:
    """Install source without overwriting an existing object.

    The temporary file is completed first. os.link() then performs the
    install-if-absent transition atomically within the object directory.
    """
    destination = object_path(store, digest)
    destination.parent.mkdir(parents=True, exist_ok=True)

    if destination.exists():
        if not same_file_bytes(source, destination):
            raise BundleError(
                f"digest collision or corrupt existing object for sha256:{digest}"
            )
        return destination

    fd, tmp_name = tempfile.mkstemp(prefix=".steve-", dir=destination.parent)
    tmp = Path(tmp_name)
    try:
        with os.fdopen(fd, "wb") as out, source.open("rb") as src:
            while chunk := src.read(1024 * 1024):
                out.write(chunk)
            out.flush()
            os.fsync(out.fileno())

        try:
            os.link(tmp, destination)
        except FileExistsError:
            if not same_file_bytes(tmp, destination):
                raise BundleError(
                    f"digest collision or concurrent corrupt install for sha256:{digest}"
                )
        return destination
    finally:
        tmp.unlink(missing_ok=True)


def install_bytes_if_absent(store: Path, data: bytes, digest: str) -> Path:
    destination = object_path(store, digest)
    destination.parent.mkdir(parents=True, exist_ok=True)

    if destination.exists():
        if destination.read_bytes() != data:
            raise BundleError(
                f"digest collision or corrupt existing object for sha256:{digest}"
            )
        return destination

    fd, tmp_name = tempfile.mkstemp(prefix=".steve-", dir=destination.parent)
    tmp = Path(tmp_name)
    try:
        with os.fdopen(fd, "wb") as out:
            out.write(data)
            out.flush()
            os.fsync(out.fileno())
        try:
            os.link(tmp, destination)
        except FileExistsError:
            if destination.read_bytes() != data:
                raise BundleError(
                    f"digest collision or concurrent corrupt install for sha256:{digest}"
                )
        return destination
    finally:
        tmp.unlink(missing_ok=True)


def load_spec(spec_path: Path) -> dict[str, Any]:
    try:
        spec = json.loads(spec_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise BundleError(f"cannot read spec {spec_path}: {exc}") from exc

    if not isinstance(spec, dict):
        raise BundleError("bundle spec must be a JSON object")
    if set(spec) != {"source_revision", "objects"}:
        raise BundleError("bundle spec keys must be exactly: source_revision, objects")

    revision = spec["source_revision"]
    if not isinstance(revision, str) or not revision:
        raise BundleError("source_revision must be a non-empty string")

    objects = spec["objects"]
    if not isinstance(objects, list) or not objects:
        raise BundleError("objects must be a non-empty array")

    names: set[str] = set()
    normalized = []
    for index, item in enumerate(objects):
        if not isinstance(item, dict) or set(item) != {"name", "kind", "path"}:
            raise BundleError(
                f"objects[{index}] keys must be exactly: name, kind, path"
            )
        name, kind, path = item["name"], item["kind"], item["path"]
        if not all(isinstance(v, str) and v for v in (name, kind, path)):
            raise BundleError(f"objects[{index}] name/kind/path must be non-empty strings")
        if name in names:
            raise BundleError(f"duplicate object name: {name}")
        names.add(name)
        normalized.append({"name": name, "kind": kind, "path": path})

    return {"source_revision": revision, "objects": normalized}


def canonical_manifest_bytes(manifest: dict[str, Any]) -> bytes:
    return (
        json.dumps(manifest, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        + "\n"
    ).encode("utf-8")


def build_bundle(spec_path: Path, store: Path, root_out: Path | None) -> str:
    spec = load_spec(spec_path)
    spec_dir = spec_path.resolve().parent
    entries = []

    for item in spec["objects"]:
        source = (spec_dir / item["path"]).resolve()
        if not source.is_file():
            raise BundleError(f"object path is not a regular file: {item['path']}")
        digest, size = sha256_file(source)
        install_file_if_absent(store, source, digest)
        entries.append(
            {
                "kind": item["kind"],
                "name": item["name"],
                "sha256": digest,
                "size": size,
            }
        )

    entries.sort(key=lambda entry: entry["name"])
    manifest = {
        "format": FORMAT,
        "objects": entries,
        "phase": "0",
        "source_revision": spec["source_revision"],
    }
    manifest_bytes = canonical_manifest_bytes(manifest)
    root_digest = sha256_bytes(manifest_bytes)
    install_bytes_if_absent(store, manifest_bytes, root_digest)

    if root_out is not None:
        root_out.parent.mkdir(parents=True, exist_ok=True)
        root_out.write_text(f"sha256:{root_digest}\n", encoding="ascii")

    return root_digest


def read_object_checked(store: Path, digest: str, expected_size: int | None = None) -> bytes:
    path = object_path(store, digest)
    if not path.is_file():
        raise BundleError(f"missing object sha256:{digest}")
    data = path.read_bytes()
    actual = sha256_bytes(data)
    if actual != digest:
        raise BundleError(
            f"integrity failure for sha256:{digest}: observed sha256:{actual}"
        )
    if expected_size is not None and len(data) != expected_size:
        raise BundleError(
            f"size mismatch for sha256:{digest}: expected {expected_size}, got {len(data)}"
        )
    return data


def validate_manifest(manifest: Any) -> list[dict[str, Any]]:
    if not isinstance(manifest, dict):
        raise BundleError("root object is not a manifest object")
    if set(manifest) != {"format", "objects", "phase", "source_revision"}:
        raise BundleError("manifest has unexpected keys")
    if manifest["format"] != FORMAT or manifest["phase"] != "0":
        raise BundleError("unsupported manifest format or phase")
    if not isinstance(manifest["source_revision"], str) or not manifest["source_revision"]:
        raise BundleError("manifest source_revision must be non-empty")

    objects = manifest["objects"]
    if not isinstance(objects, list) or not objects:
        raise BundleError("manifest objects must be a non-empty array")

    previous_name = None
    seen: set[str] = set()
    for index, entry in enumerate(objects):
        if not isinstance(entry, dict) or set(entry) != {"kind", "name", "sha256", "size"}:
            raise BundleError(f"manifest objects[{index}] has unexpected shape")
        name, kind, digest, size = (
            entry["name"],
            entry["kind"],
            entry["sha256"],
            entry["size"],
        )
        if not isinstance(name, str) or not name:
            raise BundleError(f"manifest objects[{index}].name must be non-empty")
        if not isinstance(kind, str) or not kind:
            raise BundleError(f"manifest objects[{index}].kind must be non-empty")
        if not isinstance(digest, str) or not SHA256_RE.fullmatch(digest):
            raise BundleError(f"manifest objects[{index}].sha256 is invalid")
        if not isinstance(size, int) or isinstance(size, bool) or size < 0:
            raise BundleError(f"manifest objects[{index}].size is invalid")
        if name in seen:
            raise BundleError(f"duplicate manifest object name: {name}")
        if previous_name is not None and name <= previous_name:
            raise BundleError("manifest objects are not canonically sorted by name")
        seen.add(name)
        previous_name = name
    return objects


def verify_bundle(store: Path, root: str) -> dict[str, Any]:
    if root.startswith("sha256:"):
        root = root[len("sha256:") :]
    if not SHA256_RE.fullmatch(root):
        raise BundleError(f"invalid root digest: {root!r}")

    manifest_bytes = read_object_checked(store, root)
    try:
        manifest = json.loads(manifest_bytes.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise BundleError(f"root object is not valid UTF-8 JSON: {exc}") from exc

    if canonical_manifest_bytes(manifest) != manifest_bytes:
        raise BundleError("root manifest is not in canonical encoding")

    objects = validate_manifest(manifest)
    for entry in objects:
        read_object_checked(store, entry["sha256"], entry["size"])
    return manifest


def command_build(args: argparse.Namespace) -> int:
    digest = build_bundle(
        Path(args.spec),
        Path(args.store),
        Path(args.root_out) if args.root_out else None,
    )
    print(f"sha256:{digest}")
    return 0


def command_verify(args: argparse.Namespace) -> int:
    manifest = verify_bundle(Path(args.store), args.root)
    print(
        f"verified {len(manifest['objects'])} objects for "
        f"{manifest['format']} at {args.root}"
    )
    return 0


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    build = sub.add_parser("build", help="build a deterministic evidence bundle")
    build.add_argument("--spec", required=True)
    build.add_argument("--store", required=True)
    build.add_argument("--root-out")
    build.set_defaults(func=command_build)

    verify = sub.add_parser("verify", help="verify a bundle root and all reachable objects")
    verify.add_argument("--store", required=True)
    verify.add_argument("--root", required=True)
    verify.set_defaults(func=command_verify)
    return parser


def main() -> int:
    args = make_parser().parse_args()
    try:
        return args.func(args)
    except BundleError as exc:
        print(f"steve-phase0-bundle: {exc}", file=os.sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
