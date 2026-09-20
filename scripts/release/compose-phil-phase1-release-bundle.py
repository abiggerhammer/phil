#!/usr/bin/env python3
"""Compose and independently verify the final Phase-1 Phil release bundle."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import tarfile
import zipfile

BUNDLE_HEADER = "PHIL-PHASE1-DISTRIBUTION-BUNDLE-V1"
BUNDLE_REVISION = "phase1.int011.distribution-bundle.v1"
RELEASE_HEADER = "PHIL-PHASE1-DISTRIBUTION-RELEASE-V1"
RELEASE_REVISION = "phase1.int011.distribution-release.v1"
ARCHIVE_HEADER = "PHIL-PHASE1-DISTRIBUTION-ARCHIVE-V1"
ARCHIVE_REVISION = "phase1.int011.distribution-archive.v1"
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
COMMIT_RE = re.compile(r"^[0-9a-f]{40}$")

LINUX_TARGET = "x86_64-unknown-linux-gnu"
DARWIN_TARGET = "aarch64-apple-darwin"
REQUIRED_TCB_KINDS = {
    "compiler-checker",
    "build-toolchain",
    "llvm-toolchain",
    "target-assumption",
}
REQUIRED_TCB_IDS = {
    "compiler-checker",
    "build-toolchain",
    "llvm-toolchain",
    "target-assumptions",
}


class BundleError(ValueError):
    pass


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def sha_token(raw_hex: str) -> str:
    if not SHA256_RE.fullmatch(raw_hex):
        raise BundleError(f"invalid SHA-256: {raw_hex!r}")
    return "sha256:" + raw_hex


def parse_sha_token(value: str) -> str:
    prefix = "sha256:"
    if not value.startswith(prefix):
        raise BundleError(f"expected sha256: token, got {value!r}")
    raw = value[len(prefix):]
    if not SHA256_RE.fullmatch(raw):
        raise BundleError(f"invalid SHA-256 token: {value!r}")
    return raw


def unescape(value: str) -> str:
    out: list[str] = []
    i = 0
    while i < len(value):
        ch = value[i]
        if ch != "\\":
            out.append(ch)
            i += 1
            continue
        if i + 1 >= len(value):
            raise BundleError("trailing backslash in escaped field")
        nxt = value[i + 1]
        mapping = {"\\": "\\", "n": "\n", "r": "\r", "t": "\t"}
        if nxt not in mapping:
            raise BundleError(f"unknown escape sequence: \\{nxt}")
        out.append(mapping[nxt])
        i += 2
    return "".join(out)


def escape(value: str) -> str:
    return (
        value.replace("\\", "\\\\")
        .replace("\n", "\\n")
        .replace("\r", "\\r")
        .replace("\t", "\\t")
    )


def parse_record(line: str) -> tuple[str, dict[str, str]]:
    fields = line.split("\t")
    if not fields or not fields[0]:
        raise BundleError(f"invalid record line: {line!r}")
    tag = fields[0]
    values: dict[str, str] = {}
    for field in fields[1:]:
        if "=" not in field:
            raise BundleError(f"invalid record field: {field!r}")
        key, raw = field.split("=", 1)
        if not key or key in values:
            raise BundleError(f"duplicate/blank record key in {line!r}")
        values[key] = unescape(raw)
    return tag, values


def record_line(tag: str, fields: list[tuple[str, str]]) -> str:
    return "\t".join([tag] + [f"{key}={escape(value)}" for key, value in fields])


def canonical_body_and_declared_id(
    text: str,
    *,
    expected_header: str,
    id_tag: str,
    id_key: str,
) -> tuple[str, str, list[tuple[str, dict[str, str]]]]:
    if not text.endswith("\n\n"):
        raise BundleError(f"{expected_header} record must end in exactly the canonical blank line")
    lines = text.splitlines(keepends=True)
    if len(lines) < 4 or lines[0] != expected_header + "\n":
        raise BundleError(f"unexpected record header for {expected_header}")

    id_line = lines[1][:-1]
    tag, fields = parse_record(id_line)
    if tag != id_tag or set(fields) != {id_key}:
        raise BundleError(f"unexpected identity record: {id_line!r}")
    declared = parse_sha_token(fields[id_key])

    # The Haskell renderer wraps an already-newline-terminated canonical body
    # in Text.unlines, producing exactly one extra final blank line.
    body = "".join(lines[2:-1])
    actual = sha256_bytes(body.encode("utf-8"))
    if actual != declared:
        raise BundleError(
            f"{expected_header} canonical identity mismatch: declared {declared}, actual {actual}"
        )

    parsed: list[tuple[str, dict[str, str]]] = []
    for raw in body.splitlines():
        if not raw:
            raise BundleError("blank line inside canonical body")
        parsed.append(parse_record(raw))
    return declared, body, parsed


def singleton(
    records: list[tuple[str, dict[str, str]]],
    tag: str,
) -> dict[str, str]:
    matches = [fields for actual, fields in records if actual == tag]
    if len(matches) != 1:
        raise BundleError(f"expected exactly one {tag!r} record, found {len(matches)}")
    return matches[0]


def parse_release(text: str) -> dict[str, object]:
    release_id, _, records = canonical_body_and_declared_id(
        text,
        expected_header=RELEASE_HEADER,
        id_tag="release",
        id_key="id",
    )
    unknown_tags = {tag for tag, _ in records} - {
        "format", "package", "source", "handoff", "compiler", "tcb"
    }
    if unknown_tags:
        raise BundleError(f"unknown release record tags: {sorted(unknown_tags)}")

    fmt = singleton(records, "format")
    package = singleton(records, "package")
    source = singleton(records, "source")
    handoff = singleton(records, "handoff")
    compiler = singleton(records, "compiler")
    tcb = [fields for tag, fields in records if tag == "tcb"]

    if fmt != {"revision": RELEASE_REVISION}:
        raise BundleError(f"unexpected release format: {fmt!r}")
    if set(package) != {"name", "version", "target"}:
        raise BundleError(f"unexpected package record: {package!r}")
    if set(source) != {"commit"} or not COMMIT_RE.fullmatch(source["commit"]):
        raise BundleError(f"invalid source record: {source!r}")
    if set(handoff) != {"sha256"}:
        raise BundleError(f"invalid handoff record: {handoff!r}")
    if set(compiler) != {"sha256"}:
        raise BundleError(f"invalid compiler record: {compiler!r}")

    handoff_sha = parse_sha_token(handoff["sha256"])
    compiler_sha = parse_sha_token(compiler["sha256"])

    if len(tcb) != 4:
        raise BundleError(f"expected four distribution TCB rows, found {len(tcb)}")
    ids: set[str] = set()
    kinds: set[str] = set()
    for row in tcb:
        if set(row) != {"id", "kind", "name", "revision", "basis"}:
            raise BundleError(f"unexpected TCB row: {row!r}")
        if not all(row.values()):
            raise BundleError(f"blank TCB field: {row!r}")
        if row["id"] in ids:
            raise BundleError(f"duplicate TCB id: {row['id']}")
        ids.add(row["id"])
        kinds.add(row["kind"])
    if ids != REQUIRED_TCB_IDS:
        raise BundleError(f"wrong distribution TCB identity domain: {sorted(ids)}")
    if kinds != REQUIRED_TCB_KINDS:
        raise BundleError(f"wrong distribution TCB kind domain: {sorted(kinds)}")

    return {
        "release_id": release_id,
        "name": package["name"],
        "version": package["version"],
        "target": package["target"],
        "source_commit": source["commit"],
        "handoff_sha256": handoff_sha,
        "compiler_sha256": compiler_sha,
    }


def parse_archive_binding(text: str) -> dict[str, str]:
    binding_id, _, records = canonical_body_and_declared_id(
        text,
        expected_header=ARCHIVE_HEADER,
        id_tag="archive-binding",
        id_key="id",
    )
    unknown_tags = {tag for tag, _ in records} - {
        "format", "release", "archive", "package-manifest"
    }
    if unknown_tags:
        raise BundleError(f"unknown archive-binding record tags: {sorted(unknown_tags)}")

    fmt = singleton(records, "format")
    release = singleton(records, "release")
    archive = singleton(records, "archive")
    package_manifest = singleton(records, "package-manifest")

    if fmt != {"revision": ARCHIVE_REVISION}:
        raise BundleError(f"unexpected archive-binding format: {fmt!r}")
    if set(release) != {"id"}:
        raise BundleError(f"invalid archive release record: {release!r}")
    if set(archive) != {"name", "sha256"}:
        raise BundleError(f"invalid archive record: {archive!r}")
    if set(package_manifest) != {"sha256"}:
        raise BundleError(f"invalid package-manifest record: {package_manifest!r}")

    return {
        "archive_binding_id": binding_id,
        "release_id": parse_sha_token(release["id"]),
        "archive_name": archive["name"],
        "archive_sha256": parse_sha_token(archive["sha256"]),
        "package_manifest_sha256": parse_sha_token(package_manifest["sha256"]),
    }


def verify_checksum_sidecar(sidecar: Path, payload: Path) -> None:
    raw = sidecar.read_text(encoding="utf-8").strip()
    fields = raw.split()
    if len(fields) != 2:
        raise BundleError(f"unexpected checksum sidecar: {sidecar}")
    digest, name = fields
    if name.lstrip("*") != payload.name:
        raise BundleError(f"checksum sidecar names {name!r}, expected {payload.name!r}")
    if digest != sha256_file(payload):
        raise BundleError(f"checksum mismatch for {payload.name}")


def read_archive_files(archive: Path) -> dict[str, bytes]:
    wanted_suffixes = {
        "/share/phil/phil.release-package": "release",
        "/share/phil/phase1-handoff-manifest-v1.tsv": "handoff",
        "/bin/philc": "compiler",
        "/SHA256SUMS": "manifest",
    }
    found: dict[str, bytes] = {}

    def accept(name: str, data: bytes) -> None:
        normalized = "/" + name.lstrip("./")
        for suffix, key in wanted_suffixes.items():
            if normalized.endswith(suffix):
                if key in found:
                    raise BundleError(f"duplicate {key} member in {archive.name}")
                found[key] = data

    if archive.name.endswith(".tar.gz"):
        with tarfile.open(archive, "r:gz") as tf:
            for member in tf.getmembers():
                if not member.isfile():
                    continue
                extracted = tf.extractfile(member)
                if extracted is not None:
                    accept(member.name, extracted.read())
    elif archive.name.endswith(".zip"):
        with zipfile.ZipFile(archive) as zf:
            for info in zf.infolist():
                if info.is_dir():
                    continue
                accept(info.filename, zf.read(info))
    else:
        raise BundleError(f"unsupported release archive: {archive.name}")

    missing = set(wanted_suffixes.values()) - set(found)
    if missing:
        raise BundleError(f"{archive.name} missing package members: {sorted(missing)}")
    return found


def verify_package_manifest(archive: Path, manifest_bytes: bytes) -> None:
    listed: dict[str, str] = {}
    for raw in manifest_bytes.decode("utf-8").splitlines():
        if not raw:
            continue
        parts = raw.split(maxsplit=1)
        if len(parts) != 2 or not SHA256_RE.fullmatch(parts[0]):
            raise BundleError(f"invalid SHA256SUMS row in {archive.name}: {raw!r}")
        path = parts[1].lstrip("*")
        if path.startswith("./"):
            path = path[2:]
        if not path or path in listed:
            raise BundleError(f"duplicate/blank SHA256SUMS path in {archive.name}: {path!r}")
        listed[path] = parts[0]

    actual: dict[str, str] = {}
    if archive.name.endswith(".tar.gz"):
        with tarfile.open(archive, "r:gz") as tf:
            regular = [m for m in tf.getmembers() if m.isfile()]
            roots = {m.name.split("/", 1)[0] for m in regular}
            if len(roots) != 1:
                raise BundleError(f"{archive.name} does not have one package root")
            root = next(iter(roots))
            for member in regular:
                rel = member.name[len(root) + 1 :]
                if rel == "SHA256SUMS":
                    continue
                extracted = tf.extractfile(member)
                if extracted is None:
                    raise BundleError(f"cannot read {member.name}")
                actual[rel] = sha256_bytes(extracted.read())
    else:
        with zipfile.ZipFile(archive) as zf:
            regular = [i for i in zf.infolist() if not i.is_dir()]
            roots = {i.filename.split("/", 1)[0] for i in regular}
            if len(roots) != 1:
                raise BundleError(f"{archive.name} does not have one package root")
            root = next(iter(roots))
            for info in regular:
                rel = info.filename[len(root) + 1 :]
                if rel == "SHA256SUMS":
                    continue
                actual[rel] = sha256_bytes(zf.read(info))

    if actual != listed:
        missing = sorted(set(actual) - set(listed))
        extra = sorted(set(listed) - set(actual))
        drift = sorted(
            path for path in set(actual) & set(listed) if actual[path] != listed[path]
        )
        raise BundleError(
            f"{archive.name} SHA256SUMS mismatch: unlisted={missing}, missing={extra}, drift={drift}"
        )


def platform_record(
    directory: Path,
    archive_name: str,
    expected_target: str,
    source_commit: str,
    version: str,
    *,
    notarization: Path | None = None,
    notary_id_path: Path | None = None,
) -> dict[str, str]:
    archive = directory / archive_name
    archive_sha = directory / f"{archive_name}.sha256"
    binding_file = directory / f"{archive_name}.release"
    binding_sha = directory / f"{archive_name}.release.sha256"

    for path in [archive, archive_sha, binding_file, binding_sha]:
        if not path.is_file():
            raise BundleError(f"missing release input: {path}")

    verify_checksum_sidecar(archive_sha, archive)
    verify_checksum_sidecar(binding_sha, binding_file)

    members = read_archive_files(archive)
    verify_package_manifest(archive, members["manifest"])

    release = parse_release(members["release"].decode("utf-8"))
    binding = parse_archive_binding(binding_file.read_text(encoding="utf-8"))

    if release["name"] != "phil":
        raise BundleError(f"{archive_name} package name is not phil")
    if release["version"] != version:
        raise BundleError(f"{archive_name} version mismatch")
    if release["target"] != expected_target:
        raise BundleError(f"{archive_name} target mismatch")
    if release["source_commit"] != source_commit:
        raise BundleError(f"{archive_name} source commit mismatch")
    if release["compiler_sha256"] != sha256_bytes(members["compiler"]):
        raise BundleError(f"{archive_name} compiler digest mismatch")
    if release["handoff_sha256"] != sha256_bytes(members["handoff"]):
        raise BundleError(f"{archive_name} handoff digest mismatch")

    if binding["release_id"] != release["release_id"]:
        raise BundleError(f"{archive_name} release/archive identity mismatch")
    if binding["archive_name"] != archive.name:
        raise BundleError(f"{archive_name} archive-binding filename mismatch")
    if binding["archive_sha256"] != sha256_file(archive):
        raise BundleError(f"{archive_name} archive-binding digest mismatch")
    if binding["package_manifest_sha256"] != sha256_bytes(members["manifest"]):
        raise BundleError(f"{archive_name} package-manifest digest mismatch")

    result = {
        "target": expected_target,
        "release_id": str(release["release_id"]),
        "compiler_sha256": str(release["compiler_sha256"]),
        "handoff_sha256": str(release["handoff_sha256"]),
        "archive_binding_id": binding["archive_binding_id"],
        "archive_name": archive.name,
        "archive_sha256": binding["archive_sha256"],
        "archive_binding_sha256": sha256_file(binding_file),
        "package_manifest_sha256": binding["package_manifest_sha256"],
        "notarization_id": "none",
        "notarization_status": "not-applicable",
        "notarization_info_sha256": "none",
    }

    if notarization is not None:
        if not notarization.is_file():
            raise BundleError(f"missing notarization info: {notarization}")
        info = json.loads(notarization.read_text(encoding="utf-8"))
        status = info.get("status")
        notary_id = info.get("id")
        if status != "Accepted" or not isinstance(notary_id, str) or not notary_id:
            raise BundleError(f"Darwin notarization not accepted: {info!r}")
        if notary_id_path is not None:
            if not notary_id_path.is_file():
                raise BundleError(f"missing notarization id file: {notary_id_path}")
            if notary_id_path.read_text(encoding="utf-8").strip() != notary_id:
                raise BundleError("notarization ID file does not match Apple info response")
        result.update(
            {
                "notarization_id": notary_id,
                "notarization_status": status,
                "notarization_info_sha256": sha256_file(notarization),
            }
        )

    return result


def render_bundle(
    source_commit: str,
    version: str,
    handoff_sha256: str,
    platforms: list[dict[str, str]],
) -> str:
    body_lines = [
        record_line("format", [("revision", BUNDLE_REVISION)]),
        record_line("package", [("name", "phil"), ("version", version)]),
        record_line("source", [("commit", source_commit)]),
        record_line("handoff", [("sha256", sha_token(handoff_sha256))]),
    ]

    for platform in sorted(platforms, key=lambda row: row["target"]):
        body_lines.append(
            record_line(
                "platform",
                [
                    ("target", platform["target"]),
                    ("release-id", sha_token(platform["release_id"])),
                    ("compiler-sha256", sha_token(platform["compiler_sha256"])),
                    ("archive-binding-id", sha_token(platform["archive_binding_id"])),
                    ("archive-name", platform["archive_name"]),
                    ("archive-sha256", sha_token(platform["archive_sha256"])),
                    (
                        "archive-binding-sha256",
                        sha_token(platform["archive_binding_sha256"]),
                    ),
                    (
                        "package-manifest-sha256",
                        sha_token(platform["package_manifest_sha256"]),
                    ),
                    ("notarization-id", platform["notarization_id"]),
                    ("notarization-status", platform["notarization_status"]),
                    (
                        "notarization-info-sha256",
                        (
                            "none"
                            if platform["notarization_info_sha256"] == "none"
                            else sha_token(platform["notarization_info_sha256"])
                        ),
                    ),
                ],
            )
        )

    body = "\n".join(body_lines) + "\n"
    bundle_id = sha256_bytes(body.encode("utf-8"))
    return (
        BUNDLE_HEADER
        + "\n"
        + record_line("bundle", [("id", sha_token(bundle_id))])
        + "\n"
        + body
        + "\n"
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-commit", required=True)
    parser.add_argument("--version", default="0.1.0-phase1")
    parser.add_argument("--linux-dir", required=True)
    parser.add_argument("--darwin-dir", required=True)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()

    if not COMMIT_RE.fullmatch(args.source_commit):
        raise BundleError(f"invalid source commit: {args.source_commit}")

    linux_dir = Path(args.linux_dir)
    darwin_dir = Path(args.darwin_dir)

    linux_archive = f"phil-{args.version}-x86_64-linux.tar.gz"
    darwin_archive = f"phil-{args.version}-aarch64-apple-darwin.zip"

    linux = platform_record(
        linux_dir,
        linux_archive,
        LINUX_TARGET,
        args.source_commit,
        args.version,
    )
    darwin = platform_record(
        darwin_dir,
        darwin_archive,
        DARWIN_TARGET,
        args.source_commit,
        args.version,
        notarization=darwin_dir / f"{darwin_archive}.notary-info.json",
        notary_id_path=darwin_dir / f"{darwin_archive}.notary-id",
    )

    if linux["handoff_sha256"] != darwin["handoff_sha256"]:
        raise BundleError("Linux and Darwin distributions bind different Phase-1 handoff roots")

    rendered = render_bundle(
        args.source_commit,
        args.version,
        linux["handoff_sha256"],
        [linux, darwin],
    )

    output = Path(args.output)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(rendered, encoding="utf-8")

    print(f"bundle={output}")
    print(f"bundle_sha256={sha256_file(output)}")
    print(f"linux_release_id=sha256:{linux['release_id']}")
    print(f"darwin_release_id=sha256:{darwin['release_id']}")
    print(f"darwin_notarization_id={darwin['notarization_id']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
