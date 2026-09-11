#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"

if [[ "$(uname -s)" != "Darwin" || "$(uname -m)" != "arm64" ]]; then
  echo 'build-steve-phase1-darwin-package.sh requires native Apple Silicon macOS' >&2
  exit 1
fi
if ! command -v brew >/dev/null 2>&1; then
  echo 'Homebrew is required to resolve LLVM 18 for the Phase-1 Darwin build' >&2
  exit 1
fi
if ! command -v shasum >/dev/null 2>&1; then
  echo 'shasum is required to build the Phase-1 Darwin package' >&2
  exit 1
fi

output_dir="${1:-dist/releases}"
package_name="phil-steve-0.1.0-phase1-aarch64-apple-darwin"
archive_name="${package_name}.tar.gz"
mkdir -p "$output_dir"
output_dir="$(cd "$output_dir" && pwd)"

work="$(mktemp -d "${TMPDIR:-/tmp}/phil-steve-darwin-package.XXXXXX")"
trap 'rm -rf "$work"' EXIT
stage="$work/$package_name"
mkdir -p "$stage/bin" "$stage/share/phil-steve/source" "$stage/share/phil-steve/docs"

if ! brew list llvm@18 >/dev/null 2>&1; then
  brew install llvm@18
fi
llvm_prefix="$(brew --prefix llvm@18)"
clang="$llvm_prefix/bin/clang"

# Build the ordinary public checker/compiler shipped beside Steve and the
# Haskell substrate needed to materialize the native provider bridge.
cabal build all --enable-tests

llvm="$work/steve-runtime-choice.ll"
object="$work/steve-runtime-choice.o"

# Materialize the canonical Steve runtime-choice implementation under the
# target profile certified for Apple Silicon Darwin.
cabal -v0 exec -- runghc -isrc -itest -Wall -Werror \
  test/Phase1TargetAArch64AppleDarwinMain.hs emit > "$llvm"
"$clang" --target=aarch64-apple-darwin -c "$llvm" -o "$object"

cabal exec -- ghc -isrc -iruntime/phase1 \
  -package directory -package unix \
  -Wall -Werror \
  runtime/phase1/StevePublicMain.hs "$object" \
  -o "$stage/bin/steve"

philc="$(cabal list-bin exe:philc)"
cp "$philc" "$stage/bin/philc"
chmod 0755 "$stage/bin/steve" "$stage/bin/philc"

file "$stage/bin/steve" | grep -q 'Mach-O 64-bit executable arm64'
file "$stage/bin/philc" | grep -q 'Mach-O 64-bit executable arm64'

cabal -v0 exec -- runghc -isrc -itest -Wall -Werror \
  test/Phase1TargetAArch64AppleDarwinReleasePackageMain.hs emit-package \
  > "$stage/share/phil-steve/steve.release-package"

cp examples/steve/put.phil "$stage/share/phil-steve/source/"
cp examples/steve/get.phil "$stage/share/phil-steve/source/"
cp examples/steve/put-cli.phil "$stage/share/phil-steve/source/"
cp examples/steve/get-cli.phil "$stage/share/phil-steve/source/"
cp docs/tutorials/steve-provider-put-get.md \
  "$stage/share/phil-steve/docs/provider-put-get.md"
cp scripts/release/smoke-steve-phase1-package.sh "$stage/smoke-test.sh"
chmod 0755 "$stage/smoke-test.sh"
cp LICENSE "$stage/LICENSE"

{
  echo 'Phil Steve 0.1 Phase-1 trust boundary'
  echo
  echo 'The authoritative machine-readable records are in share/phil-steve/steve.release-package.'
  echo 'The records below are copied verbatim from that certified release package.'
  echo
  grep '^tcb[[:space:]]' "$stage/share/phil-steve/steve.release-package"
} > "$stage/TCB.txt"

cat > "$stage/README.md" <<'EOF'
# Phil Steve 0.1 — Phase 1 Apple Silicon macOS package

This package contains the Phase-1 Steve content-addressed store command, the
ordinary `philc` checker/compiler executable, the canonical Phil Steve source,
and the certified release-package/TCB records for the `aarch64-apple-darwin`
target.

No Phil repository checkout, GHC, Cabal, or LLVM installation is required to
use or smoke-test the unpacked package.

## What is trusted

Read `TCB.txt` before relying on the package. The authoritative machine-readable
copy is `share/phil-steve/steve.release-package`. In Phase 1, the Phil Haskell
compiler/checker remains trusted until Phase 2; the package states that rather
than hiding it. The conventional host runtime, qualified provider realization,
LLVM toolchain, external checkers, and Apple Silicon Darwin target assumptions
are also named there.

## Quick smoke

After unpacking the archive, run:

    ./smoke-test.sh

The smoke verifies every packaged file against `SHA256SUMS`, checks that the
human-readable TCB is an exact copy of the certified TCB records, exercises
`philc`, performs real Steve PUT and GET operations, and verifies that corrupt
CAS content cannot replace an existing output file. Its final lines report the
platform and package evidence digests suitable for an external-use report.

## PUT

Steve paths are relative to the user-filesystem root you select:

    mkdir -p store files
    printf 'hello from Steve\n' > files/input.txt
    content_id="$(printf 'input.txt\n' | bin/steve put "$PWD/store" "$PWD/files")"
    printf '%s\n' "$content_id"

A successful PUT prints the canonical 64-hex SHA-256 content ID. The stored CAS
object is `store/$content_id`.

## GET

GET reads the content ID and destination relative path as two standard-input
lines:

    printf '%s\noutput.txt\n' "$content_id" | \
      bin/steve get "$PWD/store" "$PWD/files"
    cmp files/input.txt files/output.txt

The command runs the compiled Phil `SteveGet` callable through the qualified
provider ABI, then performs the canonical shell's second blob read and digest
check before replacing the destination. Corrupt content therefore does not
replace an existing output file.

## Included material

- `bin/steve` — native Apple Silicon Phase-1 Steve command.
- `bin/philc` — native Apple Silicon ordinary Phil checker/compiler executable.
- `smoke-test.sh` — package-only external-use smoke.
- `share/phil-steve/source/` — canonical `StevePut`, `SteveGet`, and CLI Phil source.
- `share/phil-steve/steve.release-package` — certified machine-readable release/TCB record.
- `share/phil-steve/docs/provider-put-get.md` — provider-path tutorial.
- `SHA256SUMS` — checksums for every packaged file other than the checksum file itself.

This is a Phase-1 package. It intentionally discloses the remaining Haskell and
conventional-runtime TCB rather than presenting the artifact as fully verified.
EOF

(
  cd "$stage"
  find . -type f ! -name SHA256SUMS -print \
    | LC_ALL=C sort \
    | while IFS= read -r path; do
        digest="$(shasum -a 256 "$path" | awk '{print $1}')"
        printf '%s  %s\n' "$digest" "$path"
      done > SHA256SUMS
)

# Create stable tar metadata without depending on GNU tar. Python's standard
# library is part of the build environment only; consumers need only tar/gzip.
epoch="${SOURCE_DATE_EPOCH:-$(git log -1 --format=%ct)}"
archive="$output_dir/$archive_name"
python3 - "$stage" "$archive" "$epoch" <<'PY'
import gzip
import os
import sys
import tarfile

stage, archive, epoch_text = sys.argv[1:]
epoch = int(epoch_text)
parent = os.path.dirname(stage)
package = os.path.basename(stage)
entries = [stage]
for directory, directories, files in os.walk(stage):
    directories.sort()
    files.sort()
    entries.extend(os.path.join(directory, name) for name in directories)
    entries.extend(os.path.join(directory, name) for name in files)

with open(archive, "wb") as raw:
    with gzip.GzipFile(fileobj=raw, mode="wb", mtime=0) as zipped:
        with tarfile.open(fileobj=zipped, mode="w|", format=tarfile.PAX_FORMAT) as tar:
            for path in entries:
                arcname = os.path.relpath(path, parent)
                info = tar.gettarinfo(path, arcname=arcname)
                info.uid = 0
                info.gid = 0
                info.uname = ""
                info.gname = ""
                info.mtime = epoch
                info.pax_headers = {}
                if info.isfile():
                    with open(path, "rb") as source:
                        tar.addfile(info, source)
                else:
                    tar.addfile(info)
PY

(
  cd "$output_dir"
  shasum -a 256 "$archive_name" > "$archive_name.sha256"
)

printf '%s\n' "$archive"
