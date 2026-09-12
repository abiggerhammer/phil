#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"

if [[ "$(uname -s)" != "Darwin" || "$(uname -m)" != "arm64" ]]; then
  echo 'build-phil-phase1-darwin-package.sh requires native Apple Silicon macOS' >&2
  exit 1
fi
if ! command -v shasum >/dev/null 2>&1; then
  echo 'shasum is required to build the Phase-1 Darwin package' >&2
  exit 1
fi

output_dir="${1:-dist/releases}"
package_name="phil-0.1.0-phase1-aarch64-apple-darwin"
archive_name="${package_name}.zip"
target="aarch64-apple-darwin"
deployment_target="11.0"
mkdir -p "$output_dir"
output_dir="$(cd "$output_dir" && pwd)"

work="$(mktemp -d "${TMPDIR:-/tmp}/phil-darwin-package.XXXXXX")"
trap 'rm -rf "$work"' EXIT
stage="$work/$package_name"
mkdir -p "$stage/bin" "$stage/share/phil/docs" "$stage/share/phil/examples"

# Apple Silicon Macs begin at macOS 11. Pin that floor explicitly instead of
# inheriting the GitHub runner's macOS version into the distributed binary.
export MACOSX_DEPLOYMENT_TARGET="$deployment_target"
cabal build exe:philc
philc="$(cabal list-bin exe:philc)"
cp "$philc" "$stage/bin/philc"
chmod 0755 "$stage/bin/philc"
file "$stage/bin/philc" | grep -q 'Mach-O 64-bit executable arm64'
otool -l "$stage/bin/philc" | grep -A6 LC_BUILD_VERSION | grep -q 'minos 11.0'

cp docs/tutorials/tour-phase1.md "$stage/share/phil/docs/tour-phase1.md"
cp docs/phase-1/surface-grammar-v1.md "$stage/share/phil/docs/surface-grammar-v1.md"
cp examples/run/return-unit.phil "$stage/share/phil/examples/return-unit.phil"
cp examples/run/scalar-binding-42.phil "$stage/share/phil/examples/scalar-binding-42.phil"
cat > "$stage/share/phil/examples/rejected.phil" <<'EOF'
component not_main provides Unit {
    return unit
}
EOF
cp LICENSE "$stage/LICENSE"
cp scripts/release/smoke-phil-phase1-package.sh "$stage/smoke-test.sh"
chmod 0755 "$stage/smoke-test.sh"

build_commit="$(git rev-parse HEAD)"
cat > "$stage/share/phil/BUILD-INFO" <<EOF
package=phil
version=0.1.0-phase1
target=$target
build_commit=$build_commit
archive_format=zip
macos_deployment_target=$deployment_target
public_command=philc emit-llvm --target TARGET FILE
release_status=staging-package-signing-notarization-certification-and-publication-pending
EOF

cat > "$stage/TCB.txt" <<'EOF'
Phil 0.1 Phase-1 standalone package trust disclosure

This package is a Phase-1 distribution staging artifact. It does not claim
Phase-2 independent-compiler assurance.

Trusted boundaries retained in this package:
- Phil Haskell compiler/checker: first implementation remains trusted until Phase 2.
- GHC and conventional Apple host linker/runtime used to build the native philc executable.
- Apple Silicon Darwin ABI and macOS runtime assumptions.
- LLVM 18.x semantics/tooling remain the declared validation/lowering tool boundary for emitted LLVM IR.

The final browser-downloadable Darwin artifact additionally requires Developer
ID signing and Apple notarization. Certified-release/manifest binding for the
standalone Phil release is a later INT-011 slice. This file deliberately does
not overstate those closures.
EOF

cat > "$stage/README.md" <<'EOF'
# Phil 0.1 — Phase 1 Apple Silicon macOS package

This package contains the standalone public `philc` executable plus the frozen
Phase-1 tour, grammar reference, representative accepted/rejected source, trust
disclosure, and a package-only smoke test.

No repository checkout, GHC, Cabal, or LLVM installation is required to run the
packaged smoke or to emit LLVM text from the included examples.

## Public compiler path

    bin/philc emit-llvm --target aarch64-apple-darwin FILE.phil

Target selection is mandatory. The public compiler fails closed on missing or
unknown targets.

## Package smoke

    ./smoke-test.sh

The smoke verifies all packaged checksums, the public target-selection failure
cases, accepted source lowering with the exact target triple/data layout, scalar
binding preservation, and rejection of invalid source.

This builder pins the executable deployment floor to macOS 11, the first Apple
Silicon macOS release. The staging package is intentionally not presented as a
public browser-download release until Developer ID signing and Apple notarization
have been added and independently smoke-tested with quarantine intact.
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

archive="$output_dir/$archive_name"
epoch="${SOURCE_DATE_EPOCH:-$(git log -1 --format=%ct)}"
python3 - "$stage" "$archive" "$epoch" <<'PY'
import datetime
import os
import stat
import sys
import zipfile

stage, archive, epoch_text = sys.argv[1:]
epoch = int(epoch_text)
package = os.path.basename(stage)
# ZIP timestamps have a 1980 floor and no timezone field. Use UTC consistently.
dt = datetime.datetime.fromtimestamp(max(epoch, 315532800), datetime.timezone.utc)
date_time = (dt.year, dt.month, dt.day, dt.hour, dt.minute, dt.second)

with zipfile.ZipFile(archive, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as zf:
    paths = []
    for directory, directories, files in os.walk(stage):
        directories.sort()
        files.sort()
        for name in files:
            paths.append(os.path.join(directory, name))
    for path in paths:
        rel = os.path.relpath(path, os.path.dirname(stage))
        info = zipfile.ZipInfo(rel, date_time=date_time)
        info.create_system = 3
        mode = stat.S_IMODE(os.stat(path).st_mode)
        info.external_attr = (stat.S_IFREG | mode) << 16
        info.compress_type = zipfile.ZIP_DEFLATED
        with open(path, "rb") as source:
            zf.writestr(info, source.read(), compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
PY

(
  cd "$output_dir"
  shasum -a 256 "$archive_name" > "$archive_name.sha256"
)

printf '%s\n' "$archive"
