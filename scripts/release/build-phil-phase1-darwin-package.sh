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
cp handoff/phase1/manifest-v1.tsv "$stage/share/phil/phase1-handoff-manifest-v1.tsv"
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
release_package="$stage/share/phil/phil.release-package"

# Bind the exact UNSIGNED compiler/source/handoff using the native typed
# INT-011 distribution record with a structurally checked unsigned-only
# trust basis. The signed/privileged release builder stays unchanged.
cabal -v0 exec -- runghc -isrc -Wall -Werror \
  scripts/release/emit-phil-unsigned-darwin-distribution.hs \
  "0.1.0-phase1" "$build_commit" \
  "$stage/share/phil/phase1-handoff-manifest-v1.tsv" \
  "$stage/bin/philc" \
  > "$release_package"

record_field() {
  local file="$1" tag="$2" key="$3"
  awk -F '\t' -v wanted_tag="$tag" -v wanted_key="$key" '
    $1 == wanted_tag {
      for (i = 2; i <= NF; ++i) {
        prefix = wanted_key "="
        if (index($i, prefix) == 1) {
          print substr($i, length(prefix) + 1)
          exit
        }
      }
    }
  ' "$file"
}
release_id="$(record_field "$release_package" release id)"
[[ "$release_id" =~ ^sha256:[0-9a-f]{64}$ ]]
handoff_sha256="$(shasum -a 256 "$stage/share/phil/phase1-handoff-manifest-v1.tsv" | awk '{print $1}')"
compiler_sha256="$(shasum -a 256 "$stage/bin/philc" | awk '{print $1}')"

cat > "$stage/share/phil/BUILD-INFO" <<EOF
package=phil
version=0.1.0-phase1
target=$target
build_commit=$build_commit
distribution_release_id=$release_id
handoff_manifest_sha256=sha256:$handoff_sha256
compiler_sha256=sha256:$compiler_sha256
archive_format=zip
macos_deployment_target=$deployment_target
public_command=philc emit-llvm --target TARGET FILE
release_status=unsigned-staging-distribution-identity-checked-signing-notarization-publication-pending
EOF

# The human disclosure and machine release identity must enumerate the
# SAME four declared trust roots. Do not maintain independent hand-written lists.
{
  echo 'Phil 0.1 Phase-1 standalone package trust disclosure'
  echo
  echo 'The authoritative machine-readable distribution record is share/phil/phil.release-package.'
  echo 'The records below are copied verbatim from that distribution record.'
  echo
  grep '^tcb[[:space:]]' "$release_package"
} > "$stage/TCB.txt"
test "$(grep -c '^tcb[[:space:]]' "$stage/TCB.txt")" -eq 4

cat > "$stage/README.md" <<'EOF'
# Phil 0.1 — Phase 1 Apple Silicon macOS package

This UNSIGNED staging package contains the standalone public `philc` executable,
the frozen Phase-1 handoff, tour, grammar reference, representative
accepted/rejected source, distribution identity, declared trust disclosure,
and a package-only smoke test. No release signature or notarization is claimed.

`share/phil/phil.release-package` binds the exact packaged UNSIGNED `philc`
bytes to the source commit, target, Phase-1 handoff manifest and TCB.
`share/phil/BUILD-INFO` repeats that identity and the exact component hashes.
An archive-level `.release` sidecar separately binds the archive and manifest
byte hashes to this distribution identity. Neither record establishes
P7 checked-occurrence provenance for the separately compiled executable.

No repository checkout, GHC, Cabal, or LLVM installation is required to run the
packaged smoke or to emit LLVM text from the included examples.

## Public compiler path

    bin/philc emit-llvm --target aarch64-apple-darwin FILE.phil

Target selection is mandatory. The public compiler fails closed on missing or
unknown targets.

## Package smoke

    ./smoke-test.sh

The smoke verifies all packaged checksums, the distribution-release record,
source and handoff binding, exact compiler-byte digest, four declared TCB roots,
public target-selection failures, accepted source lowering with the exact
target triple/data layout, scalar binding, and rejection of invalid source.

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

# Separately bind downloadable archive bytes to the exact internal unsigned
# distribution identity and SHA256SUMS. No public release or sign-off occurs.
release_sidecar="$archive.release"
cabal -v0 exec -- runghc -isrc -Wall -Werror \
  app/Phase1INT011DistributionReleaseMain.hs \
  emit-archive "$release_package" "$archive" "$stage/SHA256SUMS" \
  > "$release_sidecar"
(
  cd "$output_dir"
  shasum -a 256 "$archive_name.release" > "$archive_name.release.sha256"
)

printf '%s\n' "$archive"
