#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"

if [[ "$(uname -s)" != "Linux" || "$(uname -m)" != "x86_64" ]]; then
  echo 'build-phil-phase1-package.sh requires x86-64 Linux' >&2
  exit 1
fi

output_dir="${1:-dist/releases}"
package_version="0.1.0-phase1"
package_name="phil-${package_version}-x86_64-linux"
archive_name="${package_name}.tar.gz"
target="x86_64-unknown-linux-gnu"
mkdir -p "$output_dir"
output_dir="$(cd "$output_dir" && pwd)"

work="$(mktemp -d "${TMPDIR:-/tmp}/phil-linux-package.XXXXXX")"
trap 'rm -rf "$work"' EXIT
stage="$work/$package_name"
mkdir -p "$stage/bin" "$stage/share/phil/docs" "$stage/share/phil/examples"

cabal build exe:philc
philc="$(cabal list-bin exe:philc)"
cp "$philc" "$stage/bin/philc"
chmod 0755 "$stage/bin/philc"
file "$stage/bin/philc" | grep -Eq 'ELF 64-bit .*x86-64'

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

cabal -v0 exec -- runghc -isrc -Wall -Werror \
  app/Phase1INT011DistributionReleaseMain.hs \
  emit-linux phil "$package_version" "$build_commit" \
  "$stage/share/phil/phase1-handoff-manifest-v1.tsv" \
  "$stage/bin/philc" \
  > "$release_package"

release_id="$(sed -n 's/^release[[:space:]]id=sha256:\([0-9a-f]\{64\}\)$/\1/p' "$release_package")"
test -n "$release_id"
handoff_sha256="$(sha256sum "$stage/share/phil/phase1-handoff-manifest-v1.tsv" | awk '{print $1}')"
compiler_sha256="$(sha256sum "$stage/bin/philc" | awk '{print $1}')"

cat > "$stage/share/phil/BUILD-INFO" <<EOF
package=phil
version=$package_version
target=$target
build_commit=$build_commit
distribution_release_id=sha256:$release_id
handoff_manifest_sha256=sha256:$handoff_sha256
compiler_sha256=sha256:$compiler_sha256
archive_format=tar.gz
public_command=philc emit-llvm --target TARGET FILE
release_status=linux-distribution-certified-publication-pending
EOF

{
  echo 'Phil 0.1 Phase-1 standalone package trust disclosure'
  echo
  echo 'The authoritative machine-readable distribution record is share/phil/phil.release-package.'
  echo 'The records below are copied verbatim from that distribution record.'
  echo
  grep '^tcb[[:space:]]' "$release_package"
} > "$stage/TCB.txt"

cat > "$stage/README.md" <<'EOF'
# Phil 0.1 — Phase 1 x86-64 Linux package

This package contains the standalone public `philc` executable plus the frozen
Phase-1 handoff root, tour, grammar reference, representative accepted/rejected
source, explicit trust disclosure, and a package-only smoke test.

No repository checkout, GHC, Cabal, or LLVM installation is required to run the
packaged smoke or to emit LLVM text from the included examples.

## Distribution identity

`share/phil/phil.release-package` is the authoritative machine-readable
INT-011 distribution record. It binds the exact packaged `philc` bytes to the
source commit, x86-64 Linux target, frozen Phase-1 handoff manifest, and explicit
remaining distribution TCB. `TCB.txt` is a human-readable projection of those
same TCB rows.

The archive is additionally accompanied by a `.release` sidecar that binds the
distribution release identity to the exact archive digest and the package's
`SHA256SUMS` digest.

## Public compiler path

    bin/philc emit-llvm --target x86_64-unknown-linux-gnu FILE.phil

Target selection is mandatory. The public compiler fails closed on missing or
unknown targets.

## Package smoke

    ./smoke-test.sh

The smoke verifies all packaged checksums, the distribution-release bindings,
the public target-selection failure cases, accepted source lowering with the
exact target triple/data layout, scalar binding preservation, and rejection of
invalid source.

This is a Phase-1 distribution. It explicitly retains the Haskell
compiler/checker and other TCB components named in the machine-readable release
record rather than claiming Phase-2 independent-compiler assurance.
EOF

(
  cd "$stage"
  find . -type f ! -name SHA256SUMS -print \
    | LC_ALL=C sort \
    | while IFS= read -r path; do
        digest="$(sha256sum "$path" | awk '{print $1}')"
        printf '%s  %s\n' "$digest" "$path"
      done > SHA256SUMS
)

archive="$output_dir/$archive_name"
epoch="${SOURCE_DATE_EPOCH:-$(git log -1 --format=%ct)}"
tar --sort=name \
  --mtime="@$epoch" \
  --owner=0 --group=0 --numeric-owner \
  -czf "$archive" \
  -C "$work" "$package_name"

(
  cd "$output_dir"
  sha256sum "$archive_name" > "$archive_name.sha256"
)

archive_release="$output_dir/$archive_name.release"
cabal -v0 exec -- runghc -isrc -Wall -Werror \
  app/Phase1INT011DistributionReleaseMain.hs \
  emit-archive "$release_package" "$archive" "$stage/SHA256SUMS" \
  > "$archive_release"
(
  cd "$output_dir"
  sha256sum "$archive_name.release" > "$archive_name.release.sha256"
)

printf '%s\n' "$archive"
