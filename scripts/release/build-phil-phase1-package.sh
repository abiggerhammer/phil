#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"

if [[ "$(uname -s)" != "Linux" || "$(uname -m)" != "x86_64" ]]; then
  echo 'build-phil-phase1-package.sh requires x86-64 Linux' >&2
  exit 1
fi

output_dir="${1:-dist/releases}"
package_name="phil-0.1.0-phase1-x86_64-linux"
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
archive_format=tar.gz
public_command=philc emit-llvm --target TARGET FILE
release_status=staging-package-certification-and-publication-pending
EOF

cat > "$stage/TCB.txt" <<'EOF'
Phil 0.1 Phase-1 standalone package trust disclosure

This package is a Phase-1 distribution staging artifact. It does not claim
Phase-2 independent-compiler assurance.

Trusted boundaries retained in this package:
- Phil Haskell compiler/checker: first implementation remains trusted until Phase 2.
- GHC and conventional host linker/runtime used to build the native philc executable.
- Host operating system and x86-64 Linux ABI assumptions.
- LLVM 18.x semantics/tooling remain the declared validation/lowering tool boundary for emitted LLVM IR.

The certified-release/manifest binding for the final standalone Phil release is
a later INT-011 slice. This file deliberately does not overstate that closure.
EOF

cat > "$stage/README.md" <<'EOF'
# Phil 0.1 — Phase 1 x86-64 Linux package

This package contains the standalone public `philc` executable plus the frozen
Phase-1 tour, grammar reference, representative accepted/rejected source, trust
disclosure, and a package-only smoke test.

No repository checkout, GHC, Cabal, or LLVM installation is required to run the
packaged smoke or to emit LLVM text from the included examples.

## Public compiler path

    bin/philc emit-llvm --target x86_64-unknown-linux-gnu FILE.phil

Target selection is mandatory. The public compiler fails closed on missing or
unknown targets.

## Package smoke

    ./smoke-test.sh

The smoke verifies all packaged checksums, the public target-selection failure
cases, accepted source lowering with the exact target triple/data layout, scalar
binding preservation, and rejection of invalid source.

`TCB.txt` names the remaining Phase-1 trust boundary. Final certified release
binding and public GitHub Release publication are later INT-011 closeout slices.
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

printf '%s\n' "$archive"
