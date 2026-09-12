#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"

output_dir="${1:-dist/releases}"
version="${PHIL_STEVE_PACKAGE_VERSION:-0.1.0-phase1}"
package_name="phil-steve-${version}-x86_64-linux"
archive_name="${package_name}.tar.gz"
mkdir -p "$output_dir"
output_dir="$(cd "$output_dir" && pwd)"

work="$(mktemp -d "${TMPDIR:-/tmp}/phil-steve-package.XXXXXX")"
trap 'rm -rf "$work"' EXIT
stage="$work/$package_name"
mkdir -p "$stage/bin" "$stage/share/phil-steve/source" "$stage/share/phil-steve/docs"

PHIL_LLVM18_TOOLS="clang"
source scripts/ci/resolve-llvm18.sh
unset PHIL_LLVM18_TOOLS

# Build the ordinary public checker/compiler shipped beside Steve and the
# Haskell substrate needed to materialize the certified Phase-1 Steve object.
cabal build all --enable-tests

llvm="$work/steve-runtime-choice.ll"
object="$work/steve-runtime-choice.o"

# These commands emit machine-consumed artifacts on stdout. Keep Cabal's own
# dependency/status chatter off that channel so the resulting files contain
# only the emitter output.
cabal -v0 exec -- runghc -isrc -itest -Wall -Werror \
  test/Phase1INT006RuntimeChoiceLLVMMain.hs emit > "$llvm"
"$CLANG" --target=x86_64-unknown-linux-gnu -c "$llvm" -o "$object"

cabal exec -- ghc -isrc -iruntime/phase1 \
  -package directory -package unix \
  -Wall -Werror \
  runtime/phase1/StevePublicMain.hs "$object" \
  -o "$stage/bin/steve"

philc="$(cabal list-bin exe:philc)"
cp "$philc" "$stage/bin/philc"
chmod 0755 "$stage/bin/steve" "$stage/bin/philc"

cabal -v0 exec -- runghc -isrc -itest -Wall -Werror \
  test/Phase1INT005ReleasePackageMain.hs emit steve \
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
# Phil Steve 0.1 — Phase 1 Linux x86_64 package

This package contains the Phase-1 Steve content-addressed store command, the
ordinary `philc` checker/compiler executable, the canonical Phil Steve source,
and the certified release-package/TCB records used to build this artifact.

## What is trusted

Read `TCB.txt` before relying on the package. The authoritative machine-readable
copy is `share/phil-steve/steve.release-package`. In Phase 1, the Phil Haskell
compiler/checker remains trusted until Phase 2; the package states that rather
than hiding it. The conventional host runtime, qualified provider realization,
LLVM toolchain, external checkers, and x86_64 Linux target assumptions are also
named there.

## Quick smoke

After unpacking the archive, run:

    ./smoke-test.sh

The smoke verifies every packaged file against `SHA256SUMS`, checks that the
human-readable TCB is an exact copy of the certified TCB records, exercises
`philc`, performs real Steve PUT and GET operations, and verifies that corrupt
CAS content cannot replace an existing output file. Its final lines report the
platform and package evidence digests suitable for an external-use report.

## PUT

Steve paths are relative to the user-filesystem root you select. Create a store
and a user-files directory, put a file under the user-files directory, then pass
its relative path on standard input:

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

- `bin/steve` — runnable Phase-1 Steve command for x86_64 Linux.
- `bin/philc` — ordinary Phil checker/compiler executable shipped with Steve.
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
  find . -type f ! -name SHA256SUMS -print0 \
    | LC_ALL=C sort -z \
    | xargs -0 sha256sum > SHA256SUMS
)

# Produce stable ownership/order metadata; gzip -n removes timestamp/name data
# from the gzip wrapper. SOURCE_DATE_EPOCH can pin the archive mtime externally.
epoch="${SOURCE_DATE_EPOCH:-$(git log -1 --format=%ct)}"
archive="$output_dir/$archive_name"
tar --sort=name --owner=0 --group=0 --numeric-owner --mtime="@$epoch" \
  -C "$work" -cf - "$package_name" | gzip -n > "$archive"
(
  cd "$output_dir"
  sha256sum "$archive_name" > "$archive_name.sha256"
)

printf '%s\n' "$archive"
