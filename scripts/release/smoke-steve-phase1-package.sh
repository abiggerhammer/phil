#!/usr/bin/env bash
set -euo pipefail

package_root="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$package_root"

release="share/phil-steve/steve.release-package"

if command -v sha256sum >/dev/null 2>&1; then
  verify_checksums() { sha256sum -c "$1"; }
  sha256_file() { sha256sum "$1" | awk '{print $1}'; }
elif command -v shasum >/dev/null 2>&1; then
  verify_checksums() { shasum -a 256 -c "$1"; }
  sha256_file() { shasum -a 256 "$1" | awk '{print $1}'; }
else
  echo 'need sha256sum or shasum for package verification' >&2
  exit 1
fi

verify_checksums SHA256SUMS

test -x bin/steve
test -x bin/philc
test -s "$release"
test -s TCB.txt

grep -q '^package[[:space:]]id=' "$release"
grep -q '^manifest[[:space:]]' "$release"
grep -q '^llvm[[:space:]]' "$release"
test "$(grep -c '^tcb[[:space:]]' "$release")" -eq 6
test "$(grep -c '^tcb[[:space:]]' TCB.txt)" -eq 6
diff \
  <(grep '^tcb[[:space:]]' "$release") \
  <(grep '^tcb[[:space:]]' TCB.txt)

grep -q 'name=Phil Haskell compiler/checker' TCB.txt
grep -q 'basis=first implementation remains trusted until Phase 2' TCB.txt

work="$(mktemp -d "${TMPDIR:-/tmp}/phil-steve-smoke.XXXXXX")"
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/home" "$work/user-files" "$work/store"

if HOME="$work/home" bin/philc >"$work/philc.stdout" 2>"$work/philc.stderr"; then
  echo 'philc unexpectedly accepted an empty invocation' >&2
  exit 1
fi
grep -q 'usage: philc emit-llvm FILE' "$work/philc.stderr"

printf 'external Steve smoke artifact\n' > "$work/user-files/input.bin"
content_id="$(printf 'input.bin\n' | \
  HOME="$work/home" bin/steve put "$work/store" "$work/user-files")"

test "${#content_id}" -eq 64
printf '%s' "$content_id" | grep -Eq '^[0-9a-f]{64}$'
test -f "$work/store/$content_id"
cmp "$work/user-files/input.bin" "$work/store/$content_id"

printf '%s\noutput.bin\n' "$content_id" | \
  HOME="$work/home" bin/steve get "$work/store" "$work/user-files"
cmp "$work/user-files/input.bin" "$work/user-files/output.bin"

printf 'must survive corrupt GET\n' > "$work/user-files/guard.bin"
printf 'tampered bytes\n' > "$work/store/$content_id"
printf '%s\nguard.bin\n' "$content_id" | \
  HOME="$work/home" bin/steve get "$work/store" "$work/user-files"
grep -qx 'must survive corrupt GET' "$work/user-files/guard.bin"

printf 'PASS: packaged Phase-1 Steve put/get and corruption smoke\n'
printf 'platform=%s\n' "$(uname -srm)"
printf 'release_package_sha256=%s\n' "$(sha256_file "$release")"
printf 'package_manifest_sha256=%s\n' "$(sha256_file SHA256SUMS)"
