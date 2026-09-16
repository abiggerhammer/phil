#!/usr/bin/env bash
set -euo pipefail

package_root="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$package_root"

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

test -x bin/philc
test -s README.md
test -s LICENSE
test -s TCB.txt
test -s share/phil/BUILD-INFO
test -s share/phil/docs/tour-phase1.md
test -s share/phil/docs/surface-grammar-v1.md
test -s share/phil/examples/return-unit.phil
test -s share/phil/examples/scalar-binding-42.phil
test -s share/phil/examples/rejected.phil

target="$(sed -n 's/^target=//p' share/phil/BUILD-INFO)"
build_commit="$(sed -n 's/^build_commit=//p' share/phil/BUILD-INFO)"
test -n "$target"
test -n "$build_commit"

case "$target" in
  x86_64-unknown-linux-gnu)
    expected_layout='e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128'
    ;;
  aarch64-apple-darwin)
    expected_layout='e-m:o-i64:64-i128:128-n32:64-S128'
    ;;
  *)
    echo "unsupported packaged target: $target" >&2
    exit 1
    ;;
esac

work="$(mktemp -d "${TMPDIR:-/tmp}/phil-package-smoke.XXXXXX")"
trap 'rm -rf "$work"' EXIT

if HOME="$work/home" bin/philc emit-llvm share/phil/examples/return-unit.phil \
    >"$work/implicit.stdout" 2>"$work/implicit.stderr"; then
  echo 'philc unexpectedly accepted implicit target selection' >&2
  exit 1
fi
grep -q 'usage: philc emit-llvm --target TARGET FILE' "$work/implicit.stderr"

if HOME="$work/home" bin/philc emit-llvm --target not-a-real-target \
    share/phil/examples/return-unit.phil \
    >"$work/unknown.stdout" 2>"$work/unknown.stderr"; then
  echo 'philc unexpectedly accepted unknown target' >&2
  exit 1
fi
grep -q 'unknown target: not-a-real-target' "$work/unknown.stderr"

HOME="$work/home" bin/philc emit-llvm --target "$target" \
  share/phil/examples/return-unit.phil > "$work/accepted.ll"
grep -Fq "target triple = \"$target\"" "$work/accepted.ll"
grep -Fq "target datalayout = \"$expected_layout\"" "$work/accepted.ll"
grep -Fq 'define i32 @main() {' "$work/accepted.ll"

HOME="$work/home" bin/philc emit-llvm --target "$target" \
  share/phil/examples/scalar-binding-42.phil > "$work/scalar.ll"
grep -Fq 'ret i32 %source_value_answer' "$work/scalar.ll"

if HOME="$work/home" bin/philc emit-llvm --target "$target" \
    share/phil/examples/rejected.phil \
    >"$work/rejected.stdout" 2>"$work/rejected.stderr"; then
  echo 'philc unexpectedly accepted rejected source' >&2
  exit 1
fi
test -s "$work/rejected.stderr"

printf 'PASS: packaged Phase-1 Phil public compiler smoke\n'
printf 'platform=%s\n' "$(uname -srm)"
printf 'target=%s\n' "$target"
printf 'build_commit=%s\n' "$build_commit"
printf 'package_manifest_sha256=%s\n' "$(sha256_file SHA256SUMS)"
