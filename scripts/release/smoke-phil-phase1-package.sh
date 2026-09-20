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

verify_checksums SHA256SUMS

test -x bin/philc
test -s README.md
test -s LICENSE
test -s TCB.txt
test -s share/phil/BUILD-INFO
test -s share/phil/phil.release-package
test -s share/phil/phase1-handoff-manifest-v1.tsv
test -s share/phil/docs/tour-phase1.md
test -s share/phil/docs/surface-grammar-v1.md
test -s share/phil/examples/return-unit.phil
test -s share/phil/examples/scalar-binding-42.phil
test -s share/phil/examples/rejected.phil

target="$(sed -n 's/^target=//p' share/phil/BUILD-INFO)"
build_commit="$(sed -n 's/^build_commit=//p' share/phil/BUILD-INFO)"
build_release_id="$(sed -n 's/^distribution_release_id=//p' share/phil/BUILD-INFO)"
build_handoff_sha256="$(sed -n 's/^handoff_manifest_sha256=//p' share/phil/BUILD-INFO)"
build_compiler_sha256="$(sed -n 's/^compiler_sha256=//p' share/phil/BUILD-INFO)"
test -n "$target"
test -n "$build_commit"

release_file="share/phil/phil.release-package"
grep -q '^PHIL-PHASE1-DISTRIBUTION-RELEASE-V1$' "$release_file"
release_id="$(record_field "$release_file" release id)"
release_target="$(record_field "$release_file" package target)"
release_commit="$(record_field "$release_file" source commit)"
release_handoff_sha256="$(record_field "$release_file" handoff sha256)"
release_compiler_sha256="$(record_field "$release_file" compiler sha256)"

[[ "$release_id" =~ ^sha256:[0-9a-f]{64}$ ]]
test "$release_target" = "$target"
test "$release_commit" = "$build_commit"
test "$release_handoff_sha256" = "sha256:$(sha256_file share/phil/phase1-handoff-manifest-v1.tsv)"
test "$release_compiler_sha256" = "sha256:$(sha256_file bin/philc)"
test "$build_release_id" = "$release_id"
test "$build_handoff_sha256" = "$release_handoff_sha256"
test "$build_compiler_sha256" = "$release_compiler_sha256"

work="$(mktemp -d "${TMPDIR:-/tmp}/phil-package-smoke.XXXXXX")"
trap 'rm -rf "$work"' EXIT

grep '^tcb[[:space:]]' "$release_file" > "$work/release.tcb"
grep '^tcb[[:space:]]' TCB.txt > "$work/human.tcb"
cmp "$work/release.tcb" "$work/human.tcb"
test "$(wc -l < "$work/release.tcb" | tr -d ' ')" -eq 4
for trust_id in compiler-checker build-toolchain llvm-toolchain target-assumptions; do
  grep -q "^tcb[[:space:]]id=$trust_id[[:space:]]" "$work/release.tcb"
done

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
printf 'distribution_release_id=%s\n' "$release_id"
printf 'handoff_manifest_sha256=%s\n' "$release_handoff_sha256"
printf 'compiler_sha256=%s\n' "$release_compiler_sha256"
printf 'package_manifest_sha256=sha256:%s\n' "$(sha256_file SHA256SUMS)"
