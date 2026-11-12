#!/usr/bin/env bash
# P11 audit-only staging from an exact, immutable source checkpoint.
# Produces transient Actions artifacts, NEVER a tag, release, or signed claim.
set -euo pipefail

PIN=13808408f9de0f67cefd6fa744f87d81a2d22fbb
TREE=1e5847a146401e5d36ac4250a868e284ff4640fd
PARENT=d2cbe072964c9f7dbb7f37f5e31050151e804bb9

if [[ $# -ne 2 || ( "$1" != linux && "$1" != darwin ) ]]; then
  echo "usage: $0 linux|darwin /absolute/staging-directory" >&2
  exit 2
fi
platform="$1"
out="$2"
case "$out" in /*) ;; *) echo "staging directory must be absolute" >&2; exit 2;; esac
mkdir -p "$out"
test "$(git rev-parse HEAD)" = "$PIN"
test "$(git rev-parse HEAD^{tree})" = "$TREE"
test "$(git rev-parse HEAD^)" = "$PARENT"
test -z "$(git status --porcelain --untracked-files=no)"
export SOURCE_DATE_EPOCH="$(git log -1 --format=%ct)"

hash256() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  else
    shasum -a 256 "$1" | awk '{print $1}'
  fi
}
verify_sidecar() {
  local original="$1" expected
  test -f "$original.sha256"
  expected="$(awk 'NF == 2 {print $1}' "$original.sha256")"
  [[ "$expected" =~ ^[0-9a-f]{64}$ ]]
  test "$expected" = "$(hash256 "$original")"
}
echo "P11_PIN=$PIN tree=$TREE parent=$PARENT"
echo "P11_TARGET=$platform"
{
  git --version
  uname -a
  python3 --version
  ghc --version
  cabal --version
  echo "source_date_epoch=$SOURCE_DATE_EPOCH"
  echo "github_actions_run=${GITHUB_RUN_ID:-not-in-actions}"
  echo "github_actions_attempt=${GITHUB_RUN_ATTEMPT:-not-in-actions}"
} > "$out/toolchain.txt"

case "$platform" in
  linux)
    test "$(uname -s)" = Linux
    test "$(uname -m)" = x86_64
    bash scripts/ci/setup-llvm18.sh
    clang_bin=clang-18
    clang_target=x86_64-unknown-linux-gnu
    ;;
  darwin)
    test "$(uname -s)" = Darwin
    test "$(uname -m)" = arm64
    if ! brew list llvm@18 >/dev/null 2>&1; then
      brew install llvm@18
    fi
    clang_bin="$(brew --prefix llvm@18)/bin/clang"
    clang_target=aarch64-apple-darwin
    # The unchanged Phil Darwin distribution builder pins macOS 11.
    # Build Cabal dependencies against that same floor from the outset;
    # otherwise the prebuild uses the runner's macOS 26 deployment version
    # and the package-builder relink crosses inconsistent object targets.
    export MACOSX_DEPLOYMENT_TARGET=11.0
    echo "macosx_deployment_target=$MACOSX_DEPLOYMENT_TARGET" >> "$out/toolchain.txt"
    ;;
esac
"$clang_bin" --version > "$out/clang-version.txt"
"$clang_bin" --version | head -n 1 | grep -Eq '18[.]'

# The audit-tools checkout is distinct from the pinned source checkout.
# haskell-actions/setup ran cabal update outside the source directory; on Linux
# the repository selects a separate named Hackage index. Refresh that EXACT
# index here, under the frozen candidate, before resolving dependencies.
bash scripts/ci/cabal-update-retry.sh

# Native package builders perform their own compile, manifests and checksum
# production; their historical names are not candidate release tag names.
cabal build all --enable-tests --ghc-options=-Werror

echo "P11_STAGE=phil-$platform"
if [[ "$platform" = linux ]]; then
  bash scripts/release/build-phil-phase1-package.sh "$out" > "$out/phil-build.log"
else
  # On an unsigned audit-only runner, preserve the exact failing builder
  # command if the deployment-floor or linker check still rejects staging.
  bash -x scripts/release/build-phil-phase1-darwin-package.sh "$out" > "$out/phil-build.log"
fi
echo "P11_STAGE=steve-$platform"
if [[ "$platform" = linux ]]; then
  PHIL_STEVE_PACKAGE_VERSION=0.1.1-phase1 \
    bash scripts/release/build-steve-phase1-package.sh "$out" > "$out/steve-build.log"
else
  bash scripts/release/build-steve-phase1-darwin-package.sh "$out" > "$out/steve-build.log"
fi

# Independently materialized LLVM/object evidence from exactly this checkout.
# This is a DIAGNOSTIC REBUILD; do not assert bit identity to the object linked
# into bin/steve (the release builder deletes its own temporary object).
if [[ "$platform" = linux ]]; then
  cabal -v0 exec -- runghc -isrc -itest -Wall -Werror \
    test/Phase1INT006RuntimeChoiceLLVMMain.hs emit > "$out/diagnostic-steve-choice.ll"
else
  cabal -v0 exec -- runghc -isrc -itest -Wall -Werror \
    test/Phase1TargetAArch64AppleDarwinMain.hs emit > "$out/diagnostic-steve-choice.ll"
fi
"$clang_bin" --target="$clang_target" -c \
  "$out/diagnostic-steve-choice.ll" -o "$out/diagnostic-steve-choice.o"
file "$out/diagnostic-steve-choice.o" > "$out/object-file-type.txt"

shopt -s nullglob
archives=( "$out"/*.tar.gz "$out"/*.zip )
test "${#archives[@]}" -eq 2
: > "$out/components.sha256"
: > "$out/stage-smoke.log"
: > "$out/stage-smoke-status.tsv"
p11_checkpoint_rejected=0
consumer="$(mktemp -d "${RUNNER_TEMP:-/tmp}/p11-stage-consumer.XXXXXX")"
trap 'rm -rf "$consumer"' EXIT

for archive in "${archives[@]}"; do
  verify_sidecar "$archive"
  filename="$(basename "$archive")"
  root="${filename%.tar.gz}"
  root="${root%.zip}"
  mkdir -p "$consumer/$root"
  if [[ "$archive" == *.zip ]]; then
    (cd "$consumer/$root" && unzip -q "$archive")
  else
    tar -xzf "$archive" -C "$consumer/$root"
  fi
  stage_dir="$consumer/$root/$root"
  test -x "$stage_dir/smoke-test.sh"
  echo "SMOKE $filename" | tee -a "$out/stage-smoke.log"
  if [[ "$platform" = darwin && "$filename" = phil-0.1.0-phase1-aarch64-apple-darwin.zip &&
        ! -e "$stage_dir/share/phil/phil.release-package" &&
        ! -e "$stage_dir/share/phil/phase1-handoff-manifest-v1.tsv" ]]; then
    # The immutable source checkpoint's historical unsigned Darwin builder
    # installs the NEW smoke script but does NOT emit these two now-required
    # assurance files. Execute and preserve the actual negative, rather than
    # modifying the pinned builder or pretending this is a passing candidate.
    if (cd "$stage_dir" && ./smoke-test.sh) >> "$out/stage-smoke.log" 2>&1; then
      echo "P11 ERROR: legacy Darwin smoke unexpectedly passed despite absent mandatory files" >&2
      exit 1
    fi
    printf '%s\tREJECTED\tmissing-release-package-and-handoff-manifest\n' "$filename" \
      >> "$out/stage-smoke-status.tsv"
    echo "P11 CHECKPOINT REJECTED: historical Darwin Phil builder omits required release package and handoff manifest; native bundled smoke fails" \
      | tee -a "$out/stage-smoke.log"
    # Test the independently built executable only as a LIMITED diagnostic,
    # not a substitute for the failed full package smoke or provenance gate.
    (cd "$stage_dir" && ./bin/philc emit-llvm --target aarch64-apple-darwin \
      share/phil/examples/return-unit.phil) > "$out/phil-darwin-executable-diagnostic.ll"
    grep -Fq 'target triple = "aarch64-apple-darwin"' \
      "$out/phil-darwin-executable-diagnostic.ll"
    p11_checkpoint_rejected=1
  else
    (cd "$stage_dir" && ./smoke-test.sh) | tee -a "$out/stage-smoke.log"
    printf '%s\tPASS\tfull-native-smoke\n' "$filename" >> "$out/stage-smoke-status.tsv"
  fi
  for component in bin/philc bin/steve SHA256SUMS TCB.txt \
    share/phil/phil.release-package share/phil-steve/steve.release-package \
    share/phil/BUILD-INFO; do
    if [[ -f "$stage_dir/$component" ]]; then
      printf '%s  %s/%s\n' "$(hash256 "$stage_dir/$component")" "$root" "$component" \
        >> "$out/components.sha256"
    fi
  done
done

# Tamper negative: altered digest must fail without touching built artifacts.
first="${archives[0]}"
first_sha="$first.sha256"
bad="$out/corrupted-checksum-test.sha256"
sed 's/^[0-9a-f]/0/' "$first_sha" > "$bad"
if cmp -s "$bad" "$first_sha"; then
  sed 's/^[0-9a-f]/f/' "$first_sha" > "$bad"
fi
if grep -Fq "$(hash256 "$first")" "$bad"; then
  echo "Negative control did not alter checksum" >&2
  exit 1
fi
test "$(awk 'NF == 2 {print $1}' "$bad")" != "$(hash256 "$first")"
rm "$bad"

(
  cd "$out"
  : > files.sha256
  for file in *; do
    [[ -f "$file" && "$file" != files.sha256 ]] || continue
    printf '%s  %s\n' "$(hash256 "$out/$file")" "$file" >> files.sha256
  done
)
if [[ "$p11_checkpoint_rejected" -eq 1 ]]; then
  echo "P11_CHECKPOINT_REVIEW=REJECTED; REASON=PINNED_DARWIN_BUILDER_SMOKE_CONTRACT_MISMATCH" \
    | tee "$out/checkpoint-review-status.txt"
  echo "::warning::P11 source checkpoint REJECTED for final candidate: Darwin Phil native smoke fails because pinned builder lacks required assurance files. This job succeeded ONLY as an evidence collector."
else
  echo "P11_CHECKPOINT_REVIEW=PROVISIONAL; FULL_STAGED_SMOKES=PASS" \
    | tee "$out/checkpoint-review-status.txt"
fi
echo "P11_STAGED_ARCHIVES=2; PIN=$PIN; TARGET=$platform"
cat "$out/files.sha256"
echo "P11_STAGE_PROVENANCE=STRUCTURAL_ONLY; DIAGNOSTIC_OBJECT_NOT_SHIPPED=YES"
echo "P11_DARWIN_SIGNED_NOTARIZED=NO; FINAL_PUBLISHED_BYTES=ABSENT; AUDITOR_SIGNOFF=PENDING"
