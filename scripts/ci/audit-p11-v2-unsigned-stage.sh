#!/usr/bin/env bash
# P11 audit-only staging from an exact, immutable source checkpoint.
# Produces transient Actions artifacts, NEVER a tag, release, or signed claim.
set -euo pipefail

PIN=9c7d48bc7c5f85b241df9343136c104c3af7a22b
TREE=575abbe2f916c37775e7baba9a35a8235ca0b6da
PARENT1=3d01a717dac361aba0b0eacd4bde1058b9793937
PARENT2=b90d1c1a2ca54d110200a4129dc55ff08cd8a755

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
test "$(git rev-list --parents -n 1 HEAD)" = "$PIN $PARENT1 $PARENT2"
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
echo "P11_V2_PIN=$PIN tree=$TREE parents=$PARENT1,$PARENT2"
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
# Existing typed negative insists the unsigned record cannot reuse signed identity.
cabal -v0 exec -- runghc -isrc -Wall -Werror \
  scripts/release/emit-phil-unsigned-darwin-distribution.hs --self-test

echo "P11_STAGE=phil-$platform"
if [[ "$platform" = linux ]]; then
  bash scripts/release/build-phil-phase1-package.sh "$out" > "$out/phil-build.log"
else
  # Exact pinned corrected UNSIGNED Darwin source; full smoke is mandatory.
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
  (cd "$stage_dir" && ./smoke-test.sh) | tee -a "$out/stage-smoke.log"
  printf '%s\tPASS\tfull-native-smoke\n' "$filename" >> "$out/stage-smoke-status.tsv"
  if [[ "$platform" = darwin && "$filename" = phil-0.1.0-phase1-aarch64-apple-darwin.zip ]]; then
    # Build-toolchain trust basis is explicitly UNSIGNED and must not assert
    # Developer-ID signing/notarization. All four TCB kinds remain present.
    record="$stage_dir/share/phil/phil.release-package"
    handoff="$stage_dir/share/phil/phase1-handoff-manifest-v1.tsv"
    buildinfo="$stage_dir/share/phil/BUILD-INFO"
    test -s "$record" && test -s "$handoff" && test -s "$buildinfo"
    grep '^tcb[[:space:]]id=build-toolchain' "$record" | grep -Fq 'native unsigned philc executable'
    if grep -Fq 'native signed philc executable' "$record"; then
      echo "P11 ERROR: staging record falsely claims a signed executable" >&2
      exit 1
    fi
    test "$(grep -c '^tcb[[:space:]]' "$record")" -eq 4
    diff -u <(grep '^tcb[[:space:]]' "$record") <(grep '^tcb[[:space:]]' "$stage_dir/TCB.txt")
    grep -Fxq "build_commit=$PIN" "$buildinfo"
    # A changed handoff MUST fail the unchanged distributed package smoke.
    tamper="$(mktemp -d "${RUNNER_TEMP:-/tmp}/p11-v2-tamper.XXXXXX")"
    cp -R "$stage_dir/." "$tamper/"
    printf '\nP11-v2-falsified-handoff\n' >> "$tamper/share/phil/phase1-handoff-manifest-v1.tsv"
    if (cd "$tamper" && ./smoke-test.sh) >> "$out/stage-smoke.log" 2>&1; then
      echo "P11 ERROR: changed handoff unexpectedly passed full package smoke" >&2
      rm -rf "$tamper"
      exit 1
    fi
    rm -rf "$tamper"
    echo "P11_V2_DARWIN_HANDOFF_TAMPER_REJECTED=PASS" | tee -a "$out/stage-smoke.log"
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
echo "P11_V2_CHECKPOINT_REVIEW=PROVISIONAL; FULL_STAGED_SMOKES=PASS; SIGNING_NOTARIZATION=PENDING" \
  | tee "$out/checkpoint-review-status.txt"
echo "P11_V2_STAGED_ARCHIVES=2; PIN=$PIN; TARGET=$platform"
cat "$out/files.sha256"
echo "P11_V2_STAGE_PROVENANCE=STRUCTURAL_ONLY; DIAGNOSTIC_OBJECT_NOT_SHIPPED=YES"
echo "P11_DARWIN_SIGNED_NOTARIZED=NO; FINAL_PUBLISHED_BYTES=ABSENT; AUDITOR_SIGNOFF=PENDING"
