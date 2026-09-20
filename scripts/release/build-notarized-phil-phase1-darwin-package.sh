#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"

if [[ "$(uname -s)" != "Darwin" || "$(uname -m)" != "arm64" ]]; then
  echo 'build-notarized-phil-phase1-darwin-package.sh requires native Apple Silicon macOS' >&2
  exit 1
fi

command_name="${1:-}"
output_dir="${2:-dist/releases}"
package_version="0.1.0-phase1"
package_name="phil-${package_version}-aarch64-apple-darwin"
archive_name="${package_name}.zip"
target="aarch64-apple-darwin"
deployment_target="${MACOSX_DEPLOYMENT_TARGET:-11.0}"
mkdir -p "$output_dir"
output_dir="$(cd "$output_dir" && pwd)"
archive="$output_dir/$archive_name"

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

case "$command_name" in
  build)
    : "${PHIL_DARWIN_CODESIGN_IDENTITY:?set PHIL_DARWIN_CODESIGN_IDENTITY to the imported Developer ID Application identity}"
    : "${APPLE_TEAM_ID:?set APPLE_TEAM_ID}"

    for tool in codesign ditto file otool shasum; do
      command -v "$tool" >/dev/null 2>&1 || { echo "missing required tool: $tool" >&2; exit 1; }
    done

    work="$(mktemp -d "${TMPDIR:-/tmp}/phil-signed.XXXXXX")"
    trap 'rm -rf "$work"' EXIT
    stage="$work/$package_name"
    mkdir -p "$stage/bin" "$stage/share/phil/docs" "$stage/share/phil/examples"

    export MACOSX_DEPLOYMENT_TARGET="$deployment_target"
    cabal build exe:philc
    philc="$(cabal list-bin exe:philc)"
    cp "$philc" "$stage/bin/philc"
    chmod 0755 "$stage/bin/philc"
    file "$stage/bin/philc" | grep -q 'Mach-O 64-bit executable arm64'

    printf 'stage=developer-id-sign\n'
    codesign --force \
      --options runtime \
      --timestamp \
      --sign "$PHIL_DARWIN_CODESIGN_IDENTITY" \
      "$stage/bin/philc"
    codesign --verify --strict --verbose=4 "$stage/bin/philc"
    codesign -dv --verbose=4 "$stage/bin/philc" 2>&1 \
      | grep -Fq "TeamIdentifier=$APPLE_TEAM_ID"
    minos="$(otool -l "$stage/bin/philc" | awk '/LC_BUILD_VERSION/{seen=1; next} seen && /minos/{print $2; exit}')"
    test "$minos" = "$deployment_target"

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
      emit-darwin phil "$package_version" "$build_commit" \
      "$stage/share/phil/phase1-handoff-manifest-v1.tsv" \
      "$stage/bin/philc" \
      > "$release_package"

    release_id="$(record_field "$release_package" release id)"
    [[ "$release_id" =~ ^sha256:[0-9a-f]{64}$ ]]
    handoff_sha256="$(shasum -a 256 "$stage/share/phil/phase1-handoff-manifest-v1.tsv" | awk '{print $1}')"
    compiler_sha256="$(shasum -a 256 "$stage/bin/philc" | awk '{print $1}')"

    cat > "$stage/share/phil/BUILD-INFO" <<EOF
package=phil
version=$package_version
target=$target
build_commit=$build_commit
distribution_release_id=$release_id
handoff_manifest_sha256=sha256:$handoff_sha256
compiler_sha256=sha256:$compiler_sha256
archive_format=zip
macos_deployment_target=$deployment_target
developer_id_team=$APPLE_TEAM_ID
release_status=developer-id-signed-notarization-pending
public_command=philc emit-llvm --target TARGET FILE
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
# Phil 0.1 — Phase 1 Apple Silicon macOS package

This package contains the standalone public `philc` executable, Developer-ID
signed before its canonical INT-011 distribution identity is computed.

`share/phil/phil.release-package` binds the exact signed `philc` bytes to the
source commit, Apple Silicon Darwin target, frozen Phase-1 handoff root, and
explicit distribution TCB. The external `.zip.release` sidecar binds that
internal identity to the exact downloadable archive and package manifest.

The public compiler path is:

    bin/philc emit-llvm --target aarch64-apple-darwin FILE.phil

Run `./smoke-test.sh` after extraction. The final INT-011 Darwin gate additionally
requires Apple notarization and launches the signed compiler with quarantine
intact; removing quarantine or bypassing Gatekeeper is not part of the release
procedure.

This is a Phase-1 distribution. It explicitly retains the bootstrap
compiler/checker and other TCB components named by the machine-readable release
record rather than claiming Phase-2 independent-compiler assurance.
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

    printf 'stage=package-signed-zip\n'
    ditto -c -k --keepParent "$stage" "$archive"
    (
      cd "$output_dir"
      shasum -a 256 "$archive_name" > "$archive_name.sha256"
    )

    release_sidecar="$archive.release"
    cabal -v0 exec -- runghc -isrc -Wall -Werror \
      app/Phase1INT011DistributionReleaseMain.hs \
      emit-archive "$release_package" "$archive" "$stage/SHA256SUMS" \
      > "$release_sidecar"
    (
      cd "$output_dir"
      shasum -a 256 "$archive_name.release" > "$archive_name.release.sha256"
    )

    printf 'signed_archive=%s\n' "$archive"
    printf 'signed_archive_sha256=%s\n' "$(shasum -a 256 "$archive" | awk '{print $1}')"
    printf 'distribution_release_id=%s\n' "$release_id"
    ;;

  assess)
    : "${APPLE_TEAM_ID:?set APPLE_TEAM_ID}"
    for tool in codesign ditto shasum xattr; do
      command -v "$tool" >/dev/null 2>&1 || { echo "missing required tool: $tool" >&2; exit 1; }
    done

    release_sidecar="$archive.release"
    test -s "$archive"
    test -s "$archive.sha256"
    test -s "$release_sidecar"
    test -s "$release_sidecar.sha256"
    (
      cd "$output_dir"
      shasum -a 256 -c "$archive_name.sha256"
      shasum -a 256 -c "$archive_name.release.sha256"
    )

    work="$(mktemp -d "${TMPDIR:-/tmp}/phil-quarantine.XXXXXX")"
    trap 'rm -rf "$work"' EXIT
    ditto -x -k "$archive" "$work"
    package="$work/$package_name"
    release_file="$package/share/phil/phil.release-package"

    internal_release_id="$(record_field "$release_file" release id)"
    bound_release_id="$(record_field "$release_sidecar" release id)"
    bound_archive_name="$(record_field "$release_sidecar" archive name)"
    bound_archive_sha="$(record_field "$release_sidecar" archive sha256)"
    bound_manifest_sha="$(record_field "$release_sidecar" package-manifest sha256)"

    test "$bound_release_id" = "$internal_release_id"
    test "$bound_archive_name" = "$archive_name"
    test "$bound_archive_sha" = "sha256:$(shasum -a 256 "$archive" | awk '{print $1}')"
    test "$bound_manifest_sha" = "sha256:$(shasum -a 256 "$package/SHA256SUMS" | awk '{print $1}')"

    printf 'stage=quarantine-launch-assessment\n'
    codesign --verify --strict --verbose=4 "$package/bin/philc"
    codesign -dv --verbose=4 "$package/bin/philc" 2>&1 \
      | grep -Fq "TeamIdentifier=$APPLE_TEAM_ID"

    quarantine="0081;$(printf '%x' "$(date +%s)");GitHub-Actions;https://github.com/abiggerhammer/phil/"
    xattr -w com.apple.quarantine "$quarantine" "$package/bin/philc"
    xattr -p com.apple.quarantine "$package/bin/philc" >/dev/null

    if command -v spctl >/dev/null 2>&1; then
      set +e
      spctl_output="$(spctl -a -vv -t execute "$package/bin/philc" 2>&1)"
      spctl_status=$?
      set -e
      printf 'spctl_status=%s\n' "$spctl_status"
      printf '%s\n' "$spctl_output"
    fi

    (
      cd "$package"
      ./smoke-test.sh
    )

    xattr -p com.apple.quarantine "$package/bin/philc" >/dev/null

    printf 'PASS: Developer-ID signed, notarized, quarantined Phase-1 Phil distribution\n'
    printf 'target=%s\n' "$target"
    printf 'macos_deployment_target=%s\n' "$deployment_target"
    printf 'team_id=%s\n' "$APPLE_TEAM_ID"
    printf 'distribution_release_id=%s\n' "$internal_release_id"
    printf 'archive_sha256=sha256:%s\n' "$(shasum -a 256 "$archive" | awk '{print $1}')"
    ;;

  *)
    echo "usage: $0 build|assess [OUTPUT_DIR]" >&2
    exit 2
    ;;
esac
