#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"

if [[ "$(uname -s)" != "Darwin" || "$(uname -m)" != "arm64" ]]; then
  echo 'build-notarized-steve-phase1-darwin-package.sh requires native Apple Silicon macOS' >&2
  exit 1
fi

command_name="${1:-}"
output_dir="${2:-dist/releases}"
version="${PHIL_STEVE_PACKAGE_VERSION:-0.1.1-phase1}"
package_name="phil-steve-${version}-aarch64-apple-darwin"
archive_name="${package_name}.zip"
deployment_target="${MACOSX_DEPLOYMENT_TARGET:-11.0}"
mkdir -p "$output_dir"
output_dir="$(cd "$output_dir" && pwd)"
archive="$output_dir/$archive_name"

case "$command_name" in
  build)
    : "${PHIL_DARWIN_CODESIGN_IDENTITY:?set PHIL_DARWIN_CODESIGN_IDENTITY to the imported Developer ID Application identity}"
    : "${APPLE_TEAM_ID:?set APPLE_TEAM_ID}"

    for tool in codesign ditto otool shasum; do
      command -v "$tool" >/dev/null 2>&1 || { echo "missing required tool: $tool" >&2; exit 1; }
    done

    work="$(mktemp -d "${TMPDIR:-/tmp}/phil-steve-signed.XXXXXX")"
    trap 'rm -rf "$work"' EXIT
    unsigned_out="$work/unsigned"
    mkdir -p "$unsigned_out"

    printf 'stage=build-unsigned-steve\n'
    export MACOSX_DEPLOYMENT_TARGET="$deployment_target"
    scripts/release/build-steve-phase1-darwin-package.sh "$unsigned_out" >/dev/null

    tar -xzf "$unsigned_out/phil-steve-0.1.0-phase1-aarch64-apple-darwin.tar.gz" -C "$work"
    mv "$work/phil-steve-0.1.0-phase1-aarch64-apple-darwin" "$work/$package_name"
    package="$work/$package_name"

    printf 'stage=developer-id-sign\n'
    for executable in "$package/bin/philc" "$package/bin/steve"; do
      codesign --force \
        --options runtime \
        --timestamp \
        --sign "$PHIL_DARWIN_CODESIGN_IDENTITY" \
        "$executable"
      codesign --verify --strict --verbose=4 "$executable"
      codesign -dv --verbose=4 "$executable" 2>&1 \
        | grep -Fq "TeamIdentifier=$APPLE_TEAM_ID"
      minos="$(otool -l "$executable" | awk '/LC_BUILD_VERSION/{seen=1; next} seen && /minos/{print $2; exit}')"
      if [[ "$minos" != "$deployment_target" ]]; then
        echo "$executable has minos $minos; expected $deployment_target" >&2
        exit 1
      fi
    done

    # Signing changes executable bytes, so regenerate the package manifest only
    # after the final signed binaries exist.
    (
      cd "$package"
      find . -type f ! -name SHA256SUMS -print \
        | LC_ALL=C sort \
        | while IFS= read -r path; do
            digest="$(shasum -a 256 "$path" | awk '{print $1}')"
            printf '%s  %s\n' "$digest" "$path"
          done > SHA256SUMS
    )

    printf 'stage=package-signed-zip\n'
    ditto -c -k --keepParent "$package" "$archive"
    (
      cd "$output_dir"
      shasum -a 256 "$archive_name" > "$archive_name.sha256"
    )

    printf 'signed_archive=%s\n' "$archive"
    printf 'signed_archive_sha256=%s\n' "$(shasum -a 256 "$archive" | awk '{print $1}')"
    ;;

  assess)
    : "${APPLE_TEAM_ID:?set APPLE_TEAM_ID}"
    for tool in codesign ditto shasum xattr; do
      command -v "$tool" >/dev/null 2>&1 || { echo "missing required tool: $tool" >&2; exit 1; }
    done
    test -s "$archive"
    test -s "$archive.sha256"
    (
      cd "$output_dir"
      shasum -a 256 -c "$archive_name.sha256"
    )

    work="$(mktemp -d "${TMPDIR:-/tmp}/phil-steve-quarantine.XXXXXX")"
    trap 'rm -rf "$work"' EXIT
    ditto -x -k "$archive" "$work"
    package="$work/$package_name"

    printf 'stage=quarantine-launch-assessment\n'
    quarantine="0081;$(printf '%x' "$(date +%s)");GitHub-Actions;https://github.com/abiggerhammer/phil/"
    for executable in "$package/bin/philc" "$package/bin/steve"; do
      codesign --verify --strict --verbose=4 "$executable"
      codesign -dv --verbose=4 "$executable" 2>&1 \
        | grep -Fq "TeamIdentifier=$APPLE_TEAM_ID"
      xattr -w com.apple.quarantine "$quarantine" "$executable"
      xattr -p com.apple.quarantine "$executable" >/dev/null

      # `spctl --type execute` is app-bundle-oriented on current macOS and may
      # report a correctly signed/notarized bare CLI as "valid but does not seem
      # to be an app". Keep it as diagnostic evidence, but make actual launch
      # under quarantine the authoritative Gatekeeper boundary below.
      if command -v spctl >/dev/null 2>&1; then
        set +e
        spctl_output="$(spctl -a -vv -t execute "$executable" 2>&1)"
        spctl_status=$?
        set -e
        printf 'spctl_path=%s status=%s\n' "$executable" "$spctl_status"
        printf '%s\n' "$spctl_output"
      fi
    done

    # This is the decisive regression for the failure seen by the outside user:
    # both shipped executables retain com.apple.quarantine while the package
    # smoke launches philc and performs real Steve PUT/GET operations. If
    # Gatekeeper blocks or kills either process, the smoke fails.
    printf 'stage=package-smoke-with-quarantine-intact\n'
    (
      cd "$package"
      ./smoke-test.sh
    )

    printf 'PASS: Developer-ID signed, notarized, quarantined Phase-1 Steve package\n'
    printf 'target=aarch64-apple-darwin\n'
    printf 'macos_deployment_target=%s\n' "$deployment_target"
    printf 'team_id=%s\n' "$APPLE_TEAM_ID"
    printf 'archive_sha256=%s\n' "$(shasum -a 256 "$archive" | awk '{print $1}')"
    ;;

  *)
    echo "usage: $0 build|assess [OUTPUT_DIR]" >&2
    exit 2
    ;;
esac
