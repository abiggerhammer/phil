#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"

if [[ "$(uname -s)" != "Darwin" || "$(uname -m)" != "arm64" ]]; then
  echo 'build-notarized-steve-phase1-darwin-package.sh requires native Apple Silicon macOS' >&2
  exit 1
fi

: "${PHIL_DARWIN_CODESIGN_IDENTITY:?set PHIL_DARWIN_CODESIGN_IDENTITY to the imported Developer ID Application identity}"
: "${APPLE_TEAM_ID:?set APPLE_TEAM_ID}"
: "${APPLE_NOTARY_KEY_PATH:?set APPLE_NOTARY_KEY_PATH to the App Store Connect API .p8 file}"
: "${APPLE_NOTARY_KEY_ID:?set APPLE_NOTARY_KEY_ID}"
: "${APPLE_NOTARY_ISSUER_ID:?set APPLE_NOTARY_ISSUER_ID}"

for tool in codesign ditto otool shasum spctl xattr xcrun; do
  command -v "$tool" >/dev/null 2>&1 || { echo "missing required tool: $tool" >&2; exit 1; }
done

output_dir="${1:-dist/releases}"
version="${PHIL_STEVE_PACKAGE_VERSION:-0.1.1-phase1}"
package_name="phil-steve-${version}-aarch64-apple-darwin"
archive_name="${package_name}.zip"
deployment_target="${MACOSX_DEPLOYMENT_TARGET:-11.0}"
mkdir -p "$output_dir"
output_dir="$(cd "$output_dir" && pwd)"

work="$(mktemp -d "${TMPDIR:-/tmp}/phil-steve-notarized.XXXXXX")"
trap 'rm -rf "$work"' EXIT
unsigned_out="$work/unsigned"
mkdir -p "$unsigned_out"

# Apple Silicon begins with macOS 11. Pin the distributed executable floor
# instead of inheriting the GitHub runner's current macOS version.
export MACOSX_DEPLOYMENT_TARGET="$deployment_target"
scripts/release/build-steve-phase1-darwin-package.sh "$unsigned_out" >/dev/null

tar -xzf "$unsigned_out/phil-steve-0.1.0-phase1-aarch64-apple-darwin.tar.gz" -C "$work"
mv "$work/phil-steve-0.1.0-phase1-aarch64-apple-darwin" "$work/$package_name"
package="$work/$package_name"

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

# Signing changes executable bytes, so regenerate the in-package manifest only
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

archive="$output_dir/$archive_name"
ditto -c -k --keepParent "$package" "$archive"
(
  cd "$output_dir"
  shasum -a 256 "$archive_name" > "$archive_name.sha256"
)

notary_result="$output_dir/$archive_name.notary.json"
xcrun notarytool submit "$archive" \
  --key "$APPLE_NOTARY_KEY_PATH" \
  --key-id "$APPLE_NOTARY_KEY_ID" \
  --issuer "$APPLE_NOTARY_ISSUER_ID" \
  --wait \
  --output-format json \
  > "$notary_result"

python3 - "$notary_result" <<'PY'
import json
import sys

with open(sys.argv[1], encoding="utf-8") as source:
    result = json.load(source)
status = result.get("status")
submission_id = result.get("id")
if status != "Accepted":
    raise SystemExit(f"notarization status is {status!r}, submission={submission_id!r}")
print(f"notarization=Accepted")
print(f"notarization_id={submission_id}")
PY

# Approximate the browser-download boundary in CI: unpack the exact notarized
# ZIP, apply quarantine to both executables, require Gatekeeper assessment, then
# run the package-only smoke without deleting or bypassing quarantine.
consumer="$work/consumer"
mkdir -p "$consumer"
ditto -x -k "$archive" "$consumer"
consumer_package="$consumer/$package_name"
quarantine="0081;$(printf '%x' "$(date +%s)");GitHub-Actions;https://github.com/abiggerhammer/phil/"
for executable in "$consumer_package/bin/philc" "$consumer_package/bin/steve"; do
  xattr -w com.apple.quarantine "$quarantine" "$executable"
  spctl -a -vv -t execute "$executable"
done

(
  cd "$consumer_package"
  ./smoke-test.sh
)

printf 'PASS: Developer-ID signed, notarized, quarantined Phase-1 Steve package\n'
printf 'target=aarch64-apple-darwin\n'
printf 'macos_deployment_target=%s\n' "$deployment_target"
printf 'team_id=%s\n' "$APPLE_TEAM_ID"
printf 'archive_sha256=%s\n' "$(shasum -a 256 "$archive" | awk '{print $1}')"
printf '%s\n' "$archive"
