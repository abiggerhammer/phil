#!/usr/bin/env bash
set -euo pipefail

# Historical emitters below replay structural-only INT-005 data, not the sealed
# checked-architecture producer-to-final-origin acceptance path.
OUT_DIR="dist/int005-certified-release"
rm -rf "$OUT_DIR"
mkdir -p "$OUT_DIR"

emit_bundle() {
  local witness="$1"
  local stem="$2"

  cabal exec -- runghc -isrc -itest -Wall -Werror \
    test/Phase1INT005EmitCertifiedReleaseMain.hs "$witness" \
    > "$OUT_DIR/$stem.ll"

  cabal exec -- runghc -isrc -itest -Wall -Werror \
    test/Phase1INT005ReleasePackageMain.hs emit "$witness" \
    > "$OUT_DIR/$stem.release-package"

  test -s "$OUT_DIR/$stem.ll"
  test -s "$OUT_DIR/$stem.release-package"
  grep -q '^package[[:space:]]id=' "$OUT_DIR/$stem.release-package"
  grep -q '^manifest[[:space:]]' "$OUT_DIR/$stem.release-package"
  grep -q '^llvm[[:space:]]' "$OUT_DIR/$stem.release-package"
  grep -q '^lowering-decision[[:space:]]' "$OUT_DIR/$stem.release-package"
  test "$(grep -c '^tcb[[:space:]]' "$OUT_DIR/$stem.release-package")" -eq 6
}

emit_bundle upload upload
emit_bundle steve steve

# Re-run the exact native execution path that consumes the same certified
# release construction used by the emitted package pair.
bash scripts/ci/phase1-int-005-native-release-smoke.sh

printf 'PASS: emitted inspectable INT-005 release bundles for Upload and Steve\n'
sha256sum \
  "$OUT_DIR/upload.ll" \
  "$OUT_DIR/upload.release-package" \
  "$OUT_DIR/steve.ll" \
  "$OUT_DIR/steve.release-package"

# An independently minted structural CertifiedReleaseArtifact cannot enter
# the public final-origin release-package builder; require an opaque-type
# compiler error, rather than counting a dependency/network error as rejection.
negative_log="$(mktemp)"
trap 'rm -f "$negative_log"' EXIT
if cabal exec -- ghc -fno-code -isrc -itest -Wall -Werror test/Phase1INT005FinalOriginPackageTypeNegative.hs >"$negative_log" 2>&1; then
  echo 'FAIL: legacy CertifiedReleaseArtifact entered final-origin package API' >&2
  exit 1
fi
grep -q 'AcceptedVerifiedFinalOrigin' "$negative_log" || {
  cat "$negative_log" >&2
  echo 'FAIL: did not reject opaque final-origin type' >&2
  exit 1
}
echo 'PASS: final-origin package API rejects legacy release artifact'
