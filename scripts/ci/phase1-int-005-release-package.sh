#!/usr/bin/env bash
set -euo pipefail

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
