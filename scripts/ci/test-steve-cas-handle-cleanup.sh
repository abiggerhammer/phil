#!/usr/bin/env bash
set -euo pipefail

if [[ "$(uname -s)" != Linux || ! -d /proc/self/fd ]]; then
  echo 'SKIP: E-STEVE-CLEANUP-01 needs Linux /proc/self/fd'
  exit 0
fi

repo_root="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$repo_root"
work="$(mktemp -d /tmp/phil-steve-cas-cleanup.XXXXXX)"
trap 'rm -rf "$work"' EXIT

# Read and verify the exact historical source blob rather than assuming that
# a generic failed filesystem write proves the pre-close failure mechanism.
baseline=9ad035731fc4c87c5be2aba7e4bc589b738f1231
expected_blob=ccc9e975be0ee318e333808387217c71d8217af5
mkdir -p "$work/baseline/Phil/Compiler" "$work/repaired/Phil/Compiler"
git show "$baseline:src/Phil/Compiler/SteveCAS.hs" > "$work/original-source.hs"
test "$(git hash-object "$work/original-source.hs")" = "$expected_blob"
cp src/Phil/Compiler/SteveCAS.hs "$work/repaired-source.hs"

# Test-only deterministic fault at the precise hPut point, before hClose.
# Instrument exactly one call in each source, without editing the checkout.
python3 - "$work" <<'PY'
from pathlib import Path
import sys

work = Path(sys.argv[1])
needle = "ByteString.hPut handle bytes"
fault = '(ioError (userError "E-STEVE-CLEANUP-01-injected-preclose-failure"))'
for label, original in [("baseline", "original-source.hs"),
                        ("repaired", "repaired-source.hs")]:
    source = (work / original).read_text()
    def exactly_once(text, old, replacement):
        if text.count(old) != 1:
            raise SystemExit(f"{label}: expected one instrumentation anchor: {old!r}")
        return text.replace(old, replacement)
    source = exactly_once(source, "  , readBlob\n  ) where",
                          "  , readBlob\n  , testStagedHandleClosed\n  ) where")
    source = exactly_once(source,
        "import qualified Crypto.Hash.SHA256 as SHA256",
        "import Data.IORef (IORef, newIORef, readIORef, writeIORef)\n"
        "import System.IO.Unsafe (unsafePerformIO)\n"
        "import qualified Crypto.Hash.SHA256 as SHA256")
    source = exactly_once(source,
        "import System.IO (hClose, openBinaryTempFile)",
        "import System.IO (Handle, hClose, hIsClosed, openBinaryTempFile)")
    source = exactly_once(source, "Right (tempPath, handle) -> do",
        "Right (tempPath, handle) -> do\n"
        "          writeIORef testStagedHandle (Just handle)")
    source = exactly_once(source, needle, fault)
    source += (
        "\n{-# NOINLINE testStagedHandle #-}\n"
        "testStagedHandle :: IORef (Maybe Handle)\n"
        "testStagedHandle = unsafePerformIO (newIORef Nothing)\n\n"
        "testStagedHandleClosed :: IO Bool\n"
        "testStagedHandleClosed = do\n"
        "  current <- readIORef testStagedHandle\n"
        "  case current of\n"
        "    Just handle -> hIsClosed handle\n"
        "    Nothing -> ioError (userError \"test handle anchor not populated\")\n"
    )
    destination = work / label / "Phil" / "Compiler" / "SteveCAS.hs"
    destination.write_text(source)
PY

build_worker() {
  local variant="$1"
  mkdir -p "$work/build-$variant"
  cabal exec -- ghc -fforce-recomp -DTEST_CAS_PRE_CLOSE -i"$work/$variant" -isrc \
    -outputdir "$work/build-$variant" -Wall -Werror -rtsopts \
    -package bytestring -package text -package directory \
    -package unix -package cryptohash-sha256 \
    test/Phase1AuditSteveCASCleanupWorker.hs -o "$work/$variant-worker" \
    2>&1 | tee "$work/build-$variant.log"
  # Confirm GHC actually compiled the instrumented source copy.
  grep -Fq "$work/$variant/Phil/Compiler/SteveCAS.hs" "$work/build-$variant.log"
}

# An assertion failure is counted ONLY if it identifies the open descriptor.
# A missing toolchain, bad instrumentation, or unrelated worker failure is red.
build_worker baseline
mkdir -p "$work/store-baseline"
set +e
baseline_output="$("$work/baseline-worker" "$work/store-baseline" injected +RTS -A128m -RTS 2>&1)"
baseline_status=$?
set -e
if [[ "$baseline_status" -eq 0 ]] || \
   ! grep -Fq 'temporary CAS handle survived failed hPut:' <<<"$baseline_output"; then
  printf 'Unexpected baseline outcome (exit=%s):\n%s\n' \
    "$baseline_status" "$baseline_output" >&2
  exit 1
fi
echo 'PASS: pinned original source retains a live descriptor on pre-close fault'

build_worker repaired
mkdir -p "$work/store-repaired"
"$work/repaired-worker" "$work/store-repaired" injected +RTS -A128m -RTS

# Separately require real-failure/no-replacement behavior without incorrectly
# claiming RLIMIT tells us whether hPut or hClose raised the IOException.
mkdir -p "$work/build-live" "$work/store-live"
cabal exec -- ghc -fforce-recomp -isrc -outputdir "$work/build-live" \
  -Wall -Werror -rtsopts \
  -package bytestring -package text -package directory \
  -package unix -package cryptohash-sha256 \
  test/Phase1AuditSteveCASCleanupWorker.hs -o "$work/live-worker"
(
  ulimit -f 0
  trap '' XFSZ
  "$work/live-worker" "$work/store-live" real +RTS -A128m -RTS
)
