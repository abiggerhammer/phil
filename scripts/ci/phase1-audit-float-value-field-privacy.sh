#!/usr/bin/env bash
# FLOAT-BOUNDARY: external clients must read FloatValue without being able
# to replace its representation fields.
set -euo pipefail
cd "$(dirname "$0")/../.."
scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT

cat > "$scratch/ReadFloat.hs" <<'HS'
module ReadFloat where
import Phil.Core.FloatArithmetic
  ( FloatValue, FloatFormat (..), floatBits, floatFormat, floatFromBits )
import Data.Word (Word64)

readFormat :: FloatValue -> FloatFormat
readFormat = floatFormat

readBits :: FloatValue -> Word64
readBits = floatBits

construct :: Word64 -> Bool
construct bits = case floatFromBits Float32 bits of
  Right value -> readFormat value == Float32
  Left _ -> False
HS
# All positive reads must compile before negative cases are interpreted.
cabal exec -- ghc -isrc -fno-code "$scratch/ReadFloat.hs"

for field in floatFormat floatBits; do
  cat > "$scratch/ForgeFloat.hs" <<HS
module ForgeFloat where
import Phil.Core.FloatArithmetic (FloatValue, $field)
forge :: FloatValue -> FloatValue
forge value = value { $field = undefined }
HS
  if cabal exec -- ghc -isrc -fno-code "$scratch/ForgeFloat.hs" >"$scratch/out" 2>&1; then
    echo "FAIL: exported $field permitted an external FloatValue update" >&2
    exit 1
  fi
  if ! grep -Fq "$field" "$scratch/out" || ! grep -Eiq 'not a record selector|not in scope|not a record field|not a field' "$scratch/out"; then
    echo "FAIL: $field negative compilation failed for an unexpected reason" >&2
    cat "$scratch/out" >&2
    exit 1
  fi
  echo "PASS: external FloatValue record update rejected: $field"
done

cabal exec -- runghc -Wall -Werror -isrc test/Phase1AuditFloatValueFieldPrivacyMain.hs
cabal exec -- runghc -Wall -Werror -isrc test/Phase1FloatArithmeticCoreMain.hs
cabal exec -- runghc -Wall -Werror -isrc test/Phase1NumericConversionMain.hs
