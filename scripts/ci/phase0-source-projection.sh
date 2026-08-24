#!/usr/bin/env bash
set -euo pipefail

cabal build \
  lib:phil-phase0-projection \
  exe:phil-phase0-upload-projection \
  test:projection-tests \
  --ghc-options=-Werror

cabal test projection-tests --test-show-details=direct

PROJECTION="$(cabal list-bin exe:phil-phase0-upload-projection)"
"$PROJECTION"
