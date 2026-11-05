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
mkdir -p "$work/store"

cabal exec -- ghc -isrc -Wall -Werror -rtsopts \
  -package bytestring -package text -package directory \
  -package unix -package cryptohash-sha256 \
  test/Phase1AuditSteveCASCleanupWorker.hs -o "$work/cas-cleanup-worker"

(
  ulimit -f 0
  trap '' XFSZ
  "$work/cas-cleanup-worker" "$work/store" +RTS -A128m -RTS
)
