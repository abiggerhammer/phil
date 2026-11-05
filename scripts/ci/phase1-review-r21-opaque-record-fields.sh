#!/usr/bin/env bash
# R21: exercise the certified record boundary from an external client module.
set -euo pipefail
cd "$(dirname "$0")/../.."
scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT

cat > "$scratch/R21Readable.hs" <<'HS'
module R21Readable where
import Phil.Core.ConcurrencyRendezvousCertification
import Phil.Core.ConcurrencyTerminalCertification

protocolInstance = certifiedRendezvousProtocolInstance
primaryRole = certifiedRendezvousPrimaryRole
peerRole = certifiedRendezvousPeerRole
senderProcess = certifiedRendezvousSenderProcess
receiverProcess = certifiedRendezvousReceiverProcess
resultState = certifiedRendezvousState
resultCausality = certifiedRendezvousCausality
terminalNative = certifiedTerminalDispositionNative
HS
cabal exec -- ghc -isrc -Wall -Werror -fno-code "$scratch/R21Readable.hs"

# A correctly typed external client cannot use any of the public getters
# as a record-update field. Each case must fail mentioning its exact label.
while read -r typename label; do
  cat > "$scratch/R21Forgery.hs" <<HS
module R21Forgery where
import Phil.Core.ConcurrencyRendezvousCertification
import Phil.Core.ConcurrencyTerminalCertification
forged :: $typename -> $typename
forged original = original { $label = undefined }
HS
  if cabal exec -- ghc -isrc -fno-code -fforce-recomp "$scratch/R21Forgery.hs" >"$scratch/out" 2>&1; then
    echo "R21 FAIL: exported update succeeded for $typename.$label" >&2
    exit 1
  fi
  if ! grep -Fq "$label" "$scratch/out"; then
    echo "R21 FAIL: rejected for a reason unrelated to $label" >&2
    cat "$scratch/out" >&2
    exit 1
  fi
  echo "R21: external update rejected: $typename.$label"
done <<'FIELDS'
CertifiedRendezvousProtocol certifiedRendezvousProtocolInstance
CertifiedRendezvousProtocol certifiedRendezvousPrimaryRole
CertifiedRendezvousProtocol certifiedRendezvousPeerRole
CertifiedRendezvousCausality certifiedRendezvousSenderProcess
CertifiedRendezvousCausality certifiedRendezvousReceiverProcess
CertifiedRendezvousResult certifiedRendezvousState
CertifiedRendezvousResult certifiedRendezvousCausality
CertifiedTerminalDisposition certifiedTerminalDispositionNative
FIELDS
