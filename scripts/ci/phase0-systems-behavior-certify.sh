#!/usr/bin/env bash
set -euo pipefail

profile="${1:?usage: phase0-systems-behavior-certify.sh PROFILE}"

common_ghc_flags=(
  -Wall
  -Wcompat
  -Wincomplete-record-updates
  -Wincomplete-uni-patterns
  -Wredundant-constraints
  -Werror
  -isrc
  -iapp
)

case "$profile" in
  client-outbound)
    tests=(
      phil-client-outbound-semantics-tests
      phil-recognition-failure-detail-tests
    )
    support="src/Phil/Systems/ClientOutboundProofCertification.hs"
    correspondence="app/ClientOutboundProofCorrespondenceMain.hs"
    certifier="app/ClientOutboundProofCertificationMain.hs"
    correspondence_bin="phil-check-client-outbound-proof-correspondence"
    certifier_bin="phil-certify-client-outbound"
    certificate_dir="client-outbound-certificates"
    ;;
  recognition-failure)
    tests=(
      phil-client-outbound-semantics-tests
      phil-recognition-failure-detail-tests
      phil-storage-failure-detail-tests
    )
    support="src/Phil/Systems/RecognitionFailureProofCertification.hs"
    correspondence="app/RecognitionFailureProofCorrespondenceMain.hs"
    certifier="app/RecognitionFailureProofCertificationMain.hs"
    correspondence_bin="phil-check-recognition-failure-proof-correspondence"
    certifier_bin="phil-certify-recognition-failure"
    certificate_dir="recognition-failure-certificates"
    ;;
  storage-failure-detail)
    tests=(
      phil-client-outbound-semantics-tests
      phil-recognition-failure-detail-tests
      phil-storage-failure-detail-tests
    )
    support="src/Phil/Systems/StorageFailureProofCertification.hs"
    correspondence="app/StorageFailureProofCorrespondenceMain.hs"
    certifier="app/StorageFailureProofCertificationMain.hs"
    correspondence_bin="phil-check-storage-failure-proof-correspondence"
    certifier_bin="phil-certify-storage-failure-detail"
    certificate_dir="storage-failure-detail-certificates"
    ;;
  *)
    echo "unknown Phase 0 systems-behavior proof profile: $profile" >&2
    exit 2
    ;;
esac

cabal build lib:phil-core "${tests[@]}"
for test_suite in "${tests[@]}"; do
  cabal test "$test_suite" --test-show-details=direct
done

cabal exec -- ghc "${common_ghc_flags[@]}" -fno-code "$support"
cabal exec -- ghc "${common_ghc_flags[@]}" -fno-code "$correspondence"
cabal exec -- ghc "${common_ghc_flags[@]}" -fno-code "$certifier"

cabal exec -- ghc -O0 -isrc -iapp "$correspondence" -o "$correspondence_bin"
"./$correspondence_bin"

cabal exec -- ghc -O0 -isrc -iapp "$certifier" -o "$certifier_bin"
mkdir -p "$certificate_dir"
"./$certifier_bin"

shopt -s nullglob
certificates=("$certificate_dir"/*)
if (( ${#certificates[@]} == 0 )); then
  echo "no proof certificates produced for $profile" >&2
  exit 1
fi
for certificate in "${certificates[@]}"; do
  echo "===== ${certificate} ====="
  cat "$certificate"
  sha256sum "$certificate"
done
