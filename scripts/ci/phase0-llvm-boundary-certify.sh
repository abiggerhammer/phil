#!/usr/bin/env bash
set -euo pipefail

profile="${1:?usage: phase0-llvm-boundary-certify.sh PROFILE}"

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
  client-control-send)
    emitter_target="phil-llvm-phase0-client-control-send"
    primary_test="phil-client-control-send-abi-tests"
    tests=(phil-client-control-send-abi-tests)
    support="src/Phil/LLVM/ClientControlSendProofCertification.hs"
    correspondence="app/ClientControlSendProofCorrespondenceMain.hs"
    certifier="app/ClientControlSendProofCertificationMain.hs"
    correspondence_bin="phil-check-client-control-send-proof-correspondence"
    certifier_bin="phil-certify-client-control-send"
    runtime_slug="client-control-send"
    runtime_stem="client_control_send_v1"
    certificate_dir="client-control-send-certificates"
    bad_provider_message="expected ABI checker to reject ambient/nullary client control-send provider"
    ;;
  server-framed-ingress)
    emitter_target="phil-llvm-phase0-server-framed-ingress"
    primary_test="phil-server-framed-ingress-abi-tests"
    tests=(phil-server-framed-ingress-abi-tests)
    support="src/Phil/LLVM/ServerFramedIngressProofCertification.hs"
    correspondence="app/ServerFramedIngressProofCorrespondenceMain.hs"
    certifier="app/ServerFramedIngressProofCertificationMain.hs"
    correspondence_bin="phil-check-server-framed-ingress-proof-correspondence"
    certifier_bin="phil-certify-server-framed-ingress"
    runtime_slug="server-framed-ingress"
    runtime_stem="server_framed_ingress_v1"
    certificate_dir="server-framed-ingress-certificates"
    bad_provider_message="expected ABI checker to reject ambient/nullary server ingress provider"
    ;;
  storage-failure-detail-lowering)
    emitter_target="phil-llvm-phase0-storage-failure-detail"
    primary_test="phil-storage-failure-detail-abi-tests"
    tests=(
      phil-storage-failure-detail-abi-tests
      phil-server-framed-ingress-abi-tests
      phil-storage-failure-detail-tests
    )
    support="src/Phil/LLVM/StorageFailureDetailProofCertification.hs"
    correspondence="app/StorageFailureDetailProofCorrespondenceMain.hs"
    certifier="app/StorageFailureDetailProofCertificationMain.hs"
    correspondence_bin="phil-check-storage-failure-detail-proof-correspondence"
    certifier_bin="phil-certify-storage-failure-detail"
    runtime_slug="storage-failure-detail"
    runtime_stem="storage_failure_detail_v1"
    certificate_dir="storage-failure-detail-lowering-certificates"
    bad_provider_message="expected ABI checker to reject ambient/nullary storage failure provider"
    ;;
  *)
    echo "unknown Phase 0 LLVM boundary proof profile: $profile" >&2
    exit 2
    ;;
esac

cabal build lib:phil-core "$emitter_target" "$primary_test"
for test_suite in "${tests[@]}"; do
  cabal test "$test_suite" --test-show-details=direct
done

cabal exec -- ghc "${common_ghc_flags[@]}" -fno-code "$support"
cabal exec -- ghc "${common_ghc_flags[@]}" -fno-code "$correspondence"
cabal exec -- ghc "${common_ghc_flags[@]}" -fno-code "$certifier"

cabal exec -- ghc -O0 -isrc -iapp "$correspondence" -o "$correspondence_bin"
"./$correspondence_bin"

LLVM_AS=llvm-as-18
LLVM_LINK=llvm-link-18
CLANG=clang-18
EMITTER="$(cabal list-bin "$emitter_target")"

"$EMITTER" > "phase0-${runtime_slug}.ll"
"$LLVM_AS" "phase0-${runtime_slug}.ll" -o "phase0-${runtime_slug}.bc"

"$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
  -Iruntime/phase0 -S -emit-llvm "runtime/phase0/${runtime_stem}_smoke.c" \
  -o "${runtime_slug}-runtime.ll"
python3 scripts/check_runtime_abi.py --partial \
  "phase0-${runtime_slug}.ll" "${runtime_slug}-runtime.ll"
"$LLVM_AS" "${runtime_slug}-runtime.ll" -o "${runtime_slug}-runtime.bc"
"$LLVM_LINK" "phase0-${runtime_slug}.bc" "${runtime_slug}-runtime.bc" \
  -o "phase0-${runtime_slug}-partially-linked.bc"

"$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
  -Iruntime/phase0 \
  "runtime/phase0/${runtime_stem}_smoke.c" \
  "runtime/phase0/${runtime_stem}_smoke_main.c" \
  -o "${runtime_slug}-smoke"
"./${runtime_slug}-smoke"

"$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
  -S -emit-llvm "runtime/phase0/${runtime_stem}_bad_ambient.c" \
  -o "${runtime_slug}-bad-ambient.ll"
if python3 scripts/check_runtime_abi.py --partial \
    "phase0-${runtime_slug}.ll" "${runtime_slug}-bad-ambient.ll"; then
  echo "$bad_provider_message" >&2
  exit 1
fi

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
