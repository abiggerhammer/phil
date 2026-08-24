#!/usr/bin/env bash
set -euo pipefail

profile="${1:?usage: phase0-response-chain-certify.sh PROFILE}"

cabal build phil-certify-storage
CERTIFIER="$(cabal list-bin phil-certify-storage)"

case "$profile" in
  accepted-response)
    root=rocq-accepted
    certificate_dir=accepted-response-certificates
    args=(
      "$root/systems-accepted-response/AcceptedResponse.v"
      "$root/systems-accepted-response/AcceptedResponse.vo"
      "$root/llvm-accepted-response/AcceptedResponse.v"
      "$root/llvm-accepted-response/AcceptedResponse.vo"
      "$root/systems-storage/Storage.v"
      "$root/systems-storage/Storage.vo"
      "$root/llvm-storage/Storage.v"
      "$root/llvm-storage/Storage.vo"
      "$root/systems-digest-validation/DigestValidation.v"
      "$root/systems-digest-validation/DigestValidation.vo"
      "$root/llvm-digest-validation/DigestValidation.v"
      "$root/llvm-digest-validation/DigestValidation.vo"
      "$root/systems-recognized-record/RecognizedRecord.v"
      "$root/systems-recognized-record/RecognizedRecord.vo"
      "$root/llvm-exact-receive/ExactReceive.v"
      "$root/llvm-exact-receive/ExactReceive.vo"
      "$root/llvm-recognized-record-abi/RecognizedRecordABI.v"
      "$root/llvm-recognized-record-abi/RecognizedRecordABI.vo"
      "$root/llvm-runtime-symbol-identity/RuntimeSymbolIdentity.v"
      "$root/llvm-runtime-symbol-identity/RuntimeSymbolIdentity.vo"
      "$certificate_dir/PHIL-SYS-ACCEPTED-001.rocq.cert"
      "$certificate_dir/PHIL-LLVM-ACCEPTED-001.rocq.cert"
      "$certificate_dir/PHIL-SYS-STORAGE-001.rocq.cert"
      "$certificate_dir/PHIL-LLVM-STORAGE-001.rocq.cert"
      "$certificate_dir/PHIL-SYS-DIGEST-001.rocq.cert"
      "$certificate_dir/PHIL-LLVM-DIGEST-001.rocq.cert"
      "$certificate_dir/PHIL-SYS-RECORD-001.rocq.cert"
      "$certificate_dir/PHIL-LLVM-EXACT-RECV-001.rocq.cert"
      "$certificate_dir/PHIL-LLVM-REC-ABI-001.rocq.cert"
      "$certificate_dir/PHIL-LLVM-RUNTIME-SYM-001.rocq.cert"
      "$certificate_dir/PHIL-LLVM-CERT-005.cert"
      "$certificate_dir/PHIL-LLVM-CERT-006.cert"
    )
    ;;
  rejected-response)
    root=rocq-rejected
    certificate_dir=rejected-response-certificates
    args=(
      "$root/systems-rejected-response/RejectedResponse.v"
      "$root/systems-rejected-response/RejectedResponse.vo"
      "$root/llvm-rejected-response/RejectedResponse.v"
      "$root/llvm-rejected-response/RejectedResponse.vo"
      "$root/systems-accepted-response/AcceptedResponse.v"
      "$root/systems-accepted-response/AcceptedResponse.vo"
      "$root/llvm-accepted-response/AcceptedResponse.v"
      "$root/llvm-accepted-response/AcceptedResponse.vo"
      "$root/systems-storage/Storage.v"
      "$root/systems-storage/Storage.vo"
      "$root/llvm-storage/Storage.v"
      "$root/llvm-storage/Storage.vo"
      "$root/systems-digest-validation/DigestValidation.v"
      "$root/systems-digest-validation/DigestValidation.vo"
      "$root/llvm-digest-validation/DigestValidation.v"
      "$root/llvm-digest-validation/DigestValidation.vo"
      "$root/systems-recognized-record/RecognizedRecord.v"
      "$root/systems-recognized-record/RecognizedRecord.vo"
      "$root/llvm-exact-receive/ExactReceive.v"
      "$root/llvm-exact-receive/ExactReceive.vo"
      "$root/llvm-recognized-record-abi/RecognizedRecordABI.v"
      "$root/llvm-recognized-record-abi/RecognizedRecordABI.vo"
      "$root/llvm-runtime-symbol-identity/RuntimeSymbolIdentity.v"
      "$root/llvm-runtime-symbol-identity/RuntimeSymbolIdentity.vo"
      "$certificate_dir/PHIL-SYS-REJECTED-001.rocq.cert"
      "$certificate_dir/PHIL-LLVM-REJECTED-001.rocq.cert"
      "$certificate_dir/PHIL-SYS-ACCEPTED-001.rocq.cert"
      "$certificate_dir/PHIL-LLVM-ACCEPTED-001.rocq.cert"
      "$certificate_dir/PHIL-SYS-STORAGE-001.rocq.cert"
      "$certificate_dir/PHIL-LLVM-STORAGE-001.rocq.cert"
      "$certificate_dir/PHIL-SYS-DIGEST-001.rocq.cert"
      "$certificate_dir/PHIL-LLVM-DIGEST-001.rocq.cert"
      "$certificate_dir/PHIL-SYS-RECORD-001.rocq.cert"
      "$certificate_dir/PHIL-LLVM-EXACT-RECV-001.rocq.cert"
      "$certificate_dir/PHIL-LLVM-REC-ABI-001.rocq.cert"
      "$certificate_dir/PHIL-LLVM-RUNTIME-SYM-001.rocq.cert"
      "$certificate_dir/PHIL-LLVM-CERT-006.cert"
      "$certificate_dir/PHIL-LLVM-CERT-007.cert"
    )
    ;;
  final-response)
    root=rocq-final
    certificate_dir=final-response-certificates
    args=(
      "$root/systems-final-response/FinalResponse.v"
      "$root/systems-final-response/FinalResponse.vo"
      "$root/llvm-final-response/FinalResponseReceive.v"
      "$root/llvm-final-response/FinalResponseReceive.vo"
      "$root/systems-rejected-response/RejectedResponse.v"
      "$root/systems-rejected-response/RejectedResponse.vo"
      "$root/llvm-rejected-response/RejectedResponse.v"
      "$root/llvm-rejected-response/RejectedResponse.vo"
      "$root/systems-accepted-response/AcceptedResponse.v"
      "$root/systems-accepted-response/AcceptedResponse.vo"
      "$root/llvm-accepted-response/AcceptedResponse.v"
      "$root/llvm-accepted-response/AcceptedResponse.vo"
      "$root/systems-storage/Storage.v"
      "$root/systems-storage/Storage.vo"
      "$root/llvm-storage/Storage.v"
      "$root/llvm-storage/Storage.vo"
      "$root/systems-digest-validation/DigestValidation.v"
      "$root/systems-digest-validation/DigestValidation.vo"
      "$root/llvm-digest-validation/DigestValidation.v"
      "$root/llvm-digest-validation/DigestValidation.vo"
      "$root/systems-recognized-record/RecognizedRecord.v"
      "$root/systems-recognized-record/RecognizedRecord.vo"
      "$root/llvm-exact-receive/ExactReceive.v"
      "$root/llvm-exact-receive/ExactReceive.vo"
      "$root/llvm-recognized-record-abi/RecognizedRecordABI.v"
      "$root/llvm-recognized-record-abi/RecognizedRecordABI.vo"
      "$root/llvm-runtime-symbol-identity/RuntimeSymbolIdentity.v"
      "$root/llvm-runtime-symbol-identity/RuntimeSymbolIdentity.vo"
      "$certificate_dir/PHIL-SYS-FINAL-RESPONSE-001.rocq.cert"
      "$certificate_dir/PHIL-LLVM-FINAL-RESPONSE-001.rocq.cert"
      "$certificate_dir/PHIL-SYS-REJECTED-001.rocq.cert"
      "$certificate_dir/PHIL-LLVM-REJECTED-001.rocq.cert"
      "$certificate_dir/PHIL-SYS-ACCEPTED-001.rocq.cert"
      "$certificate_dir/PHIL-LLVM-ACCEPTED-001.rocq.cert"
      "$certificate_dir/PHIL-SYS-STORAGE-001.rocq.cert"
      "$certificate_dir/PHIL-LLVM-STORAGE-001.rocq.cert"
      "$certificate_dir/PHIL-SYS-DIGEST-001.rocq.cert"
      "$certificate_dir/PHIL-LLVM-DIGEST-001.rocq.cert"
      "$certificate_dir/PHIL-SYS-RECORD-001.rocq.cert"
      "$certificate_dir/PHIL-LLVM-EXACT-RECV-001.rocq.cert"
      "$certificate_dir/PHIL-LLVM-REC-ABI-001.rocq.cert"
      "$certificate_dir/PHIL-LLVM-RUNTIME-SYM-001.rocq.cert"
      "$certificate_dir/PHIL-LLVM-CERT-007.cert"
      "$certificate_dir/PHIL-LLVM-CERT-008.cert"
    )
    ;;
  *)
    echo "unknown Phase 0 response proof profile: $profile" >&2
    exit 2
    ;;
esac

mkdir -p "$certificate_dir"
"$CERTIFIER" "${args[@]}"

shopt -s nullglob
certificates=("$certificate_dir"/*)
if (( ${#certificates[@]} == 0 )); then
  echo "no response proof certificates produced for $profile" >&2
  exit 1
fi
for certificate in "${certificates[@]}"; do
  echo "===== ${certificate} ====="
  cat "$certificate"
  sha256sum "$certificate"
done
