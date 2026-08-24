#!/usr/bin/env bash
set -euo pipefail

profile="${1:?usage: phase0-response-chain-rocq.sh PROFILE}"
export PATH="/home/rocq/.opam/${COMPILER}/bin:$PATH"

compile() {
  rocq c -Q proof/Phil Phil "$1"
}

common=(
  proof/Phil/Core/Syntax.v
  proof/Phil/Core/Scalar.v
  proof/Phil/Core/Session.v
  proof/Phil/Core/Context.v
  proof/Phil/Core/Process.v
  proof/Phil/Core/SessionLabel.v
  proof/Phil/Core/SessionStep.v
  proof/Phil/Core/Recognition.v
  proof/Phil/Core/RecognitionLoan.v
  proof/Phil/Core/ContextJoin.v
  proof/Phil/Core/ProcessJoin.v
  proof/Phil/Core/ProcessTerminal.v
  proof/Phil/Core/Discharge.v
  proof/Phil/Core/DecisionSound.v
  proof/Phil/Core/SessionRec.v
  proof/Phil/Core/Focusing.v
  proof/Phil/Surface/Elaboration.v
  proof/Phil/Surface/Checking.v
  proof/Phil/Surface/ScopeJoin.v
  proof/Phil/Surface/FreshOwnership.v
  proof/Phil/Surface/SystemsProjection.v
  proof/Phil/Assurance/Manifest.v
  proof/Phil/Assurance/EvidenceUse.v
  proof/Phil/Systems/Identity.v
  proof/Phil/Systems/FactDisposition.v
  proof/Phil/Systems/Ownership.v
  proof/Phil/Systems/Runtime.v
  proof/Phil/Systems/Scalar.v
  proof/Phil/Systems/ScalarDataflow.v
  proof/Phil/Systems/FieldProjection.v
  proof/Phil/Systems/RecognizedRecord.v
  proof/Phil/Systems/DigestValidation.v
  proof/Phil/Systems/Storage.v
)

for source in "${common[@]}"; do
  compile "$source"
done

case "$profile" in
  accepted-response)
    systems_extra=(proof/Phil/Systems/AcceptedResponse.v)
    ;;
  rejected-response)
    systems_extra=(
      proof/Phil/Systems/AcceptedResponse.v
      proof/Phil/Systems/RejectedResponse.v
    )
    ;;
  final-response)
    systems_extra=(
      proof/Phil/Systems/AcceptedResponse.v
      proof/Phil/Systems/RejectedResponse.v
      proof/Phil/Systems/FinalResponse.v
    )
    ;;
  *)
    echo "unknown Phase 0 response proof profile: $profile" >&2
    exit 2
    ;;
esac

for source in "${systems_extra[@]}"; do
  compile "$source"
done

llvm_common=(
  proof/Phil/LLVM/Identity.v
  proof/Phil/LLVM/Preservation.v
  proof/Phil/LLVM/FieldProjection.v
  proof/Phil/LLVM/Strengthening.v
  proof/Phil/LLVM/Certification.v
  proof/Phil/LLVM/Scalar.v
  proof/Phil/LLVM/RecognizedRecordABI.v
  proof/Phil/LLVM/RuntimeSymbolIdentity.v
  proof/Phil/LLVM/RecognizedRecordCertification.v
  proof/Phil/LLVM/ExactReceive.v
  proof/Phil/LLVM/ExactReceiveCertification.v
  proof/Phil/LLVM/DigestValidation.v
  proof/Phil/LLVM/DigestValidationCertification.v
  proof/Phil/LLVM/Storage.v
  proof/Phil/LLVM/StorageCertification.v
)

for source in "${llvm_common[@]}"; do
  compile "$source"
done

case "$profile" in
  accepted-response)
    llvm_extra=(
      proof/Phil/LLVM/AcceptedResponse.v
      proof/Phil/LLVM/AcceptedResponseCertification.v
    )
    root=rocq-accepted
    ;;
  rejected-response)
    llvm_extra=(
      proof/Phil/LLVM/AcceptedResponse.v
      proof/Phil/LLVM/AcceptedResponseCertification.v
      proof/Phil/LLVM/RejectedResponse.v
      proof/Phil/LLVM/RejectedResponseCertification.v
    )
    root=rocq-rejected
    ;;
  final-response)
    llvm_extra=(
      proof/Phil/LLVM/AcceptedResponse.v
      proof/Phil/LLVM/AcceptedResponseCertification.v
      proof/Phil/LLVM/RejectedResponse.v
      proof/Phil/LLVM/RejectedResponseCertification.v
      proof/Phil/LLVM/FinalResponseReceive.v
      proof/Phil/LLVM/FinalResponseReceiveCertification.v
    )
    root=rocq-final
    ;;
esac

for source in "${llvm_extra[@]}"; do
  compile "$source"
done

stage_pair() {
  local source=$1
  local destination=$2
  mkdir -p "$root/$destination"
  cp "$source.v" "$source.vo" "$root/$destination/"
}

case "$profile" in
  accepted-response)
    stage_pair proof/Phil/Systems/AcceptedResponse systems-accepted-response
    stage_pair proof/Phil/LLVM/AcceptedResponse llvm-accepted-response
    ;;
  rejected-response)
    stage_pair proof/Phil/Systems/RejectedResponse systems-rejected-response
    stage_pair proof/Phil/LLVM/RejectedResponse llvm-rejected-response
    stage_pair proof/Phil/Systems/AcceptedResponse systems-accepted-response
    stage_pair proof/Phil/LLVM/AcceptedResponse llvm-accepted-response
    ;;
  final-response)
    stage_pair proof/Phil/Systems/FinalResponse systems-final-response
    stage_pair proof/Phil/LLVM/FinalResponseReceive llvm-final-response
    stage_pair proof/Phil/LLVM/FinalResponseReceiveCertification llvm-final-response-certification
    stage_pair proof/Phil/Systems/RejectedResponse systems-rejected-response
    stage_pair proof/Phil/LLVM/RejectedResponse llvm-rejected-response
    stage_pair proof/Phil/Systems/AcceptedResponse systems-accepted-response
    stage_pair proof/Phil/LLVM/AcceptedResponse llvm-accepted-response
    ;;
esac

stage_pair proof/Phil/Systems/Storage systems-storage
stage_pair proof/Phil/LLVM/Storage llvm-storage
stage_pair proof/Phil/Systems/DigestValidation systems-digest-validation
stage_pair proof/Phil/LLVM/DigestValidation llvm-digest-validation
stage_pair proof/Phil/Systems/RecognizedRecord systems-recognized-record
stage_pair proof/Phil/LLVM/ExactReceive llvm-exact-receive
stage_pair proof/Phil/LLVM/RecognizedRecordABI llvm-recognized-record-abi
stage_pair proof/Phil/LLVM/RuntimeSymbolIdentity llvm-runtime-symbol-identity
