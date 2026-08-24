#!/usr/bin/env bash
set -euo pipefail

PROFILE="${1:?usage: phase0-back-certification-rocq.sh <profile>}"
export PATH="/home/rocq/.opam/${COMPILER}/bin:$PATH"

compile() {
  for source in "$@"; do
    rocq c -Q proof/Phil Phil "${source}"
  done
}

stage() {
  local directory="$1"
  shift
  mkdir -p "checked/${directory}"
  for source in "$@"; do
    cp "${source}.v" "checked/${directory}/"
    cp "${source}.vo" "checked/${directory}/"
  done
}

case "$PROFILE" in
  assurance-foundations)
    compile \
      proof/Phil/Assurance/Manifest.v \
      proof/Phil/Assurance/EvidenceUse.v
    stage proof/Phil/Assurance \
      proof/Phil/Assurance/Manifest \
      proof/Phil/Assurance/EvidenceUse
    ;;

  core-foundations)
    compile \
      proof/Phil/Core/Syntax.v \
      proof/Phil/Core/Context.v \
      proof/Phil/Core/ContextJoin.v \
      proof/Phil/Core/Session.v \
      proof/Phil/Core/SessionStep.v \
      proof/Phil/Core/SessionLabel.v
    stage proof/Phil/Core \
      proof/Phil/Core/Context \
      proof/Phil/Core/ContextJoin \
      proof/Phil/Core/Session \
      proof/Phil/Core/SessionStep \
      proof/Phil/Core/SessionLabel
    ;;

  core-control-assurance)
    compile \
      proof/Phil/Core/Syntax.v \
      proof/Phil/Core/Context.v \
      proof/Phil/Core/ContextJoin.v \
      proof/Phil/Core/SessionRec.v \
      proof/Phil/Core/Process.v \
      proof/Phil/Core/ProcessJoin.v \
      proof/Phil/Core/ProcessTerminal.v \
      proof/Phil/Core/Discharge.v \
      proof/Phil/Core/DecisionSound.v
    stage proof/Phil/Core \
      proof/Phil/Core/SessionRec \
      proof/Phil/Core/Process \
      proof/Phil/Core/ProcessJoin \
      proof/Phil/Core/ProcessTerminal \
      proof/Phil/Core/Discharge \
      proof/Phil/Core/DecisionSound
    ;;

  focusing-foundations)
    compile proof/Phil/Core/Focusing.v
    stage proof/Phil/Core proof/Phil/Core/Focusing
    ;;

  llvm-foundations)
    compile \
      proof/Phil/Core/Scalar.v \
      proof/Phil/Systems/Scalar.v \
      proof/Phil/LLVM/Identity.v \
      proof/Phil/LLVM/Preservation.v \
      proof/Phil/LLVM/Strengthening.v \
      proof/Phil/LLVM/Scalar.v
    stage proof/Phil/LLVM \
      proof/Phil/LLVM/Identity \
      proof/Phil/LLVM/Preservation \
      proof/Phil/LLVM/Strengthening \
      proof/Phil/LLVM/Scalar
    ;;

  recognition-bundle)
    compile \
      proof/Phil/Core/Syntax.v \
      proof/Phil/Core/Context.v \
      proof/Phil/Core/SessionStep.v \
      proof/Phil/Core/Recognition.v \
      proof/Phil/Core/RecognitionLoan.v
    stage proof/Phil/Core \
      proof/Phil/Core/Recognition \
      proof/Phil/Core/RecognitionLoan
    ;;

  recognition-gates)
    compile \
      proof/Phil/Core/Syntax.v \
      proof/Phil/Core/Context.v \
      proof/Phil/Core/SessionStep.v \
      proof/Phil/Core/Recognition.v
    stage proof/Phil/Core proof/Phil/Core/Recognition
    ;;

  surface-foundations)
    compile \
      proof/Phil/Core/Syntax.v \
      proof/Phil/Core/Context.v \
      proof/Phil/Core/ContextJoin.v \
      proof/Phil/Core/SessionStep.v \
      proof/Phil/Core/Scalar.v \
      proof/Phil/Surface/Elaboration.v \
      proof/Phil/Surface/Checking.v \
      proof/Phil/Surface/ScopeJoin.v \
      proof/Phil/Surface/FreshOwnership.v \
      proof/Phil/Surface/SystemsProjection.v
    stage proof/Phil/Surface \
      proof/Phil/Surface/Elaboration \
      proof/Phil/Surface/Checking \
      proof/Phil/Surface/ScopeJoin \
      proof/Phil/Surface/FreshOwnership \
      proof/Phil/Surface/SystemsProjection
    ;;

  systems-foundations)
    compile \
      proof/Phil/Core/Scalar.v \
      proof/Phil/Systems/Identity.v \
      proof/Phil/Systems/Ownership.v \
      proof/Phil/Systems/FactDisposition.v \
      proof/Phil/Systems/Runtime.v \
      proof/Phil/Systems/Scalar.v \
      proof/Phil/Systems/ScalarDataflow.v
    stage proof/Phil/Systems \
      proof/Phil/Systems/Identity \
      proof/Phil/Systems/Ownership \
      proof/Phil/Systems/FactDisposition \
      proof/Phil/Systems/Runtime \
      proof/Phil/Systems/Scalar \
      proof/Phil/Systems/ScalarDataflow
    ;;

  *)
    echo "unknown Phase 0 back-certification profile: ${PROFILE}" >&2
    exit 2
    ;;
esac
