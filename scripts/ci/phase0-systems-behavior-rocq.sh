#!/usr/bin/env bash
set -euo pipefail

profile="${1:?usage: phase0-systems-behavior-rocq.sh PROFILE}"
export PATH="/home/rocq/.opam/${COMPILER}/bin:$PATH"

case "$profile" in
  client-outbound)
    theorem="proof/Phil/Systems/ClientOutbound.v"
    stage="rocq-client-outbound"
    ;;
  recognition-failure)
    theorem="proof/Phil/Systems/RecognitionFailureDetail.v"
    stage="rocq-recognition-failure"
    ;;
  storage-failure-detail)
    theorem="proof/Phil/Systems/StorageFailureDetail.v"
    stage="rocq-storage-failure-detail"
    ;;
  *)
    echo "unknown Phase 0 systems-behavior proof profile: $profile" >&2
    exit 2
    ;;
esac

rocq c -Q proof/Phil Phil "$theorem"
mkdir -p "$stage/proof/Phil/Systems"
cp "$theorem" "${theorem%.v}.vo" "$stage/proof/Phil/Systems/"
