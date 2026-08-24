#!/usr/bin/env bash
set -euo pipefail

profile="${1:?usage: phase0-llvm-boundary-rocq.sh PROFILE}"

case "$profile" in
  client-control-send)
    theorem="proof/Phil/LLVM/ClientControlSend.v"
    stage="rocq-client-control-send"
    ;;
  server-framed-ingress)
    theorem="proof/Phil/LLVM/ServerFramedIngress.v"
    stage="rocq-server-framed-ingress"
    ;;
  storage-failure-detail-lowering)
    theorem="proof/Phil/LLVM/StorageFailureDetail.v"
    stage="rocq-storage-failure-detail-lowering"
    ;;
  *)
    echo "unknown Phase 0 LLVM boundary proof profile: $profile" >&2
    exit 2
    ;;
esac

export PATH="/home/rocq/.opam/${COMPILER}/bin:$PATH"
rocq c -Q proof/Phil Phil "$theorem"

mkdir -p "$stage/proof/Phil/LLVM"
cp "$theorem" "${theorem%.v}.vo" "$stage/proof/Phil/LLVM/"
