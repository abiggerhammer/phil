#!/usr/bin/env bash
set -euo pipefail

profile="${1:?usage: phase0-assurance-meta-rocq.sh PROFILE}"
export PATH="/home/rocq/.opam/${COMPILER}/bin:$PATH"

rm -rf checked
mkdir -p checked/proof/Phil/Assurance

check_and_stage() {
  local theorem="$1"
  rocq c -Q proof/Phil Phil "proof/Phil/Assurance/${theorem}.v"
  cp "proof/Phil/Assurance/${theorem}.v" checked/proof/Phil/Assurance/
  cp "proof/Phil/Assurance/${theorem}.vo" checked/proof/Phil/Assurance/
}

case "$profile" in
  ledger-extension)
    rocq c -Q proof/Phil Phil proof/Phil/Assurance/Manifest.v
    rocq c -Q proof/Phil Phil proof/Phil/Assurance/EvidenceUse.v
    check_and_stage LedgerExtension
    ;;
  lineage-authority)
    check_and_stage LineageAuthority
    ;;
  validity-scope)
    check_and_stage ValidityScope
    ;;
  *)
    echo "unknown assurance meta-proof profile: $profile" >&2
    exit 2
    ;;
esac
