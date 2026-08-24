#!/usr/bin/env bash
set -euo pipefail

profile="${1:?usage: phase0-assurance-meta-certify.sh PROFILE}"

case "$profile" in
  ledger-extension)
    theorem=LedgerExtension
    correspondence=LedgerExtensionProofCorrespondenceMain.hs
    certifier=LedgerExtensionProofCertificationMain.hs
    check_binary=phil-check-ledger-extension-correspondence
    certify_binary=phil-certify-ledger-extension
    certificate_dir=ledger-extension-certificates
    certificate_name=PHIL-ASSURE-LEDGER-EXT-001.rocq.cert
    ;;
  lineage-authority)
    theorem=LineageAuthority
    correspondence=LineageAuthorityProofCorrespondenceMain.hs
    certifier=LineageAuthorityProofCertificationMain.hs
    check_binary=phil-check-lineage-authority-correspondence
    certify_binary=phil-certify-lineage-authority
    certificate_dir=lineage-authority-certificates
    certificate_name=PHIL-ASSURE-LINEAGE-001.rocq.cert
    ;;
  validity-scope)
    theorem=ValidityScope
    correspondence=ValidityScopeProofCorrespondenceMain.hs
    certifier=ValidityScopeProofCertificationMain.hs
    check_binary=phil-check-validity-scope-correspondence
    certify_binary=phil-certify-validity-scope
    certificate_dir=validity-scope-certificates
    certificate_name=PHIL-ASSURE-VALIDITY-001.rocq.cert
    ;;
  *)
    echo "unknown assurance meta-proof profile: $profile" >&2
    exit 2
    ;;
esac

cabal build lib:phil-core

flags=(
  -Wall
  -Wcompat
  -Wincomplete-record-updates
  -Wincomplete-uni-patterns
  -Wredundant-constraints
  -Werror
  -isrc
  -iapp
  -fno-code
)

cabal exec -- ghc "${flags[@]}" "app/${correspondence}"
cabal exec -- ghc "${flags[@]}" "app/${certifier}"

cabal exec -- ghc -O0 -isrc -iapp "app/${correspondence}" -o "$check_binary"
"./${check_binary}"

cabal exec -- ghc -O0 -isrc -iapp "app/${certifier}" -o "$certify_binary"

mkdir -p "$certificate_dir"
"./${certify_binary}" \
  "checked/proof/Phil/Assurance/${theorem}.v" \
  "checked/proof/Phil/Assurance/${theorem}.vo" \
  "${certificate_dir}/${certificate_name}"

cat "${certificate_dir}/${certificate_name}"
sha256sum "${certificate_dir}/${certificate_name}"
