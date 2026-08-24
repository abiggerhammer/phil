#!/usr/bin/env bash
set -euo pipefail

PROFILE="${1:?usage: phase0-back-certification-certify.sh <profile>}"

GHC_FLAGS=(
  -Wall
  -Wcompat
  -Wincomplete-record-updates
  -Wincomplete-uni-patterns
  -Wredundant-constraints
  -Werror
  -isrc
  -iapp
)

typecheck() {
  cabal exec -- ghc "${GHC_FLAGS[@]}" -fno-code "$1"
}

build_exe() {
  local source="$1"
  local output="$2"
  cabal exec -- ghc -O0 -isrc -iapp "$source" -o "$output"
}

cabal build lib:phil-core

case "$PROFILE" in
  assurance-foundations)
    metadata=src/Phil/Assurance/RocqAssuranceFoundations.hs
    app=app/AssuranceFoundationsBackCertificationMain.hs
    binary=phil-certify-assurance-foundations
    out=assurance-foundations-certificates
    count=6
    ;;
  core-foundations)
    metadata=src/Phil/Assurance/RocqCoreFoundations.hs
    app=app/CoreFoundationsBackCertificationMain.hs
    binary=phil-certify-core-foundations
    out=core-foundations-certificates
    count=6
    ;;
  core-control-assurance)
    metadata=src/Phil/Assurance/RocqCoreControlAssurance.hs
    app=app/CoreControlAssuranceBackCertificationMain.hs
    binary=phil-certify-core-control-assurance
    out=core-control-assurance-certificates
    count=8
    ;;
  focusing-foundations)
    metadata=src/Phil/Assurance/RocqFocusingFoundations.hs
    app=app/FocusingFoundationsBackCertificationMain.hs
    binary=phil-certify-focusing-foundations
    out=focusing-foundations-certificates
    count=5
    ;;
  llvm-foundations)
    metadata=src/Phil/Assurance/RocqLLVMFoundations.hs
    app=app/LLVMFoundationsBackCertificationMain.hs
    binary=phil-certify-llvm-foundations
    out=llvm-foundations-certificates
    count=4
    ;;
  recognition-gates)
    metadata=src/Phil/Assurance/RocqRecognitionGates.hs
    app=app/RecognitionGatesBackCertificationMain.hs
    binary=phil-certify-recognition-gates
    out=recognition-gates-certificates
    count=2
    ;;
  surface-foundations)
    metadata=src/Phil/Assurance/RocqSurfaceFoundations.hs
    app=app/SurfaceFoundationsBackCertificationMain.hs
    binary=phil-certify-surface-foundations
    out=surface-foundations-certificates
    count=7
    ;;
  systems-foundations)
    metadata=src/Phil/Assurance/RocqSystemsFoundations.hs
    app=app/SystemsFoundationsBackCertificationMain.hs
    binary=phil-certify-systems-foundations
    out=systems-foundations-certificates
    count=6
    ;;
  recognition-bundle)
    typecheck src/Phil/Assurance/RocqBundle.hs
    typecheck src/Phil/Assurance/RocqRecognitionBundles.hs
    typecheck app/RecognitionBundleCorrespondenceMain.hs
    typecheck app/RecognitionBundlesBackCertificationMain.hs
    build_exe app/RecognitionBundleCorrespondenceMain.hs phil-check-recognition-bundles
    ./phil-check-recognition-bundles checked
    build_exe app/RecognitionBundlesBackCertificationMain.hs phil-certify-recognition-bundles
    out=recognition-bundle-certificates
    mkdir -p "$out"
    ./phil-certify-recognition-bundles checked "$out"
    test "$(find "$out" -type f -name '*.rocq.cert' | wc -l)" -eq 4
    for certificate in "$out"/*.rocq.cert; do
      cat "$certificate"
      sha256sum "$certificate"
    done
    exit 0
    ;;
  *)
    echo "unknown Phase 0 back-certification profile: ${PROFILE}" >&2
    exit 2
    ;;
esac

typecheck "$metadata"
typecheck "$app"
build_exe "$app" "$binary"
mkdir -p "$out"
./"$binary" checked "$out"
test "$(find "$out" -type f -name '*.rocq.cert' | wc -l)" -eq "$count"
for certificate in "$out"/*.rocq.cert; do
  cat "$certificate"
  sha256sum "$certificate"
done
