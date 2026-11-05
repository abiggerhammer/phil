#!/usr/bin/env bash
# Phase 1 uses LLVM 18 regardless of the GitHub runner image's default.
set -euo pipefail

if ! command -v llvm-as-18 >/dev/null 2>&1 \
   || ! command -v llvm-link-18 >/dev/null 2>&1 \
   || ! command -v clang-18 >/dev/null 2>&1; then
  sudo apt-get update
  sudo apt-get install -y llvm-18 clang-18
fi

for binary in llvm-as-18 llvm-link-18 clang-18; do
  command -v "$binary"
  "$binary" --version | head -n 2
done

llvm-as-18 --version | grep -Eq 'version 18\\.'
llvm-link-18 --version | grep -Eq 'version 18\\.'
clang-18 --version | grep -Eq 'version 18\\.'
