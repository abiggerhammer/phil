#!/usr/bin/env bash
set -euo pipefail

resolve_llvm_tool() {
  local tool="$1"
  local versioned="${tool}-18"

  if command -v "$versioned" >/dev/null 2>&1; then
    printf '%s\n' "$versioned"
    return 0
  fi

  if command -v "$tool" >/dev/null 2>&1 \
      && "$tool" --version | head -n 1 | grep -Eq 'LLVM version 18([.]|$)'; then
    printf '%s\n' "$tool"
    return 0
  fi

  echo "LLVM 18 ${tool} is required" >&2
  return 1
}

LLVM_AS="$(resolve_llvm_tool llvm-as)"
LLVM_LINK="$(resolve_llvm_tool llvm-link)"
LLVM_DIS="$(resolve_llvm_tool llvm-dis)"

if command -v clang-18 >/dev/null 2>&1; then
  CLANG=clang-18
elif command -v clang >/dev/null 2>&1 \
    && clang --version | head -n 1 | grep -Eq 'clang version 18([.]|$)'; then
  CLANG=clang
else
  echo 'Clang 18 is required' >&2
  exit 1
fi

export LLVM_AS LLVM_LINK LLVM_DIS CLANG

echo "LLVM_AS=${LLVM_AS}"
echo "LLVM_LINK=${LLVM_LINK}"
echo "LLVM_DIS=${LLVM_DIS}"
echo "CLANG=${CLANG}"
