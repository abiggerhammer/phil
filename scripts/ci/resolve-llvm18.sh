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

resolve_clang() {
  if command -v clang-18 >/dev/null 2>&1; then
    printf '%s\n' clang-18
    return 0
  fi

  if command -v clang >/dev/null 2>&1 \
      && clang --version | head -n 1 | grep -Eq 'clang version 18([.]|$)'; then
    printf '%s\n' clang
    return 0
  fi

  echo 'Clang 18 is required' >&2
  return 1
}

REQUESTED_TOOLS="${PHIL_LLVM18_TOOLS:-llvm-as llvm-link llvm-dis clang}"

for tool in $REQUESTED_TOOLS; do
  case "$tool" in
    llvm-as)
      LLVM_AS="$(resolve_llvm_tool llvm-as)"
      export LLVM_AS
      echo "LLVM_AS=${LLVM_AS}"
      ;;
    llvm-link)
      LLVM_LINK="$(resolve_llvm_tool llvm-link)"
      export LLVM_LINK
      echo "LLVM_LINK=${LLVM_LINK}"
      ;;
    llvm-dis)
      LLVM_DIS="$(resolve_llvm_tool llvm-dis)"
      export LLVM_DIS
      echo "LLVM_DIS=${LLVM_DIS}"
      ;;
    clang)
      CLANG="$(resolve_clang)"
      export CLANG
      echo "CLANG=${CLANG}"
      ;;
    *)
      echo "unknown LLVM 18 tool request: ${tool}" >&2
      exit 1
      ;;
  esac
done
