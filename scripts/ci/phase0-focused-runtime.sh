#!/usr/bin/env bash
set -euo pipefail

PROFILE="${1:?usage: phase0-focused-runtime.sh <storage|accepted-response|rejected-response|exact-send>}"
PHIL_LLVM18_TOOLS="llvm-as llvm-link clang"
source scripts/ci/resolve-llvm18.sh
unset PHIL_LLVM18_TOOLS

case "$PROFILE" in
  storage)
    cabal build phil-llvm-phase0-storage phil-storage-abi-tests

    STORAGE_EMITTER="$(cabal list-bin phil-llvm-phase0-storage)"
    "$STORAGE_EMITTER" > phase0-upload-storage.ll
    "$LLVM_AS" phase0-upload-storage.ll -o phase0-upload-storage.bc

    "$CLANG" --target=x86_64-unknown-linux-gnu \
      -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -Iruntime/phase0 -S -emit-llvm \
      runtime/phase0/storage_v1_smoke.c \
      -o storage-runtime.ll

    python3 scripts/check_runtime_abi.py \
      phase0-upload-storage.ll \
      storage-runtime.ll
    "$LLVM_AS" storage-runtime.ll -o storage-runtime.bc

    "$CLANG" --target=x86_64-unknown-linux-gnu \
      -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -Iruntime/phase0 -emit-llvm -c \
      runtime/phase0/storage_v1_smoke_main.c \
      -o storage-smoke-main.bc

    "$LLVM_LINK" \
      phase0-upload-storage.bc \
      storage-runtime.bc \
      storage-smoke-main.bc \
      -o phase0-upload-storage-linked.bc

    "$CLANG" --target=x86_64-unknown-linux-gnu \
      phase0-upload-storage-linked.bc \
      -lcrypto \
      -o phase0-upload-storage-smoke
    ./phase0-upload-storage-smoke

    "$CLANG" --target=x86_64-unknown-linux-gnu \
      -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -S -emit-llvm \
      runtime/phase0/storage_v1_bad_ambient.c \
      -o storage-bad-ambient.ll
    if python3 scripts/check_runtime_abi.py --partial \
        phase0-upload-storage.ll \
        storage-bad-ambient.ll; then
      echo "expected ABI checker to reject nullary/bool storage provider" >&2
      exit 1
    fi
    echo "PASS: runtime ABI checker rejects ambient nullary storage"

    "$LLVM_AS" --version | head -n 1
    "$CLANG" --version | head -n 1
    ;;

  accepted-response)
    cabal build phil-llvm-phase0-accepted-response phil-accepted-response-abi-tests

    EMITTER="$(cabal list-bin phil-llvm-phase0-accepted-response)"
    "$EMITTER" > phase0-upload-accepted-response.ll
    "$LLVM_AS" phase0-upload-accepted-response.ll -o phase0-upload-accepted-response.bc

    "$CLANG" --target=x86_64-unknown-linux-gnu \
      -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -Iruntime/phase0 -S -emit-llvm \
      runtime/phase0/accepted_response_v1_smoke.c \
      -o accepted-response-runtime.ll

    python3 scripts/check_runtime_abi.py \
      phase0-upload-accepted-response.ll \
      accepted-response-runtime.ll
    "$LLVM_AS" accepted-response-runtime.ll -o accepted-response-runtime.bc

    "$CLANG" --target=x86_64-unknown-linux-gnu \
      -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -Iruntime/phase0 -emit-llvm -c \
      runtime/phase0/accepted_response_v1_smoke_main.c \
      -o accepted-response-smoke-main.bc

    "$LLVM_LINK" \
      phase0-upload-accepted-response.bc \
      accepted-response-runtime.bc \
      accepted-response-smoke-main.bc \
      -o phase0-upload-accepted-response-linked.bc

    "$CLANG" --target=x86_64-unknown-linux-gnu \
      phase0-upload-accepted-response-linked.bc \
      -lcrypto \
      -o phase0-upload-accepted-response-smoke
    ./phase0-upload-accepted-response-smoke

    "$CLANG" --target=x86_64-unknown-linux-gnu \
      -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -S -emit-llvm \
      runtime/phase0/accepted_response_v1_bad_ambient.c \
      -o accepted-response-bad-ambient.ll
    if python3 scripts/check_runtime_abi.py --partial \
        phase0-upload-accepted-response.ll \
        accepted-response-bad-ambient.ll; then
      echo "expected ABI checker to reject nullary accepted-response provider" >&2
      exit 1
    fi
    echo "PASS: runtime ABI checker rejects ambient nullary accepted-response encoding"

    "$LLVM_AS" --version | head -n 1
    "$CLANG" --version | head -n 1
    ;;

  rejected-response)
    cabal build phil-llvm-phase0-rejected-response phil-rejected-response-abi-tests

    EMITTER="$(cabal list-bin phil-llvm-phase0-rejected-response)"
    "$EMITTER" > phase0-upload-rejected-response.ll
    "$LLVM_AS" phase0-upload-rejected-response.ll -o phase0-upload-rejected-response.bc

    "$CLANG" --target=x86_64-unknown-linux-gnu \
      -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -Iruntime/phase0 -S -emit-llvm \
      runtime/phase0/rejected_response_v1_smoke.c \
      -o rejected-response-runtime.ll

    python3 scripts/check_runtime_abi.py \
      phase0-upload-rejected-response.ll \
      rejected-response-runtime.ll
    "$LLVM_AS" rejected-response-runtime.ll -o rejected-response-runtime.bc

    "$CLANG" --target=x86_64-unknown-linux-gnu \
      -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -Iruntime/phase0 -emit-llvm -c \
      runtime/phase0/rejected_response_v1_smoke_main.c \
      -o rejected-response-smoke-main.bc

    "$LLVM_LINK" \
      phase0-upload-rejected-response.bc \
      rejected-response-runtime.bc \
      rejected-response-smoke-main.bc \
      -o phase0-upload-rejected-response-linked.bc

    "$CLANG" --target=x86_64-unknown-linux-gnu \
      phase0-upload-rejected-response-linked.bc \
      -lcrypto \
      -o phase0-upload-rejected-response-smoke
    ./phase0-upload-rejected-response-smoke

    "$CLANG" --target=x86_64-unknown-linux-gnu \
      -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -S -emit-llvm \
      runtime/phase0/rejected_response_v1_bad_ambient.c \
      -o rejected-response-bad-ambient.ll
    if python3 scripts/check_runtime_abi.py --partial \
        phase0-upload-rejected-response.ll \
        rejected-response-bad-ambient.ll; then
      echo "expected ABI checker to reject nullary rejected-response provider" >&2
      exit 1
    fi
    echo "PASS: runtime ABI checker rejects ambient nullary rejected-response encoding"

    "$LLVM_AS" --version | head -n 1
    "$CLANG" --version | head -n 1
    ;;

  exact-send)
    cabal build phil-llvm-phase0-exact-send phil-exact-send-abi-tests

    EMITTER="$(cabal list-bin phil-llvm-phase0-exact-send)"
    "$EMITTER" > phase0-exact-send.ll
    "$LLVM_AS" phase0-exact-send.ll -o phase0-exact-send.bc

    "$CLANG" --target=x86_64-unknown-linux-gnu \
      -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -Iruntime/phase0 -S -emit-llvm \
      runtime/phase0/exact_send_v1_smoke.c \
      -o exact-send-runtime.ll
    python3 scripts/check_runtime_abi.py --partial \
      phase0-exact-send.ll exact-send-runtime.ll
    "$LLVM_AS" exact-send-runtime.ll -o exact-send-runtime.bc
    "$LLVM_LINK" phase0-exact-send.bc exact-send-runtime.bc \
      -o phase0-exact-send-partially-linked.bc

    "$CLANG" --target=x86_64-unknown-linux-gnu \
      -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -Iruntime/phase0 \
      runtime/phase0/exact_send_v1_smoke.c \
      runtime/phase0/exact_send_v1_smoke_main.c \
      -o exact-send-smoke
    ./exact-send-smoke

    "$CLANG" --target=x86_64-unknown-linux-gnu \
      -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -S -emit-llvm runtime/phase0/exact_send_v1_bad_ambient.c \
      -o exact-send-bad-ambient.ll
    if python3 scripts/check_runtime_abi.py --partial \
        phase0-exact-send.ll exact-send-bad-ambient.ll; then
      echo "expected ABI checker to reject ambient/nullary exact-send provider" >&2
      exit 1
    fi

    cabal test phil-exact-send-abi-tests --test-show-details=direct
    ;;

  *)
    echo "unknown focused Phase 0 runtime profile: ${PROFILE}" >&2
    exit 2
    ;;
esac
