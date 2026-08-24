#!/usr/bin/env bash
set -euo pipefail

PROFILE="${1:?usage: phase0-protocol-runtime.sh <client-control-send|server-framed-ingress|final-response-receive|storage-failure-detail|control-codec>}"
PHIL_LLVM18_TOOLS="llvm-as llvm-link clang"
source scripts/ci/resolve-llvm18.sh
unset PHIL_LLVM18_TOOLS

case "$PROFILE" in
  client-control-send)
    cabal build phil-llvm-phase0-client-control-send phil-client-control-send-abi-tests
    EMITTER="$(cabal list-bin phil-llvm-phase0-client-control-send)"
    "$EMITTER" > phase0-client-control-send.ll
    "$LLVM_AS" phase0-client-control-send.ll -o phase0-client-control-send.bc
    "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -Iruntime/phase0 -S -emit-llvm runtime/phase0/client_control_send_v1_smoke.c \
      -o client-control-send-runtime.ll
    python3 scripts/check_runtime_abi.py --partial phase0-client-control-send.ll client-control-send-runtime.ll
    "$LLVM_AS" client-control-send-runtime.ll -o client-control-send-runtime.bc
    "$LLVM_LINK" phase0-client-control-send.bc client-control-send-runtime.bc \
      -o phase0-client-control-send-partially-linked.bc
    "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -Iruntime/phase0 runtime/phase0/client_control_send_v1_smoke.c \
      runtime/phase0/client_control_send_v1_smoke_main.c -o client-control-send-smoke
    ./client-control-send-smoke
    "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -S -emit-llvm runtime/phase0/client_control_send_v1_bad_ambient.c \
      -o client-control-send-bad-ambient.ll
    if python3 scripts/check_runtime_abi.py --partial phase0-client-control-send.ll client-control-send-bad-ambient.ll; then
      echo "expected ABI checker to reject ambient/nullary client control-send provider" >&2
      exit 1
    fi
    cabal test phil-client-control-send-abi-tests --test-show-details=direct
    ;;

  server-framed-ingress)
    cabal build phil-llvm-phase0-server-framed-ingress phil-server-framed-ingress-abi-tests
    EMITTER="$(cabal list-bin phil-llvm-phase0-server-framed-ingress)"
    "$EMITTER" > phase0-server-framed-ingress.ll
    "$LLVM_AS" phase0-server-framed-ingress.ll -o phase0-server-framed-ingress.bc
    "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -Iruntime/phase0 -S -emit-llvm runtime/phase0/server_framed_ingress_v1_smoke.c \
      -o server-framed-ingress-runtime.ll
    python3 scripts/check_runtime_abi.py --partial phase0-server-framed-ingress.ll server-framed-ingress-runtime.ll
    "$LLVM_AS" server-framed-ingress-runtime.ll -o server-framed-ingress-runtime.bc
    "$LLVM_LINK" phase0-server-framed-ingress.bc server-framed-ingress-runtime.bc \
      -o phase0-server-framed-ingress-partially-linked.bc
    "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -Iruntime/phase0 runtime/phase0/server_framed_ingress_v1_smoke.c \
      runtime/phase0/server_framed_ingress_v1_smoke_main.c -o server-framed-ingress-smoke
    ./server-framed-ingress-smoke
    "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -S -emit-llvm runtime/phase0/server_framed_ingress_v1_bad_ambient.c \
      -o server-framed-ingress-bad-ambient.ll
    if python3 scripts/check_runtime_abi.py --partial phase0-server-framed-ingress.ll server-framed-ingress-bad-ambient.ll; then
      echo "expected ABI checker to reject ambient/nullary server ingress provider" >&2
      exit 1
    fi
    cabal test phil-server-framed-ingress-abi-tests --test-show-details=direct
    ;;

  final-response-receive)
    cabal build phil-llvm-phase0-final-response-receive phil-final-response-receive-tests
    EMITTER="$(cabal list-bin phil-llvm-phase0-final-response-receive)"
    "$EMITTER" > phase0-final-response-receive.ll
    "$LLVM_AS" phase0-final-response-receive.ll -o phase0-final-response-receive.bc
    "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -Iruntime/phase0 -S -emit-llvm runtime/phase0/final_response_receive_v1_smoke.c \
      -o final-response-runtime.ll
    python3 scripts/check_runtime_abi.py phase0-final-response-receive.ll final-response-runtime.ll
    "$LLVM_AS" final-response-runtime.ll -o final-response-runtime.bc
    "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -Iruntime/phase0 -emit-llvm -c runtime/phase0/final_response_receive_v1_smoke_main.c \
      -o final-response-smoke-main.bc
    "$LLVM_LINK" phase0-final-response-receive.bc final-response-runtime.bc final-response-smoke-main.bc \
      -o phase0-final-response-linked.bc
    "$CLANG" --target=x86_64-unknown-linux-gnu phase0-final-response-linked.bc -o phase0-final-response-smoke
    ./phase0-final-response-smoke
    "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -S -emit-llvm runtime/phase0/final_response_receive_v1_bad_ambient.c \
      -o final-response-bad-ambient.ll
    if python3 scripts/check_runtime_abi.py --partial phase0-final-response-receive.ll final-response-bad-ambient.ll; then
      echo "expected ABI checker to reject ambient/nullary final-response decoder" >&2
      exit 1
    fi
    cabal test phil-final-response-receive-tests
    ;;

  storage-failure-detail)
    cabal build phil-llvm-phase0-storage-failure-detail phil-storage-failure-detail-abi-tests
    cabal test phil-storage-failure-detail-abi-tests --test-show-details=direct
    cabal test phil-server-framed-ingress-abi-tests --test-show-details=direct
    cabal test phil-storage-failure-detail-tests --test-show-details=direct
    EMITTER="$(cabal list-bin phil-llvm-phase0-storage-failure-detail)"
    "$EMITTER" > phase0-storage-failure-detail.ll
    "$LLVM_AS" phase0-storage-failure-detail.ll -o phase0-storage-failure-detail.bc
    "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -Iruntime/phase0 -S -emit-llvm runtime/phase0/storage_failure_detail_v1_smoke.c \
      -o storage-failure-detail-runtime.ll
    python3 scripts/check_runtime_abi.py --partial phase0-storage-failure-detail.ll storage-failure-detail-runtime.ll
    "$LLVM_AS" storage-failure-detail-runtime.ll -o storage-failure-detail-runtime.bc
    "$LLVM_LINK" phase0-storage-failure-detail.bc storage-failure-detail-runtime.bc \
      -o phase0-storage-failure-detail-partially-linked.bc
    "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -Iruntime/phase0 runtime/phase0/storage_failure_detail_v1_smoke.c \
      runtime/phase0/storage_failure_detail_v1_smoke_main.c -o storage-failure-detail-smoke
    ./storage-failure-detail-smoke
    "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -S -emit-llvm runtime/phase0/storage_failure_detail_v1_bad_ambient.c \
      -o storage-failure-detail-bad-ambient.ll
    if python3 scripts/check_runtime_abi.py --partial phase0-storage-failure-detail.ll storage-failure-detail-bad-ambient.ll; then
      echo "expected ABI checker to reject ambient/nullary storage failure provider" >&2
      exit 1
    fi
    ;;

  control-codec)
    cabal build phil-llvm-phase0-control-codec phil-control-codec-abi-tests
    cabal test phil-control-codec-abi-tests --test-show-details=direct
    cabal test phil-storage-failure-detail-abi-tests --test-show-details=direct
    cabal test phil-server-framed-ingress-abi-tests --test-show-details=direct
    cabal test phil-client-control-send-abi-tests --test-show-details=direct
    EMITTER="$(cabal list-bin phil-llvm-phase0-control-codec)"
    "$EMITTER" > phase0-control-codec.ll
    "$LLVM_AS" phase0-control-codec.ll -o phase0-control-codec.bc
    "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -Iruntime/phase0 -S -emit-llvm runtime/phase0/control_codec_v1.c \
      -o control-codec-runtime.ll
    python3 scripts/check_runtime_abi.py --partial phase0-control-codec.ll control-codec-runtime.ll
    "$LLVM_AS" control-codec-runtime.ll -o control-codec-runtime.bc
    "$LLVM_LINK" phase0-control-codec.bc control-codec-runtime.bc \
      -o phase0-control-codec-partially-linked.bc
    "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -Iruntime/phase0 runtime/phase0/control_codec_v1.c \
      runtime/phase0/control_codec_v1_smoke.c runtime/phase0/control_codec_v1_smoke_main.c \
      -o control-codec-smoke
    ./control-codec-smoke
    ;;

  *)
    echo "unknown Phase 0 protocol runtime profile: ${PROFILE}" >&2
    exit 2
    ;;
esac
