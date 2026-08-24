#!/usr/bin/env bash
set -euo pipefail

PROFILE="${1:?usage: phase0-control-runtime.sh <hello-policy-validation|begin-policy-choice|version-session-choice|payload-cancel-choice>}"
PHIL_LLVM18_TOOLS="llvm-as llvm-link clang"
source scripts/ci/resolve-llvm18.sh
unset PHIL_LLVM18_TOOLS

case "$PROFILE" in
  hello-policy-validation)
    cabal build phil-llvm-phase0-hello-policy-validation phil-hello-policy-validation-abi-tests

    EMITTER="$(cabal list-bin phil-llvm-phase0-hello-policy-validation)"
    "$EMITTER" > phase0-hello-policy-validation.ll
    "$LLVM_AS" phase0-hello-policy-validation.ll -o phase0-hello-policy-validation.bc

    "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -Iruntime/phase0 -S -emit-llvm runtime/phase0/hello_policy_validation_v1_smoke.c \
      -o hello-policy-runtime.ll
    python3 scripts/check_runtime_abi.py --partial \
      phase0-hello-policy-validation.ll hello-policy-runtime.ll
    "$LLVM_AS" hello-policy-runtime.ll -o hello-policy-runtime.bc
    "$LLVM_LINK" phase0-hello-policy-validation.bc hello-policy-runtime.bc \
      -o phase0-hello-policy-validation-partially-linked.bc

    "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -Iruntime/phase0 \
      runtime/phase0/hello_policy_validation_v1_smoke.c \
      runtime/phase0/hello_policy_validation_v1_smoke_main.c \
      -o hello-policy-validation-smoke
    ./hello-policy-validation-smoke

    "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -S -emit-llvm runtime/phase0/hello_policy_validation_v1_bad_ambient.c \
      -o hello-policy-bad-ambient.ll
    if python3 scripts/check_runtime_abi.py --partial \
        phase0-hello-policy-validation.ll hello-policy-bad-ambient.ll; then
      echo "expected ABI checker to reject ambient/nullary HelloPolicy provider" >&2
      exit 1
    fi

    cabal test phil-hello-policy-validation-abi-tests
    ;;

  begin-policy-choice)
    cabal build phil-llvm-phase0-begin-policy-choice phil-begin-policy-choice-abi-tests

    EMITTER="$(cabal list-bin phil-llvm-phase0-begin-policy-choice)"
    "$EMITTER" > phase0-begin-policy-choice.ll
    "$LLVM_AS" phase0-begin-policy-choice.ll -o phase0-begin-policy-choice.bc

    "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -Iruntime/phase0 -S -emit-llvm runtime/phase0/begin_policy_choice_v1_smoke.c \
      -o begin-policy-runtime.ll
    python3 scripts/check_runtime_abi.py --partial \
      phase0-begin-policy-choice.ll begin-policy-runtime.ll
    "$LLVM_AS" begin-policy-runtime.ll -o begin-policy-runtime.bc
    "$LLVM_LINK" phase0-begin-policy-choice.bc begin-policy-runtime.bc \
      -o phase0-begin-policy-choice-partially-linked.bc

    "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -Iruntime/phase0 \
      runtime/phase0/begin_policy_choice_v1_smoke.c \
      runtime/phase0/begin_policy_choice_v1_smoke_main.c \
      -o begin-policy-choice-smoke
    ./begin-policy-choice-smoke

    "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -S -emit-llvm runtime/phase0/begin_policy_choice_v1_bad_ambient.c \
      -o begin-policy-bad-ambient.ll
    if python3 scripts/check_runtime_abi.py --partial \
        phase0-begin-policy-choice.ll begin-policy-bad-ambient.ll; then
      echo "expected ABI checker to reject ambient/nullary BeginPolicy provider" >&2
      exit 1
    fi

    cabal test phil-begin-policy-choice-abi-tests
    ;;

  version-session-choice)
    cabal build phil-llvm-phase0-version-session-choice phil-version-session-choice-abi-tests

    EMITTER="$(cabal list-bin phil-llvm-phase0-version-session-choice)"
    "$EMITTER" > phase0-version-session-choice.ll
    "$LLVM_AS" phase0-version-session-choice.ll -o phase0-version-session-choice.bc

    "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -Iruntime/phase0 -S -emit-llvm runtime/phase0/version_session_choice_v1_smoke.c \
      -o version-session-runtime.ll
    python3 scripts/check_runtime_abi.py --partial \
      phase0-version-session-choice.ll version-session-runtime.ll
    "$LLVM_AS" version-session-runtime.ll -o version-session-runtime.bc
    "$LLVM_LINK" phase0-version-session-choice.bc version-session-runtime.bc \
      -o phase0-version-session-choice-partially-linked.bc

    "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -Iruntime/phase0 \
      runtime/phase0/version_session_choice_v1_smoke.c \
      runtime/phase0/version_session_choice_v1_smoke_main.c \
      -o version-session-choice-smoke
    ./version-session-choice-smoke

    "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -S -emit-llvm runtime/phase0/version_session_choice_v1_bad_ambient.c \
      -o version-session-bad-ambient.ll
    if python3 scripts/check_runtime_abi.py --partial \
        phase0-version-session-choice.ll version-session-bad-ambient.ll; then
      echo "expected ABI checker to reject ambient/nullary version-choice provider" >&2
      exit 1
    fi

    cabal test phil-version-session-choice-abi-tests
    ;;

  payload-cancel-choice)
    cabal build phil-llvm-phase0-payload-cancel-choice phil-payload-cancel-choice-abi-tests

    EMITTER="$(cabal list-bin phil-llvm-phase0-payload-cancel-choice)"
    "$EMITTER" > phase0-payload-cancel-choice.ll
    "$LLVM_AS" phase0-payload-cancel-choice.ll -o phase0-payload-cancel-choice.bc

    "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -Iruntime/phase0 -S -emit-llvm runtime/phase0/payload_cancel_choice_v1_smoke.c \
      -o payload-cancel-runtime.ll
    python3 scripts/check_runtime_abi.py \
      phase0-payload-cancel-choice.ll payload-cancel-runtime.ll
    "$LLVM_AS" payload-cancel-runtime.ll -o payload-cancel-runtime.bc

    "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -Iruntime/phase0 -emit-llvm -c runtime/phase0/payload_cancel_choice_v1_smoke_main.c \
      -o payload-cancel-smoke-main.bc
    "$LLVM_LINK" phase0-payload-cancel-choice.bc payload-cancel-runtime.bc payload-cancel-smoke-main.bc \
      -o phase0-payload-cancel-linked.bc
    "$CLANG" --target=x86_64-unknown-linux-gnu phase0-payload-cancel-linked.bc \
      -o phase0-payload-cancel-smoke
    ./phase0-payload-cancel-smoke

    "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
      -S -emit-llvm runtime/phase0/payload_cancel_choice_v1_bad_ambient.c \
      -o payload-cancel-bad-ambient.ll
    if python3 scripts/check_runtime_abi.py --partial \
        phase0-payload-cancel-choice.ll payload-cancel-bad-ambient.ll; then
      echo "expected ABI checker to reject ambient/nullary payload-cancel provider" >&2
      exit 1
    fi

    cabal test phil-payload-cancel-choice-abi-tests
    ;;

  *)
    echo "unknown Phase 0 control runtime profile: ${PROFILE}" >&2
    exit 2
    ;;
esac
