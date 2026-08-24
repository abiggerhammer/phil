#!/usr/bin/env bash
set -euo pipefail

PHIL_LLVM18_TOOLS="llvm-as llvm-link clang"
source scripts/ci/resolve-llvm18.sh
unset PHIL_LLVM18_TOOLS

LLVM_EMITTER="$(cabal list-bin phil-llvm-phase0)"
"$LLVM_EMITTER" > phase0-upload.ll
"$LLVM_AS" phase0-upload.ll -o /dev/null

RECOGNIZED_RECORD_EMITTER="$(cabal list-bin phil-llvm-phase0-recognized-record)"
"$RECOGNIZED_RECORD_EMITTER" > phase0-upload-recognized-record.ll
"$LLVM_AS" phase0-upload-recognized-record.ll -o phase0-upload-recognized-record.bc

"$CLANG" --target=x86_64-unknown-linux-gnu \
  -std=c11 -Wall -Wextra -Wpedantic -Werror \
  -Iruntime/phase0 -S -emit-llvm \
  runtime/phase0/recognized_record_v1_smoke.c \
  -o recognized-record-runtime.ll
python3 scripts/check_runtime_abi.py \
  phase0-upload-recognized-record.ll \
  recognized-record-runtime.ll
"$LLVM_AS" recognized-record-runtime.ll -o recognized-record-runtime.bc

"$CLANG" --target=x86_64-unknown-linux-gnu \
  -std=c11 -Wall -Wextra -Wpedantic -Werror \
  -Iruntime/phase0 -emit-llvm -c \
  runtime/phase0/recognized_record_v1_smoke_main.c \
  -o recognized-record-smoke-main.bc

"$LLVM_LINK" \
  phase0-upload-recognized-record.bc \
  recognized-record-runtime.bc \
  recognized-record-smoke-main.bc \
  -o phase0-upload-recognized-record-linked.bc
"$CLANG" --target=x86_64-unknown-linux-gnu \
  phase0-upload-recognized-record-linked.bc \
  -o phase0-upload-recognized-record-smoke
./phase0-upload-recognized-record-smoke

"$CLANG" --target=x86_64-unknown-linux-gnu \
  -std=c11 -Wall -Wextra -Wpedantic -Werror \
  -S -emit-llvm \
  runtime/phase0/recognized_record_v1_bad_accessor.c \
  -o recognized-record-bad-accessor.ll
if python3 scripts/check_runtime_abi.py --partial \
    phase0-upload-recognized-record.ll \
    recognized-record-bad-accessor.ll; then
  echo "expected ABI checker to reject ptr -> i32 Begin.length accessor" >&2
  exit 1
fi
echo "PASS: runtime ABI checker rejects i64 -> i32 accessor width drift"

EXACT_RECEIVE_EMITTER="$(cabal list-bin phil-llvm-phase0-exact-receive)"
"$EXACT_RECEIVE_EMITTER" > phase0-upload-exact-receive.ll
"$LLVM_AS" phase0-upload-exact-receive.ll -o phase0-upload-exact-receive.bc

"$CLANG" --target=x86_64-unknown-linux-gnu \
  -std=c11 -Wall -Wextra -Wpedantic -Werror \
  -Iruntime/phase0 -S -emit-llvm \
  runtime/phase0/transport_exact_receive_v1_smoke.c \
  -o transport-exact-receive-runtime.ll
python3 scripts/check_runtime_abi.py \
  phase0-upload-exact-receive.ll \
  transport-exact-receive-runtime.ll
"$LLVM_AS" transport-exact-receive-runtime.ll -o transport-exact-receive-runtime.bc

"$CLANG" --target=x86_64-unknown-linux-gnu \
  -std=c11 -Wall -Wextra -Wpedantic -Werror \
  -Iruntime/phase0 -emit-llvm -c \
  runtime/phase0/transport_exact_receive_v1_smoke_main.c \
  -o transport-exact-receive-smoke-main.bc

"$LLVM_LINK" \
  phase0-upload-exact-receive.bc \
  transport-exact-receive-runtime.bc \
  transport-exact-receive-smoke-main.bc \
  -o phase0-upload-exact-receive-linked.bc
"$CLANG" --target=x86_64-unknown-linux-gnu \
  phase0-upload-exact-receive-linked.bc \
  -o phase0-upload-exact-receive-smoke
./phase0-upload-exact-receive-smoke

"$CLANG" --target=x86_64-unknown-linux-gnu \
  -std=c11 -Wall -Wextra -Wpedantic -Werror \
  -S -emit-llvm \
  runtime/phase0/transport_exact_receive_v1_bad_ambient.c \
  -o transport-exact-receive-bad-ambient.ll
if python3 scripts/check_runtime_abi.py --partial \
    phase0-upload-exact-receive.ll \
    transport-exact-receive-bad-ambient.ll; then
  echo "expected ABI checker to reject exact receive without transport operand" >&2
  exit 1
fi
echo "PASS: runtime ABI checker rejects ambient length-only exact receive"

DIGEST_VALIDATION_EMITTER="$(cabal list-bin phil-llvm-phase0-digest-validation)"
"$DIGEST_VALIDATION_EMITTER" > phase0-upload-digest-validation.ll
"$LLVM_AS" phase0-upload-digest-validation.ll -o phase0-upload-digest-validation.bc

"$CLANG" --target=x86_64-unknown-linux-gnu \
  -std=c11 -Wall -Wextra -Wpedantic -Werror \
  -Iruntime/phase0 -S -emit-llvm \
  runtime/phase0/digest_validation_v1_smoke.c \
  -o digest-validation-runtime.ll
python3 scripts/check_runtime_abi.py \
  phase0-upload-digest-validation.ll \
  digest-validation-runtime.ll
"$LLVM_AS" digest-validation-runtime.ll -o digest-validation-runtime.bc

"$CLANG" --target=x86_64-unknown-linux-gnu \
  -std=c11 -Wall -Wextra -Wpedantic -Werror \
  -Iruntime/phase0 -emit-llvm -c \
  runtime/phase0/digest_validation_v1_smoke_main.c \
  -o digest-validation-smoke-main.bc

"$LLVM_LINK" \
  phase0-upload-digest-validation.bc \
  digest-validation-runtime.bc \
  digest-validation-smoke-main.bc \
  -o phase0-upload-digest-validation-linked.bc
"$CLANG" --target=x86_64-unknown-linux-gnu \
  phase0-upload-digest-validation-linked.bc \
  -lcrypto \
  -o phase0-upload-digest-validation-smoke
./phase0-upload-digest-validation-smoke

"$CLANG" --target=x86_64-unknown-linux-gnu \
  -std=c11 -Wall -Wextra -Wpedantic -Werror \
  -S -emit-llvm \
  runtime/phase0/digest_validation_v1_bad_ambient.c \
  -o digest-validation-bad-ambient.ll
if python3 scripts/check_runtime_abi.py --partial \
    phase0-upload-digest-validation.ll \
    digest-validation-bad-ambient.ll; then
  echo "expected ABI checker to reject nullary digest validation" >&2
  exit 1
fi
echo "PASS: runtime ABI checker rejects ambient nullary digest validation"

PHILC="$(cabal list-bin philc)"

"$PHILC" emit-llvm examples/run/return-unit.phil > return-unit.ll
"$LLVM_AS" return-unit.ll -o return-unit.bc
"$CLANG" return-unit.bc -o return-unit
./return-unit

"$PHILC" emit-llvm examples/run/return-42.phil > return-42.ll
"$LLVM_AS" return-42.ll -o return-42.bc
"$CLANG" return-42.bc -o return-42
set +e
./return-42
SCALAR_STATUS=$?
set -e
if [ "$SCALAR_STATUS" -ne 42 ]; then
  echo "expected direct U32 Phil program to exit 42; got $SCALAR_STATUS" >&2
  exit 1
fi

"$PHILC" emit-llvm examples/run/scalar-binding-42.phil > scalar-binding-42.ll
"$LLVM_AS" scalar-binding-42.ll -o scalar-binding-42.bc
"$CLANG" scalar-binding-42.bc -o scalar-binding-42
set +e
./scalar-binding-42
BINDING_STATUS=$?
set -e
if [ "$BINDING_STATUS" -ne 42 ]; then
  echo "expected scalar-binding Phil program to exit 42; got $BINDING_STATUS" >&2
  exit 1
fi

echo "Phase 0 reference, recognized-record, exact-receive, and digest-validation LLVM assembled successfully"
echo "recognized-record runtime signatures verified, linked, and executed successfully"
echo "transport exact-receive runtime signatures verified, linked, and executed successfully"
echo "SHA-256 digest-validation runtime signatures verified, linked, and executed successfully"
echo "direct and bound scalar Phil programs returned 42 successfully"
"$LLVM_AS" --version | head -n 1
"$CLANG" --version | head -n 1
