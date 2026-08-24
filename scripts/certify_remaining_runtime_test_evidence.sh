#!/usr/bin/env bash
set -euo pipefail

CERTIFIER=${CERTIFIER:-./phil-certify-test-evidence}
OUT_DIR=${OUT_DIR:-remaining-runtime-test-evidence-certificates}
mkdir -p "$OUT_DIR"

if command -v llvm-as-18 >/dev/null 2>&1; then
  LLVM_AS=llvm-as-18
elif command -v llvm-as >/dev/null 2>&1 && llvm-as --version | head -n 1 | grep -Eq 'LLVM version 18([.]|$)'; then
  LLVM_AS=llvm-as
else
  echo "LLVM 18 llvm-as is required" >&2
  exit 1
fi

if command -v llvm-link-18 >/dev/null 2>&1; then
  LLVM_LINK=llvm-link-18
elif command -v llvm-link >/dev/null 2>&1 && llvm-link --version | head -n 1 | grep -Eq 'LLVM version 18([.]|$)'; then
  LLVM_LINK=llvm-link
else
  echo "LLVM 18 llvm-link is required" >&2
  exit 1
fi

if command -v clang-18 >/dev/null 2>&1; then
  CLANG=clang-18
elif command -v clang >/dev/null 2>&1 && clang --version | head -n 1 | grep -Eq 'clang version 18([.]|$)'; then
  CLANG=clang
else
  echo "Clang 18 is required" >&2
  exit 1
fi

certify_digest() {
  local emitter
  emitter="$(cabal list-bin phil-llvm-phase0-digest-validation)"
  "$emitter" > phase0-upload-digest-validation.ll
  "$LLVM_AS" phase0-upload-digest-validation.ll -o phase0-upload-digest-validation.bc

  "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
    -Iruntime/phase0 -S -emit-llvm runtime/phase0/digest_validation_v1_smoke.c \
    -o digest-validation-runtime.ll
  "$LLVM_AS" digest-validation-runtime.ll -o digest-validation-runtime.bc

  "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
    -Iruntime/phase0 -emit-llvm -c runtime/phase0/digest_validation_v1_smoke_main.c \
    -o digest-validation-smoke-main.bc
  "$LLVM_LINK" phase0-upload-digest-validation.bc digest-validation-runtime.bc \
    digest-validation-smoke-main.bc -o phase0-upload-digest-validation-linked.bc
  "$CLANG" --target=x86_64-unknown-linux-gnu phase0-upload-digest-validation-linked.bc \
    -lcrypto -o phase0-upload-digest-validation-smoke

  "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
    -S -emit-llvm runtime/phase0/digest_validation_v1_bad_ambient.c \
    -o digest-validation-bad-ambient.ll

  {
    python3 scripts/check_runtime_abi.py phase0-upload-digest-validation.ll digest-validation-runtime.ll
    ./phase0-upload-digest-validation-smoke
    if python3 scripts/check_runtime_abi.py --partial \
        phase0-upload-digest-validation.ll digest-validation-bad-ambient.ll; then
      echo "expected ABI checker to reject nullary digest validation" >&2
      exit 1
    fi
    echo "PASS: runtime ABI checker rejects ambient nullary digest validation"
  } 2>&1 | tee runtime-digest.log

  "$CERTIFIER" runtime-digest runtime-digest.log \
    "$OUT_DIR/PHIL-RUNTIME-DIGEST-001.test.cert"
}

certify_exact_receive() {
  local emitter
  emitter="$(cabal list-bin phil-llvm-phase0-exact-receive)"
  "$emitter" > phase0-upload-exact-receive.ll
  "$LLVM_AS" phase0-upload-exact-receive.ll -o phase0-upload-exact-receive.bc

  "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
    -Iruntime/phase0 -S -emit-llvm runtime/phase0/transport_exact_receive_v1_smoke.c \
    -o transport-exact-receive-runtime.ll
  "$LLVM_AS" transport-exact-receive-runtime.ll -o transport-exact-receive-runtime.bc

  "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
    -Iruntime/phase0 -emit-llvm -c runtime/phase0/transport_exact_receive_v1_smoke_main.c \
    -o transport-exact-receive-smoke-main.bc
  "$LLVM_LINK" phase0-upload-exact-receive.bc transport-exact-receive-runtime.bc \
    transport-exact-receive-smoke-main.bc -o phase0-upload-exact-receive-linked.bc
  "$CLANG" --target=x86_64-unknown-linux-gnu phase0-upload-exact-receive-linked.bc \
    -o phase0-upload-exact-receive-smoke

  "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
    -S -emit-llvm runtime/phase0/transport_exact_receive_v1_bad_ambient.c \
    -o transport-exact-receive-bad-ambient.ll

  {
    python3 scripts/check_runtime_abi.py phase0-upload-exact-receive.ll transport-exact-receive-runtime.ll
    ./phase0-upload-exact-receive-smoke
    if python3 scripts/check_runtime_abi.py --partial \
        phase0-upload-exact-receive.ll transport-exact-receive-bad-ambient.ll; then
      echo "expected ABI checker to reject exact receive without transport operand" >&2
      exit 1
    fi
    echo "PASS: runtime ABI checker rejects ambient length-only exact receive"
  } 2>&1 | tee runtime-exact-receive.log

  "$CERTIFIER" runtime-exact-receive-fixture runtime-exact-receive.log \
    "$OUT_DIR/PHIL-RUNTIME-EXACT-001.test.cert"
}

certify_storage() {
  local emitter
  emitter="$(cabal list-bin phil-llvm-phase0-storage)"
  "$emitter" > phase0-upload-storage.ll
  "$LLVM_AS" phase0-upload-storage.ll -o phase0-upload-storage.bc

  "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
    -Iruntime/phase0 -S -emit-llvm runtime/phase0/storage_v1_smoke.c -o storage-runtime.ll
  "$LLVM_AS" storage-runtime.ll -o storage-runtime.bc

  "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
    -Iruntime/phase0 -emit-llvm -c runtime/phase0/storage_v1_smoke_main.c \
    -o storage-smoke-main.bc
  "$LLVM_LINK" phase0-upload-storage.bc storage-runtime.bc storage-smoke-main.bc \
    -o phase0-upload-storage-linked.bc
  "$CLANG" --target=x86_64-unknown-linux-gnu phase0-upload-storage-linked.bc \
    -lcrypto -o phase0-upload-storage-smoke

  "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
    -S -emit-llvm runtime/phase0/storage_v1_bad_ambient.c -o storage-bad-ambient.ll

  {
    python3 scripts/check_runtime_abi.py phase0-upload-storage.ll storage-runtime.ll
    ./phase0-upload-storage-smoke
    if python3 scripts/check_runtime_abi.py --partial phase0-upload-storage.ll storage-bad-ambient.ll; then
      echo "expected ABI checker to reject nullary/bool storage provider" >&2
      exit 1
    fi
    echo "PASS: runtime ABI checker rejects ambient nullary storage"
  } 2>&1 | tee runtime-storage.log

  "$CERTIFIER" runtime-storage-fixture runtime-storage.log \
    "$OUT_DIR/PHIL-RUNTIME-STORAGE-001.test.cert"
}

certify_accepted() {
  local emitter
  emitter="$(cabal list-bin phil-llvm-phase0-accepted-response)"
  "$emitter" > phase0-upload-accepted-response.ll
  "$LLVM_AS" phase0-upload-accepted-response.ll -o phase0-upload-accepted-response.bc

  "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
    -Iruntime/phase0 -S -emit-llvm runtime/phase0/accepted_response_v1_smoke.c \
    -o accepted-response-runtime.ll
  "$LLVM_AS" accepted-response-runtime.ll -o accepted-response-runtime.bc

  "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
    -Iruntime/phase0 -emit-llvm -c runtime/phase0/accepted_response_v1_smoke_main.c \
    -o accepted-response-smoke-main.bc
  "$LLVM_LINK" phase0-upload-accepted-response.bc accepted-response-runtime.bc \
    accepted-response-smoke-main.bc -o phase0-upload-accepted-response-linked.bc
  "$CLANG" --target=x86_64-unknown-linux-gnu phase0-upload-accepted-response-linked.bc \
    -lcrypto -o phase0-upload-accepted-response-smoke

  "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
    -S -emit-llvm runtime/phase0/accepted_response_v1_bad_ambient.c \
    -o accepted-response-bad-ambient.ll

  {
    python3 scripts/check_runtime_abi.py phase0-upload-accepted-response.ll accepted-response-runtime.ll
    ./phase0-upload-accepted-response-smoke
    if python3 scripts/check_runtime_abi.py --partial \
        phase0-upload-accepted-response.ll accepted-response-bad-ambient.ll; then
      echo "expected ABI checker to reject nullary accepted-response provider" >&2
      exit 1
    fi
    echo "PASS: runtime ABI checker rejects ambient nullary accepted-response encoding"
  } 2>&1 | tee runtime-accepted.log

  "$CERTIFIER" runtime-accepted-fixture runtime-accepted.log \
    "$OUT_DIR/PHIL-RUNTIME-ACCEPTED-001.test.cert"
}

certify_rejected() {
  local emitter
  emitter="$(cabal list-bin phil-llvm-phase0-rejected-response)"
  "$emitter" > phase0-upload-rejected-response.ll
  "$LLVM_AS" phase0-upload-rejected-response.ll -o phase0-upload-rejected-response.bc

  "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
    -Iruntime/phase0 -S -emit-llvm runtime/phase0/rejected_response_v1_smoke.c \
    -o rejected-response-runtime.ll
  "$LLVM_AS" rejected-response-runtime.ll -o rejected-response-runtime.bc

  "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
    -Iruntime/phase0 -emit-llvm -c runtime/phase0/rejected_response_v1_smoke_main.c \
    -o rejected-response-smoke-main.bc
  "$LLVM_LINK" phase0-upload-rejected-response.bc rejected-response-runtime.bc \
    rejected-response-smoke-main.bc -o phase0-upload-rejected-response-linked.bc
  "$CLANG" --target=x86_64-unknown-linux-gnu phase0-upload-rejected-response-linked.bc \
    -lcrypto -o phase0-upload-rejected-response-smoke

  "$CLANG" --target=x86_64-unknown-linux-gnu -std=c11 -Wall -Wextra -Wpedantic -Werror \
    -S -emit-llvm runtime/phase0/rejected_response_v1_bad_ambient.c \
    -o rejected-response-bad-ambient.ll

  {
    python3 scripts/check_runtime_abi.py phase0-upload-rejected-response.ll rejected-response-runtime.ll
    ./phase0-upload-rejected-response-smoke
    if python3 scripts/check_runtime_abi.py --partial \
        phase0-upload-rejected-response.ll rejected-response-bad-ambient.ll; then
      echo "expected ABI checker to reject nullary rejected-response provider" >&2
      exit 1
    fi
    echo "PASS: runtime ABI checker rejects ambient nullary rejected-response encoding"
  } 2>&1 | tee runtime-rejected.log

  "$CERTIFIER" runtime-rejected-fixture runtime-rejected.log \
    "$OUT_DIR/PHIL-RUNTIME-REJECTED-001.test.cert"
}

certify_digest
certify_exact_receive
certify_storage
certify_accepted
certify_rejected

for certificate in "$OUT_DIR"/*.test.cert; do
  echo "===== $certificate ====="
  cat "$certificate"
  sha256sum "$certificate"
done
