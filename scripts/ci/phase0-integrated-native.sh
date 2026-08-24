#!/usr/bin/env bash
set -euo pipefail

source scripts/ci/resolve-llvm18.sh

cabal build \
  lib:phil-phase0-projection \
  exe:phil-phase0-upload-llvm \
  test:projection-tests \
  --ghc-options=-Werror
cabal test projection-tests --test-show-details=direct

EMITTER="$(cabal list-bin exe:phil-phase0-upload-llvm)"
"$EMITTER" > phase0-source-bound.ll

grep -q '^; phase0-source-pair-digest=5339e6c7e6520e5495c1d304edcc2427e4bdbe19ce80167af3a314ab2f69e4df$' phase0-source-bound.ll
grep -q '^; phase0-source-projection=surface-to-systems/phase0-upload/v1$' phase0-source-bound.ll
grep -q '^; runtime-abi-profile=phil-runtime/phase0/control-codec-v1$' phase0-source-bound.ll
grep -Fq 'define i32 @UploadClient(ptr %client_transport, ptr %client_payload_owner)' phase0-source-bound.ll
grep -Fq 'define i32 @UploadServer(ptr %server_policy_context, ptr %server_supported_versions, ptr %server_transport)' phase0-source-bound.ll
"$LLVM_AS" phase0-source-bound.ll -o phase0-source-bound.bc

"$CLANG" --target=x86_64-unknown-linux-gnu \
  -std=c11 -Wall -Wextra -Wpedantic -Werror \
  -Iruntime/phase0 -S -emit-llvm \
  runtime/phase0/control_codec_v1.c \
  -o control-codec-provider.ll
"$CLANG" --target=x86_64-unknown-linux-gnu \
  -std=c11 -Wall -Wextra -Wpedantic -Werror -pthread \
  -Iruntime/phase0 -S -emit-llvm \
  runtime/phase0/integrated_upload_v1.c \
  -o integrated-upload-provider.ll
"$CLANG" --target=x86_64-unknown-linux-gnu \
  -std=c11 -Wall -Wextra -Wpedantic -Werror -pthread \
  -Iruntime/phase0 -S -emit-llvm \
  runtime/phase0/integrated_upload_v1_main.c \
  -o integrated-upload-main.ll

"$LLVM_AS" control-codec-provider.ll -o control-codec-provider.bc
"$LLVM_AS" integrated-upload-provider.ll -o integrated-upload-provider.bc
"$LLVM_AS" integrated-upload-main.ll -o integrated-upload-main.bc
"$LLVM_LINK" \
  control-codec-provider.bc \
  integrated-upload-provider.bc \
  -o integrated-provider.bc
"$LLVM_DIS" integrated-provider.bc -o integrated-provider.ll

python3 scripts/check_runtime_abi.py \
  phase0-source-bound.ll \
  integrated-provider.ll

"$LLVM_LINK" \
  phase0-source-bound.bc \
  integrated-provider.bc \
  integrated-upload-main.bc \
  -o phase0-integrated-upload.bc
"$CLANG" --target=x86_64-unknown-linux-gnu \
  phase0-integrated-upload.bc \
  -lcrypto -pthread \
  -o phase0-integrated-upload

./phase0-integrated-upload
