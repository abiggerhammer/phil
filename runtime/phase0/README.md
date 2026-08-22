# Phase 0 runtime smoke boundary

This directory contains the first executable runtime-side fixture for Phil's
`phil-runtime/phase0/recognized-record-v1` ABI.

It is intentionally **not** the production upload runtime. Transport, framing,
policy, digest, and storage operations that are outside the current slice are
deterministic stubs. The purpose of this fixture is narrower:

1. compile a C implementation of the runtime ABI with Clang 18;
2. link its LLVM bitcode directly with Phil's emitted recognized-record bitcode;
3. execute `UploadServer` far enough to exercise the real recognized-record data
   dependency;
4. verify that `Begin.length` survives as the same full-width `uint64_t`/`i64`
   value into `phil_runtime_receive_exact_u64`;
5. verify that a reserved recognition status fails closed before record field
   access or exact receive;
6. verify that an ABI-incompatible provider defining the `Begin.length`
   accessor as `ptr -> i32` is rejected against Phil's required `ptr -> i64`
   declaration.

The success scenario is ABI-conforming. The malformed-status scenario is an
intentional fault injection: the fixture returns status `2` even though the ABI
reserves `1` for success and `0` for ordinary failure. This tests the generated
consumer's exact `status == 1` guard; it is not evidence that a conforming
runtime may normally return `2`.

`llvm-link` is the ABI type gate. It must accept Phil's declarations and the
Clang-generated runtime definitions as one LLVM module before native linking or
execution occurs. This catches declaration/definition type drift that an ELF
linker alone would not reliably diagnose. The deliberately incompatible
`recognized_record_v1_bad_accessor.c` fixture is expected to fail this gate,
so CI checks both acceptance of the correct ABI and rejection of a concrete
width-drift mutation.

The remaining boundary after this fixture is to replace deterministic stubs
with actual transport/framing/runtime mechanisms while preserving the same
content-bound ABI and assurance obligations.
