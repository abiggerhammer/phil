# Phase 0 runtime smoke boundary

This directory contains the first executable runtime-side fixture for Phil's
`phil-runtime/phase0/recognized-record-v1` ABI.

It is intentionally **not** the production upload runtime. Transport, framing,
policy, digest, and storage operations that are outside the current slice are
deterministic stubs. The purpose of this fixture is narrower:

1. compile a C implementation of the runtime ABI with Clang 18;
2. compare the Clang-emitted `phil_*` function definitions against Phil's LLVM
   declarations for exact result/argument types and arity;
3. link the checked runtime LLVM bitcode directly with Phil's emitted
   recognized-record bitcode;
4. execute `UploadServer` far enough to exercise the real recognized-record data
   dependency;
5. verify that `Begin.length` survives as the same full-width `uint64_t`/`i64`
   value into `phil_runtime_receive_exact_u64`;
6. verify that a reserved recognition status fails closed before record field
   access or exact receive;
7. verify that an ABI-incompatible provider defining the `Begin.length`
   accessor as `ptr -> i32` is rejected against Phil's required `ptr -> i64`
   declaration.

The success scenario is ABI-conforming. The malformed-status scenario is an
intentional fault injection: the fixture returns status `2` even though the ABI
reserves `1` for success and `0` for ordinary failure. This tests the generated
consumer's exact `status == 1` guard; it is not evidence that a conforming
runtime may normally return `2`.

A successful `llvm-link` is **not** treated as proof of exact ABI type equality.
LLVM may reconcile incompatible global function types while still producing a
valid linked module. `scripts/check_runtime_abi.py` therefore checks the
pre-link declarations and definitions explicitly. The deliberately incompatible
`recognized_record_v1_bad_accessor.c` fixture must fail that checker, while the
normal runtime fixture must match every `phil_*` declaration in the generated
module. `llvm-link` remains a separate composition gate after signature
validation, followed by native linking and execution.

The current checker intentionally compares result/argument LLVM types and arity
under the default calling convention while ignoring linkage and parameter/return
attributes. If the runtime ABI later assigns authority to calling-convention or
ABI-affecting attributes, those must become explicit checked dimensions too.

The remaining boundary after this fixture is to replace deterministic stubs
with actual transport/framing/runtime mechanisms while preserving the same
content-bound ABI and assurance obligations.
