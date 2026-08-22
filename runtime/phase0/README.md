# Phase 0 runtime boundary

This directory contains executable runtime-side fixtures for Phil's
`phil-runtime/phase0/recognized-record-v1` ABI.

It is intentionally **not** the production upload runtime. Recognition framing,
policy, digest, storage, and most protocol operations remain deterministic stubs.
The fixtures isolate successive runtime boundaries while preserving the exact
compiler-side ABI.

## Recognized-record ABI smoke fixture

`recognized_record_v1_smoke.c` and `recognized_record_v1_smoke_main.c` establish
the first executable provider-side ABI/dataflow evidence:

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

## Exact payload fd transport fixture

`recognized_record_v1_fd_transport.c` replaces the `receive_exact_u64` stub with
a real synchronous byte-stream mechanism while keeping the same ABI symbol and
signature. The runtime owns a configured input file descriptor and implements
`phil_runtime_receive_exact_u64(i64) -> i1` as a bounded `read(2)` loop:

- reads are retried after `EINTR`;
- the requested 64-bit count is consumed incrementally without allocating a
  payload-sized buffer;
- success is returned only after exactly the declared number of bytes have been
  consumed;
- EOF or another read failure before that point returns false, allowing Phil's
  generated exact-receive failure edge to run;
- bytes after the declared payload length are not consumed.

`recognized_record_v1_fd_transport_main.c` exercises two native cases after the
normal ABI-signature gate and LLVM composition:

1. a stream containing `Begin.length` payload bytes followed by sentinel bytes;
   `UploadServer` succeeds and the sentinel bytes remain unread;
2. a stream that reaches EOF before `Begin.length`; `receive_exact_u64` returns
   false and `UploadServer` takes its cleanup/failure path rather than selecting
   acceptance.

This is executable evidence for synchronous ordered exact-byte acquisition. It
does **not** yet establish production socket lifecycle, timeouts, cancellation,
framing, grammar recognition, buffering policy, payload retention, digesting,
or storage semantics.

## ABI conformance boundary

A successful `llvm-link` is **not** treated as proof of exact ABI type equality.
LLVM may reconcile incompatible global function types while still producing a
valid linked module. `scripts/check_runtime_abi.py` therefore checks the
pre-link declarations and definitions explicitly. The deliberately incompatible
`recognized_record_v1_bad_accessor.c` fixture must fail that checker, while both
normal providers must match every `phil_*` declaration in the generated module.
`llvm-link` remains a separate composition gate after signature validation,
followed by native linking and execution.

The current checker intentionally compares result/argument LLVM types and arity
under the default calling convention while ignoring linkage and parameter/return
attributes. If the runtime ABI later assigns authority to calling-convention or
ABI-affecting attributes, those must become explicit checked dimensions too.

The next runtime boundary is framing/recognition or concrete socket/session
lifecycle on top of the same exact-receive contract. Whichever lands first must
preserve the content-bound recognized-record ABI and keep acquisition failure
fail-closed.
