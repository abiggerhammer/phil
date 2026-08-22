# Exact payload transport slice

This slice replaces only the Phase 0 `phil_runtime_receive_exact_u64` smoke stub
with a concrete synchronous ordered byte-stream mechanism. The compiler-side
`phil-runtime/phase0/recognized-record-v1` ABI is unchanged.

The provider reads from a runtime-owned file descriptor with POSIX `read(2)` in
bounded chunks, retries interrupted reads, returns success only after exactly the
requested `uint64_t` count is consumed, and returns failure on EOF or another
read error before that point.

The native harness establishes two positive/negative observations:

- exact receive consumes exactly `Begin.length` bytes and leaves later bytes in
  the stream untouched;
- EOF before `Begin.length` makes the runtime primitive return false, and the
  generated `UploadServer` follows its exact-receive failure path rather than
  selecting acceptance.

This evidence is intentionally runtime-tested rather than a proof of POSIX,
Clang, LLVM, the host kernel, or production transport correctness. Socket
lifecycle, deadlines, cancellation, buffering policy, framing/recognition,
payload retention, digesting, and storage remain outside this slice.
