# Phase 0 integrated native upload v1

## Purpose

This is the final Phase 0 implementation convergence slice. It takes the frozen checked `examples/upload/client.phil` and `examples/upload/server.phil` source pair through the landed source-to-Systems projection and current `control-codec-v1` LLVM lowering, links the emitted client and server functions against one concrete runtime provider, and executes them together as a native process.

The demonstrator is deliberately an **in-memory loopback**, not a production network transport. The point is to exercise the whole compiled authority chain in one executable without introducing operating-system I/O, durability, or deployment claims.

## Compilation chain

The native LLVM emitter `phil-phase0-upload-llvm` performs:

```text
client.phil + server.phil
  -> parse + Surface check
  -> surface-to-systems/phase0-upload/v1
  -> verified StorageFailure Systems successor
  -> phil-runtime/phase0/control-codec-v1 LLVM
```

Before emitting LLVM it reruns the source projection and `verifyLLVMEmissionWith` using the source-bound Systems verification context. The emitted module carries the real source-pair digest as a comment.

The focused workflow then assembles that LLVM, compiles the runtime providers to LLVM, checks the complete `phil_*` ABI with `scripts/check_runtime_abi.py`, links the modules, builds a native executable, and runs it.

## Runtime composition

`runtime/phase0/control_codec_v1.c` remains the single shared concrete implementation of Hello/Begin framing and encoding/recognition. The integrated demonstrator links that landed provider unchanged.

`runtime/phase0/integrated_upload_v1.c` supplies only the remaining runtime effects needed to run the complete reference program: version negotiation, policy decisions, payload/cancel and final-response choices, exact payload transfer, SHA-256 validation, storage, and UploadId observation.

The loopback uses one transcript for the shared control codec and condition-variable mailboxes for the later protocol choices and payload. The compiled client begins first and sends Hello. The server begins only once the client is waiting for the version response, so Hello is complete before framed ingress. During version selection the server waits until the client has sent Begin before returning to its Begin receive. This preserves the existing nonblocking codec provider byte-for-byte while giving the compiled endpoints deterministic lock-step execution.

## Native scenarios

The demonstrator executes three source-valid paths:

1. **Accepted upload**
   - concrete Hello and Begin round trip through the shared codec;
   - common version selected and refined;
   - both policies accept;
   - client selects payload and performs exact send;
   - server performs exact receive and SHA-256 validation;
   - storage consumes the payload and returns an opaque UploadId;
   - server selects accepted and the client records the exact same UploadId.

2. **Digest rejection**
   - the same control and exact-transfer path;
   - the fixture deliberately declares a different SHA-256 digest;
   - server validation rejects, releases the received payload, and selects rejected;
   - storage is never called and the client terminates on the rejected response.

3. **Client cancellation**
   - Hello/Begin negotiation and policy acceptance complete;
   - client selects cancel and releases its payload;
   - no exact payload transfer, digest validation, storage, or final response occurs.

## Storage failure

The integrated two-party executable intentionally does **not** synthesize a peer response for server storage failure. In the Phil source, storage failure is a local terminal internal failure and has no normal peer-protocol continuation. Fabricating a client-visible response solely to make the demo terminate would add authority not present in the program.

The dedicated storage-failure semantic, physical, runtime, proof, and certification gates remain the evidence for that terminal path.

## Authority boundary

This slice claims that:

- the frozen checked source pair feeds the native artifact through the landed source projection;
- the current verified Systems successor reaches the current control-codec LLVM target;
- the emitted LLVM and concrete provider have exact `phil_*` ABI agreement;
- the existing shared control codec is used in the integrated executable rather than reimplemented;
- exact client payload bytes reach server digest validation and storage on the accepted path;
- the accepted UploadId identity reaches the client recorder; and
- accepted, digest-rejected, and cancelled executions complete natively with the expected resource/effect observations.

It does **not** claim production networking, socket behavior, crash durability, remote receipt, filesystem persistence, or a general-purpose runtime implementation.
