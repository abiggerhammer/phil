# Phase 0 final-response receive ABI v1

Status: implementation candidate

This target profile lowers the semantic `TermSessionOffer` introduced by the Systems session-choice slice for the final client upload response. It preserves the exact `accepted(id)` / `rejected(reason)` control relation while allowing target-specific physical decoding.

## Runtime ABI

```llvm
declare i1 @phil_runtime_receive_final_response(ptr %transport, ptr %upload_id_out)
declare void @phil_runtime_record_upload_id(ptr %upload_id)
```

The decoder receives the exact client transport handle. The second operand points to a caller-owned slot for one opaque runtime-managed `UploadId` handle.

- `true`: the response is exactly `0x01 || UploadIdToken[16]`; the runtime materializes the token into its private `UploadId` representation and writes that opaque handle to `%upload_id_out`.
- `false`: the response is exactly `0x00 || 0x01` (`DigestMismatch`). The out slot is not read by generated code on this branch.
- malformed, truncated, overlong, reserved-tag, or reserved-reason responses must not cause this function to return normally. How the provider terminates/fails the transport remains outside the source CFG because the current source `offer` has no malformed-response arm.

Generated LLVM allocates the pointer slot at the offer site, branches on the runtime's `i1`, and loads the opaque handle only in the accepted binder block before calling `phil_runtime_record_upload_id`.

## Representation decisions

The 16-octet wire token is not the client `UploadId` representation. Only the runtime decoder may interpret/materialize it. Generated code receives an opaque pointer and does not dereference, infer layout, mutate, release, or strengthen it.

The decoded `UploadId` handle is runtime-owned and non-owning from generated code's perspective. Its guaranteed lifetime extends through the exact `phil_runtime_record_upload_id` call. If the application needs the ID afterward, that runtime operation must persist or copy the necessary state before the handle's guaranteed lifetime ends; generated code does not acquire ownership merely by carrying the handle.

The semantic `DigestFailure` binding from Systems has no physical target object in this exact profile because the frozen client never observes it. This is an exact-program erasure justified by the Systems session-choice witness, not a global claim that `DigestFailure` is representation-free.

No ambient current response, current UploadId, or last-response state is permitted.

## Translation certification — PHIL-LLVM-CERT-008

`PHIL-LLVM-CERT-008` content-binds the exact session-choice Systems artifact, canonical pre-optimization LLVM module/text, target/tool identity, and `final-response-receive-v1` ABI digest.

Its `TranslationValidated` evidence covers the exact client transport operand, accepted/rejected continuation mapping, accepted branch-local `UploadId` load, exact `record_upload_id(id)` use, exact-program erasure of the unused `DigestFailure`, elimination of the old generic final-response calls, absence of ambient response/UploadId state, preservation of the server accepted/rejected operations, and the fact that no malformed-response CFG edge is invented.

Provider parsing correctness, exact wire-token-to-private-UploadId materialization, malformed-input non-return, provider ABI conformance, LLVM implementation correctness, linking, and native execution remain independent external gates rather than claims of `CERT-008`.
