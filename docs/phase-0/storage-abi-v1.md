# Phase 0 storage ABI v1

Status: implementation candidate

Runtime profile: `phil-runtime/phase0/storage-v1`

This profile extends `digest-validation-v1` by materializing the already-explicit Systems storage boundary. It does not change the Phase 0 source or Systems artifact.

## Store call

The generated target calls:

```llvm
declare { i8, ptr } @phil_runtime_store(ptr)

%r = call { i8, ptr } @phil_runtime_store(ptr %server_payload_owner)
%status = extractvalue { i8, ptr } %r, 0
%server_upload_id = extractvalue { i8, ptr } %r, 1
%ok = icmp eq i8 %status, 1
```

The pointer argument is the exact payload owner returned by `receive_exact`. No ambient or current-payload state is permitted.

Status `1` is success. Every other status value takes the storage-failure edge.

## Ownership

Calling `phil_runtime_store` transfers the payload owner to storage. Storage consumes/releases that owner on both success and failure. Generated code must not release the payload after the store call on either outgoing edge.

A conforming failure result returns a null UploadId pointer. The runtime smoke fixture also injects reserved status `2` with a deliberately non-null pointer to verify that generated code still fails closed; that injected result is intentionally not a conforming provider result.

## UploadId representation

`UploadId` remains semantically opaque in Phase 0. The physical v1 representation is an opaque, runtime-managed, non-owning pointer handle returned only on storage success. A successful handle remains valid through the return of the calling Phil component; the runtime owns its storage throughout that interval.

Generated Phil code may carry the handle by SSA identity, but it must not:

- dereference it;
- infer or depend on a concrete layout;
- mutate it;
- free/release it;
- retain it beyond the calling component return under this ABI revision;
- add `nonnull`, `dereferenceable`, `align`, `noalias`, `noundef`, or similar strengthening without separate authority.

The wire representation of `UploadId` is deliberately deferred to the later accepted-response encoding slice.

## Certification boundary

`PHIL-LLVM-CERT-005` binds the exact Systems source identity, canonical pre-optimization LLVM text/module, target identity, and this ABI descriptor. LLVM 18 acceptance, C-provider signature conformance, actual persistence behavior, ownership consumption, and native execution remain independent external gates.