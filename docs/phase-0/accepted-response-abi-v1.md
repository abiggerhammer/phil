# Phase 0 accepted-response ABI v1

Status: implementation candidate

Runtime profile: `phil-runtime/phase0/accepted-response-v1`

This profile extends `storage-v1` by materializing the already-explicit Systems operation:

```text
select accepted(server.transport, server.upload_id)
```

It does not change the Phase 0 source or Systems artifact.

## Target boundary

Generated LLVM calls:

```llvm
declare void @phil_runtime_select_accepted(ptr, ptr)

call void @phil_runtime_select_accepted(
  ptr %server_transport,
  ptr %server_upload_id)
```

The first operand is the exact component transport handle. The second is the exact opaque `UploadId` handle returned on the successful `storage-v1` edge.

There is no ambient/current transport or UploadId state.

## Accepted response payload encoding

The Phase 0 accepted-response payload is exactly 17 octets:

```text
+--------+-------------------------------------------------+
| byte 0 | bytes 1..16                                     |
+--------+-------------------------------------------------+
| 0x01   | 16-octet UploadId wire token                    |
+--------+-------------------------------------------------+
```

`0x00` is reserved for a future materialized rejected response. This profile does not otherwise define rejected-response encoding.

The 16-octet token is a **wire representation**, not the semantic/runtime representation of `UploadId`. Only the declared runtime encoder has authority to inspect the provider-private UploadId representation and produce these octets. Generated Phil code continues to treat the ID as an opaque, runtime-managed, non-owning pointer handle.

Generated code must not dereference, mutate, free, infer layout for, or add pointer-strengthening attributes to the UploadId.

## Framing boundary

The 17 octets above are the accepted **response payload bytes**. This profile deliberately does not define an outer record/frame envelope, length prefix, transport packetization, buffering policy, or retry mechanism. Those are separate representation decisions.

The source `select accepted(id)` operation has no physical-write failure branch. Accordingly, `accepted-response-v1` does not invent one. Failure of the runtime provider to emit the declared bytes is an explicit residual runtime assumption/evidence boundary for this slice.

## Identity and freshness

This profile preserves the exact UploadId identity returned by the successful store operation. It does **not** certify that UploadIds are globally unique, cryptographically random, unguessable, monotonic, or fresh across calls; none of those properties are currently part of the source-level claim being lowered here.

## Certification boundary

`PHIL-LLVM-CERT-006` binds the exact Systems source identity, canonical pre-optimization LLVM module/text, target identity, and this ABI descriptor. It certifies the operand-explicit translation from `select accepted(id)` to the declared runtime encoder boundary.

The following remain independent external gates:

- LLVM 18 acceptance;
- exact C-provider signature conformance;
- the runtime encoder's exact 17-octet output;
- native linking and execution;
- the provider-private UploadId implementation;
- physical transport write behavior and any outer framing.
