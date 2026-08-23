# Phase 0 transport exact-send ABI v1

## Scope

This target physically lowers the already-explicit Phase 0 client operation:

```text
send_exact(client.transport, client.payload)
```

without changing its source semantics or inventing a recoverable transport-failure branch.

Runtime profile:

```text
phil-runtime/phase0/transport-exact-send-v1
```

It composes on top of `hello-policy-validation-v1`.

## UploadClient entry ABI

The predecessor target already exposes the client transport as an opaque pointer parameter. This target appends the source-owned payload handle. LLVM arguments and basic-block labels share a function-local namespace, and the source block `client.payload` already renders as `client_payload`, so the target uses the established owned-buffer `.owner` suffix:

```text
Systems client.payload  -> LLVM client.payload.owner
UploadClient(ptr client.transport, ptr client.payload.owner)
```

This is an explicit source-to-target naming relation, not a different semantic payload. `client.payload` remains the exact existing Systems `OwnedBuffer` identity. It is not copied, rematerialized, or looked up through ambient state.

## Runtime primitive

```c
void phil_runtime_send_exact(void *transport, void *payload);
```

The two arguments are:

1. the exact `client.transport` handle;
2. target `%client_payload_owner`, representing the exact source `client.payload` owned-buffer handle.

The payload representation remains opaque to Phil. The selected runtime owns the concrete buffer layout and send mechanism.

## Completion and failure semantics

The source program has:

```text
let session4 = send_exact payload on session3
```

and no transport-failure continuation. Therefore the v1 physical contract is:

- normal return means the runtime has completed the source-level exact send of the entire logical buffer and ownership has been consumed;
- a partial write, transport failure, or inability to complete that exact send must not return normally.

This is intentionally weaker than a durability claim. The profile does **not** define:

- kernel/socket buffering semantics;
- remote receipt or acknowledgement;
- persistence/durability;
- packetization;
- encryption;
- outer framing.

Those remain runtime/provider or later protocol concerns.

## Runtime-site preservation

The exact existing `ExactSendBoundary` `RuntimeSiteRef` remains represented in the LLVM target. Physical lowering replaces the predecessor's generic zero-argument runtime-site call with the explicit primitive above; it does not erase the runtime assurance site.

## Ownership

No representation copy is introduced by translation. The opaque payload handle represented by `%client_payload_owner` is passed directly to `phil_runtime_send_exact`.

On normal return, the target treats the source-owned payload as consumed by the send operation. Alternative source paths that release the payload remain path-local predecessor behavior.

## Fail-closed rules

The target rejects or tests against:

- missing/incorrect client payload role;
- wrong transport or payload identities;
- loss of the explicit `client.payload -> client.payload.owner` source-to-target relation;
- generic/nullary exact-send calls;
- ambient current-transport/current-payload state;
- loss of the exact runtime site;
- unresolved poison/unreachable residue;
- regression of the already-lowered HelloPolicy/BeginPolicy/version machinery.

## Certification boundary

`PHIL-LLVM-CERT-013` is translation-only. It content-binds the exact Systems source, canonical pre-optimization LLVM module/text, target profile, tool/layout identities, and runtime ABI digest.

Provider whole-send/non-return semantics, opaque buffer implementation, physical I/O, LLVM 18 semantics, linking, and native execution remain independent gates.
