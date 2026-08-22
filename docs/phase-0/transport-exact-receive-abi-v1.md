# Phase 0 Transport Exact-Receive ABI v1

## Status

Implementation decision for the next Phase 0 LLVM/runtime candidate after `phil-runtime/phase0/recognized-record-v1`.

The recognized-record ABI deliberately made only the `Begin.length` dependency concrete. It left the physical transport handle and exact-receive payload owner unresolved. This document closes that narrower boundary without choosing representations for digest, storage, send, or the complete upload runtime.

## Decision

For the Phase 0 x86_64 LLVM target:

- a Systems `TransportHandle` that is live at component entry is represented as an opaque caller-supplied `ptr` LLVM function parameter;
- session typestate transitions reuse that physical transport pointer while remaining represented by checked CFG/typestate rather than by manufacturing new runtime handles;
- exact receive consumes the exact transport handle and the exact typed length SSA value;
- exact receive returns a status plus an opaque runtime-owned payload buffer handle;
- the returned payload handle becomes the physical representation of the exact Systems `OwnedBuffer` value;
- partial-buffer cleanup consumes that exact payload handle explicitly.

No ambient `current transport`, implicit singleton connection, thread-local session, or global payload slot is part of this ABI.

## Component transport parameters

For the current Phase 0 functions:

```llvm
define i32 @UploadServer(ptr %server_transport)
define i32 @UploadClient(ptr %client_transport)
```

The parameter is the physical representation of the corresponding Systems `TransportHandle` value. The pointer is opaque to generated LLVM. Generated code may pass it to declared runtime primitives but may not dereference it or attach pointer-strengthening attributes without separate authority.

The many source-level session values (`session0`, `session1`, ...) do not imply many physical transports. Their protocol state is enforced by Phil and lowered primarily into control flow. Reusing one physical pointer is therefore an implementation of the existing Systems lowering decision, not an erasure of source sequencing.

## Exact-receive result

For `U64` lengths the runtime primitive is:

```llvm
declare { i8, ptr } @phil_runtime_receive_exact_u64(ptr, i64)
```

A call is lowered structurally as:

```llvm
%r = call { i8, ptr } @phil_runtime_receive_exact_u64(
  ptr %server_transport,
  i64 %server_begin_length)
%status = extractvalue { i8, ptr } %r, 0
%server_payload_owner = extractvalue { i8, ptr } %r, 1
%ok = icmp eq i8 %status, 1
br i1 %ok, label %server_digest, label %server_early_eof
```

The elements are:

1. `i8 status` — `1` means exactly the requested number of bytes were received; `0` means early EOF / incomplete receive;
2. `ptr payload` — opaque runtime-owned buffer handle representing the resulting Systems payload owner.

Generated code compares the status with exactly `1`. Other values are reserved and take the failure edge. As elsewhere in the runtime TCB, a provider that violates the ABI may invalidate assumptions about the other fields; the fail-closed comparison is not a claim of memory safety against an arbitrarily malicious ABI provider.

## Payload ownership and LLVM identity

On success, the returned handle owns exactly the requested byte count and is the physical representative of `server.payload : OwnedBuffer "Bytes[begin.length]"`.

The Systems identity remains `server.payload`. Its Phase 0 LLVM SSA spelling is deterministically derived as `server.payload.owner`, rendered as `%server_payload_owner`. The suffix is required because LLVM local SSA names and basic-block labels share a namespace, while this program already has a `server.payload` basic block. Renaming historical blocks would change previously certified LLVM text, so the new profile disambiguates the newly materialized owner instead.

Translation validation binds `%server_payload_owner` back to the exact Systems `server.payload` owner; it is not an unrelated runtime temporary.

On ordinary early EOF (`status == 0`), the returned handle represents the partial payload owner required by the existing Systems failure path. That owner must be valid for explicit release by the generated cleanup path.

The runtime implementation may choose any internal buffer layout. Generated LLVM may not dereference or index the handle directly in this profile.

## Explicit partial cleanup

The exact-receive failure path lowers the existing Systems `OpCleanupPartial server.payload` to:

```llvm
declare void @phil_buffer_release(ptr)
call void @phil_buffer_release(ptr %server_payload_owner)
```

The same primitive is also used when a later ordinary `OpReleaseOwner server.payload` releases the concrete exact-receive owner. This slice requires that both paths preserve exact owner identity.

## In-memory transport fixture

The first runtime implementation is an independently compiled fixture with an opaque transport object containing a finite input byte sequence and cursor. `phil_runtime_receive_exact_u64`:

1. receives the explicit transport pointer;
2. checks/allocates a payload buffer for the requested bounded fixture length;
3. copies bytes from that transport only;
4. returns success iff the requested count was available;
5. otherwise returns a partial owner and the failure status.

This is a real transport-backed implementation of the ABI operation, but it is deliberately an in-memory test transport rather than sockets, files, TLS, or a production framing stack.

## Translation-validation obligations

The new LLVM candidate must be rejected if any of the following drift occurs:

- the Systems transport identity is not the LLVM transport parameter consumed by exact receive;
- the length is not the exact `Begin.length : U64` SSA value;
- the runtime argument width changes from `i64`;
- the exact-receive result payload is not the deterministic LLVM representative of the Systems `exactPayloadOwner`;
- the success/failure edges change;
- the status test ceases to be exact `== 1`;
- the EarlyEOF cleanup releases any payload other than the returned exact-receive owner;
- an ordinary later release of that owner is substituted with a different handle;
- transport or payload is recovered from ambient runtime state;
- linker-visible runtime symbols become assurance-evidence identities.

## ABI identity

This is a new target/runtime ABI profile because it changes function signatures and exact-receive representation relative to `recognized-record-v1`.

Working profile name:

```text
phil-runtime/phase0/transport-exact-receive-v1
```

Its canonical descriptor binds at least:

- the base recognized-record ABI digest;
- target triple and data layout;
- `TransportHandle -> opaque ptr` component-entry convention;
- exact-receive signature `ptr,i64 -> {i8,ptr}`;
- exact status semantics;
- payload-owner handle semantics;
- deterministic Systems-owner-to-LLVM-SSA naming for the newly materialized payload;
- explicit owner release `phil_buffer_release(ptr)`;
- physical runtime-symbol convention;
- absence of default pointer-strengthening attributes.

Changing any item requires a new ABI digest/profile revision.

## Certification boundary

`PHIL-LLVM-CERT-002` remains bound to the exact `recognized-record-v1` artifact. This candidate must use a fresh certification revision if promoted.

The certificate may establish the exact Systems -> pre-optimization LLVM translation relation for this ABI. Runtime implementation conformance and execution are separate evidence: the runtime provider's LLVM signatures are checked independently before composition, and the executable fixture tests the concrete transport/dataflow behavior. Neither is represented as a proof of LLVM or of a production transport stack.

## Deferred work

This slice does not yet make the digest validator, storage operation, exact send, framing receive, or all payload-success uses physically consume their Systems operands. In particular, after successful exact receive the payload handle is concrete, but later semantic uses remain future runtime-ABI slices unless explicitly covered by this candidate.