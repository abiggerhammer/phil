# Phase 0 Digest-Validation ABI v1

## Status

Implementation decision for the next Phase 0 LLVM/runtime candidate after `phil-runtime/phase0/transport-exact-receive-v1`.

This slice makes the source-level `DigestMatches(begin, payloadView)` subjects concrete at the Systems and LLVM/runtime boundaries. It does not yet make storage, exact send, or frame acquisition operand-complete.

## Systems correction

The source program validates:

```phil
borrow payload as payloadView {
    validate DigestMatches on (begin, payloadView)
}
```

The historical Systems artifact represented the digest runtime check with only `payloadView`. This candidate corrects that omission and records the exact semantic subject pair:

```text
server.begin : RuntimeRecord "Begin"
server.payload : OwnedBuffer "Bytes[begin.length]"
server.payload_view : BorrowedSlice server.payload

OpBorrowView server.payload_view server.payload
TermRuntimeCheck [server.begin, server.payload_view] digestSite ...
```

The historical Systems/LLVM artifacts and `PHIL-LLVM-CERT-001` through `PHIL-LLVM-CERT-003` remain unchanged.

## Borrow representation

The payload borrow is semantic and ownership-restricting, but it does not require a second physical runtime object in this target profile.

After Systems verifies that `server.payload_view` is a `BorrowedSlice` of the exact `server.payload` owner and that the matching `OpBorrowView` occurs before the digest check, LLVM may represent the borrowed view by passing the existing opaque payload-owner pointer to the digest validator.

This is representation erasure, not ownership erasure. The owner remains live and cannot be consumed while the source borrow is active; generated LLVM merely avoids allocating a redundant view object.

## Digest validator ABI

The concrete Phase 0 runtime primitive is:

```llvm
declare i1 @phil_runtime_digest_validate(ptr, ptr)
```

Its operands are, in order:

1. the exact opaque recognized-record handle for source `begin`;
2. the exact opaque payload-owner handle underlying source `payloadView`.

The generated call is structurally:

```llvm
%phil_digest_ok_server_digest = call i1 @phil_runtime_digest_validate(
  ptr %server_begin,
  ptr %server_payload_owner)
br i1 %phil_digest_ok_server_digest,
   label %server_store,
   label %server_digest_mismatch
```

No ambient current-Begin, current-payload, thread-local upload context, or nullary digest operation is permitted.

## Runtime semantics

The Phase 0 assurance ledger declares the digest mechanism to be SHA-256. The runtime provider therefore computes SHA-256 over the exact payload bytes represented by the second operand and compares it against the expected digest carried by the exact recognized `Begin` semantic record represented by the first operand.

The validator returns `true` iff they match. On `false`, ownership of the payload is unchanged so the existing digest-mismatch path may release it and select rejection.

The private runtime representation of the `Begin` digest field and payload bytes remains hidden behind opaque handles. Generated LLVM receives no layout authority from this ABI.

## Translation-validation obligations

The candidate is rejected if any of the following drift occurs:

- Systems omits either source digest subject;
- the payload view is not a borrow of the exact payload owner;
- the LLVM record operand differs from the exact recognition result;
- the LLVM payload operand differs from the exact receive result;
- the borrow is materialized from a different owner;
- record and payload operands are swapped;
- the digest runtime symbol is nullary or recovers subjects from ambient state;
- the success/failure edges differ from the Systems digest check;
- linker-visible runtime identity is derived from assurance evidence rather than the physical primitive/signature.

## ABI identity

Working profile:

```text
phil-runtime/phase0/digest-validation-v1
```

Its canonical descriptor binds at least:

- the exact-receive ABI digest;
- target triple and data layout;
- `BorrowedSlice(owner) -> same owner ptr` no-copy representation;
- `phil_runtime_digest_validate(ptr,ptr)->i1`;
- exact record and payload operand ordering;
- SHA-256 mechanism semantics;
- physical runtime symbol identity;
- absence of ambient subject state;
- absence of default pointer-strengthening attributes.

Changing any item requires a new ABI digest/profile revision.

## Certification boundary

Promotion requires a fresh `PHIL-LLVM-CERT-004` binding the exact corrected Systems artifact and exact pre-optimization LLVM artifact/profile.

Runtime-provider ABI conformance and concrete SHA-256 execution remain separate external evidence. The translation certificate must not claim that pure Haskell verified the C implementation or SHA-256 algorithm.
