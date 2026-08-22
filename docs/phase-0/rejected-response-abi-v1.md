# Phase 0 rejected-response ABI v1

Status: implementation candidate

Runtime profile: `phil-runtime/phase0/rejected-response-v1`

This profile extends `accepted-response-v1` by materializing the already-explicit final payload failure operation:

```text
release server.payload
select rejected(reason) on server.transport
```

The Phase 0 semantic session types the peer-visible payload as `DigestFailure`. At this boundary, `DigestFailure` has exactly one protocol-observable class: **DigestMismatch**. Rich validator diagnostics, implementation error objects, hash-library errors, and debug strings are not protocol data.

## Target boundary

Generated LLVM calls:

```llvm
declare void @phil_runtime_select_rejected(ptr, i8)

call void @phil_runtime_select_rejected(
  ptr %server_transport,
  i8 1)
```

The first operand is the exact component transport handle. The second is the explicit Phase 0 wire reason code for `DigestMismatch`.

There is no ambient/current transport, rejection reason, or “last digest error” state.

## Why the reason is a code, not an opaque runtime object

`digest-validation-v1` returns only the success predicate needed by the source control flow. The current source never inspects diagnostic detail from the failed digest check before selecting `rejected(reason)`, and the semantic session exposes only `DigestFailure` to the peer.

Rather than extend the digest ABI with a runtime-owned error object solely to carry non-semantic diagnostics, this profile makes the protocol-observable equivalence explicit:

```text
DigestFailure at the final payload digest boundary
    ≡ DigestMismatch
    ≡ reason code 0x01
```

The code is therefore derived from the exact digest-failure control-flow edge. This is not recovery from ambient state and does not add a runtime check. Any future source program that distinguishes multiple peer-visible digest failure reasons must introduce a correspondingly richer semantic type and a new ABI profile.

## Rejected response payload encoding

The Phase 0 rejected-response payload is exactly 2 octets:

```text
+--------+-----------------------+
| byte 0 | byte 1                |
+--------+-----------------------+
| 0x00   | 0x01 DigestMismatch   |
+--------+-----------------------+
```

- response tag `0x00`: rejected;
- reason code `0x01`: `DigestMismatch`;
- every other reason code is reserved in v1 and must not be emitted by a conforming v1 encoder.

Together with `accepted-response-v1`, the final response payload family is therefore:

```text
0x00 || 0x01                    rejected(DigestMismatch)
0x01 || UploadIdToken[16]       accepted(id)
```

## Ownership and ordering

The rejected response is reachable only from the digest-validation failure edge. The exact payload owner returned by exact receive must be released before the rejected response is emitted. Storage must not run on this path.

The Systems witness and LLVM translation validator check this ordering and identity explicitly.

## Framing boundary

The two octets above are response payload bytes. This profile deliberately does not define an outer frame envelope, length prefix, transport packetization, buffering policy, or retry mechanism.

The source `select rejected(reason)` operation has no physical-write failure branch. Accordingly, this profile does not invent one. Failure of the runtime provider to emit the declared bytes remains an explicit residual runtime assumption/evidence boundary.

## Certification boundary

`PHIL-LLVM-CERT-007` binds the exact Systems source identity, canonical pre-optimization LLVM module/text, target identity, and this ABI descriptor. It certifies:

- exact digest-failure predecessor identity;
- exact payload-owner release before emission;
- exact transport identity;
- explicit `DigestMismatch -> i8 0x01` lowering;
- elimination of the generic nullary `select rejected` call;
- absence of ambient rejection/digest-error state;
- preservation of the already-materialized accepted response in the successor profile.

The following remain independent external gates:

- LLVM 18 acceptance;
- exact C-provider signature conformance;
- exact `00 01` runtime output;
- native linking and execution;
- physical transport write behavior and outer framing.
