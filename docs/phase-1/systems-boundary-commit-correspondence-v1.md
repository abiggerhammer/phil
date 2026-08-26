# Phase 1 Systems boundary owner/length and commit correspondence v1

Status: bounded executable conformance slice for `SYS-010`.

## Governing rule

A concrete send or receive path may realize a source boundary transition only when it preserves the exact boundary byte subject, owner, length semantics, runtime boundary authority, and protocol commit point.

In particular, a target may not:

- substitute a borrowed view or unrelated owner for the source byte owner;
- preserve the same bytes while changing the source semantic subject;
- receive with a different runtime length value;
- send a differently indexed owned-byte object;
- use receive evidence to justify a send boundary, or vice versa;
- advance the protocol endpoint before complete send emission; or
- turn a receive failure into a live protocol successor.

## Source authority

`BoundaryTransferContract` does not invent a second free-form boundary proof. Each transfer names an existing source fact in the wrapped `StageContract`.

For the upload witness these are:

- `payload.exact_receive`; and
- `payload.exact_send`.

The verifier requires the named fact to have:

1. an exact source `RevisionId`; and
2. a `FactRuntimeRetained` evidence entry.

The selected target runtime site must carry exactly that revision and evidence entry and must have the direction-appropriate runtime kind:

- `ExactReceiveBoundary`; or
- `ExactSendBoundary`.

This prevents target-local metadata from making an incorrect boundary self-consistent.

## Exact byte subject and owner

Every transfer names one SYS-004 `SourceSubjectKey` and one exact `(function, ValueId)` owner.

The owner must:

- occur in that already-checked subject correspondence;
- be an `OwnedBuffer`, never a `BorrowedSlice`; and
- carry the exact expected owned-byte shape.

SYS-010 therefore reuses SYS-004 semantic-subject authority rather than introducing a boundary-specific notion of byte identity.

The upload SYS-004 witness is extended with a second independent stable subject:

- `upload.payload.server` -> server payload owner and its digest borrow; and
- `upload.payload.client` -> client payload owner.

The server and client objects are different semantic subjects even when they describe corresponding protocol bytes.

## Length representation

The bounded Systems IR has two intentional length representations.

### Exact receive

`TermReceiveExact` carries an explicit runtime length `ValueId`. The boundary contract therefore uses `ExplicitBoundaryLength`, binding:

- a source semantic length key; and
- the exact Systems length value.

For upload the receive relation is:

```text
begin.length
    -> UploadServer:server.begin_length
```

and the exact receive owner is:

```text
UploadServer:server.payload : OwnedBuffer "Bytes[begin.length]"
```

### Exact send

`TermSendExact` deliberately carries the owned byte object rather than a separate length SSA operand. The frozen Phase-0 upload send has the same semantic shape in its exact-send runtime boundary: the target receives exactly `[transport, owner]`, where the owner itself is indexed by the source length.

The boundary contract therefore uses `OwnerIndexedBoundaryLength` for sends. Upload requires:

```text
payload.length
    -> UploadClient:client.payload
       : OwnedBuffer "Bytes[payload.length]"
```

This is not permission to infer arbitrary lengths from implementation buffers. The semantic length key and exact required owner shape are explicit StageContract relation data.

## Commit point

Every boundary transfer also names one exact SYS-009 protocol transition and one success outcome.

The verifier requires:

- the protocol transition's target site to be exactly the boundary emission/receive site;
- the same exact transport value;
- the declared commit outcome to produce a fresh protocol successor; and
- any declared failure outcome to remain terminal.

For the frozen client send, the relevant block is:

```text
client.payload:
    operation 0: select payload
    operation 1: send_exact(client.transport, client.payload)
                 @ ExactSendBoundary
    operation 2: receive accepted/rejected
```

SYS-010 extends the upload protocol witness with a client endpoint transition whose success successor is attached to **operation 1**. Moving that successor to operation 0 is the explicit early-send mutation and is rejected.

Thus physical transport reuse remains legal, while protocol progression cannot precede complete-frame emission.

## Frozen Phase-0 exact-send bridge

The generic Phase-1 stage stack still intentionally wraps the frozen Phase-0 Systems artifact. Its client exact send predates `TermSendExact` and appears as an `OpRuntimeCall` carrying:

- exact inputs `[client.transport, client.payload]`;
- no outputs; and
- the exact `ExactSendBoundary` runtime site.

SYS-010 does **not** infer send semantics from the runtime-call name. The operation is accepted only because:

- the exact target site is named;
- the exact source `payload.exact_send` fact binds the runtime site revision/evidence;
- the exact owner and transport operands are checked; and
- the SYS-009 client transition uses an explicit checked legacy protocol bridge.

A future fully normalized artifact using `TermSendExact` is checked by the same boundary relation without that legacy operation representation.

## Upload witness

The receive transfer checks:

```text
subject     = upload.payload.server
owner       = UploadServer:server.payload
length      = UploadServer:server.begin_length
source fact = payload.exact_receive
site        = UploadServer:server.payload terminator
commit      = receive-payload success successor
failure     = EarlyEOF terminal
```

The send transfer checks:

```text
subject     = upload.payload.client
owner       = UploadClient:client.payload
length      = payload.length, owner-indexed
source fact = payload.exact_send
site        = UploadClient:client.payload operation 1
commit      = client exact-send success successor
```

## Conformance corpus

The dedicated corpus requires:

- real upload receive/send acceptance;
- rejection of a borrowed receive view substituted for the owner;
- rejection of the wrong explicit receive length value;
- rejection of the server byte subject used for the client send owner;
- rejection of a mismatched owner-indexed send length;
- rejection when receive boundary evidence is used for send;
- rejection when the send successor is moved before complete emission;
- rejection when send success becomes terminal instead of producing its successor;
- rejection when receive failure produces a live successor; and
- deterministic boundary-stage identity under map ordering.

## Deferred

This slice does not yet implement evidence-copy correspondence (`SYS-011`), erasure (`SYS-012`), assumption laundering (`SYS-013`), target strengthening (`SYS-014`), runtime carrier/site multiplicity, staging effects/costs, next-stage ABI requirements, or final compact semantic digests.

It also does not replace the frozen Phase-0 upload artifact with the later normalized session/boundary candidate; that migration belongs to the post-SYS canonical source/parser integration tranche rather than being smuggled into one StageContract conformance row.
