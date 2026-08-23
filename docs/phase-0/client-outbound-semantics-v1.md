# Phase 0 client outbound semantics v1

## Scope

This tranche closes the remaining semantic compression in the first half of the frozen upload client. It does **not** choose a physical codec, record layout, framing format, transport ABI, or SHA-256 implementation.

The frozen source constructs and sends two semantic records:

```phil
let versions = supported_versions()
prove len(versions) > 0

let hello = construct Hello {
    versions = versions
}
let session1 = send hello on session0
```

and later:

```phil
let declaredDigest = borrow payload as payloadView {
    sha256(payloadView)
}

let begin = construct Begin {
    length = payload.length,
    kind = payload.kind,
    digestAlg = sha256,
    digest = declaredDigest
}
let session2 = send begin on session1
```

Earlier Systems candidates compressed those into bare `send Hello(transport)` and `send Begin(transport)` operations. That was adequate for proving protocol control but did not preserve the outbound record identities or their construction dataflow.

## Explicit client values

The successor Systems candidate materializes:

```text
client.supported_versions : RuntimeOpaque[VersionSet]
client.hello              : RuntimeRecord[Hello]
client.payload_view       : BorrowedSlice[client.payload]
client.payload_length     : UInt64
client.payload_kind       : RuntimeOpaque[PayloadKind]
client.declared_digest    : RuntimeOpaque[SHA256Digest]
client.begin              : RuntimeRecord[Begin]
```

`client.payload` and `client.transport` retain their predecessor identities.

## Hello dataflow

The entry block now represents:

```text
supported_versions()
  -> client.supported_versions

construct Hello(client.supported_versions)
  -> client.hello

send Hello(client.transport, client.hello)
```

The source proof `len(versions) > 0` remains compile-time evidence. This tranche deliberately introduces no runtime proof object for it.

The exact semantic relation is:

```text
client.hello.versions = client.supported_versions
```

Physical representation of the set and the `Hello` record remains target-selected.

## Begin dataflow

On the selected-version branch the candidate now represents:

```text
borrow client.payload
  -> client.payload_view

sha256(client.payload_view)
  -> client.declared_digest

project client.payload.length
  -> client.payload_length

project client.payload.kind
  -> client.payload_kind

construct Begin[sha256](
    client.payload_length,
    client.payload_kind,
    client.declared_digest)
  -> client.begin

send Begin(client.transport, client.begin)
```

The fixed `digestAlg = sha256` field is a static constructor fact, not a separately materialized runtime enum in this semantic layer.

The exact semantic relations are:

```text
client.begin.length    = client.payload_length
client.begin.kind      = client.payload_kind
client.begin.digestAlg = sha256
client.begin.digest    = client.declared_digest
```

and `client.declared_digest` is computed from the exact shared view of the same `client.payload` owner.

## Ownership and cost

Digest computation uses a non-owning `BorrowedSlice` and introduces no representation copy. The stage invariant

```text
invariant.client.payload.digest_borrow_no_copy
```

binds `client.payload_view` to `client.payload`.

SHA-256 work is attributed explicitly by `lower.client.outbound.sha256`; record/value materialization is attributed by `lower.client.outbound.records`; the shared loan is attributed by `lower.client.outbound.digest_borrow`.

This tranche does not change payload ownership transfer at `send_exact` or any existing session/failure path.

## Preservation

The successor must preserve the already-normalized:

- version session choice and selected-version refinement;
- BeginPolicy local validation plus peer-visible reject/proceed choice;
- HelloPolicy accepted/rejected(reason) local choice and terminal failure effect;
- payload/cancel and final-response session choices;
- exact receive, digest validation, storage, and response semantics.

The focused verifier reruns the relevant predecessor witnesses against the successor artifact.

## Physical competence boundary

Merged `PHIL-LLVM-CERT-013` certifies the predecessor Systems source digest used by `transport-exact-send-v1`. Adding explicit outbound values changes the Systems artifact digest, so that certificate does **not** automatically extend to this successor.

The next backend tranche must choose physical representations and ABIs for outbound `Hello`/`Begin` encoding and transport before any new translation certificate can cover this candidate.
