# Phase 0 storage failure detail — v1

## Purpose

The frozen upload server source binds `failure(err)` from `store(payload)` and forwards that exact value into `fail internal(err) on session5`.

The predecessor Systems artifact preserves the storage success/failure control split and the payload-consumption contract, but the failure arm contains only `TermFatal "StorageFailure"`. The source error identity is therefore lost.

This semantic tranche restores that information without choosing a physical storage-error representation or changing the storage runtime ABI.

After recognition-failure detail landed, this tranche composes on `RecognitionFailureBundle` rather than reconstructing from the older client-outbound predecessor. The storage successor therefore preserves the exact grammar-specific `Hello` and `Begin` recognition reasons as well as the new storage error identity.

## Successor value

The dedicated storage failure edge binds:

```text
server.storage_error : RuntimeOpaque[StorageError]
```

The value exists only to preserve the source-level failure payload and is not an upload ID, payload owner, diagnostic string, errno, or target ABI object.

## Exact flow

The existing storage terminator remains authoritative:

```text
TermStore
  owner   = server.payload
  result  = server.upload_id
  site    = StorageBoundary
  success = server.accepted
  failure = server.storage_failure
```

On the dedicated failure edge, the successor requires:

```text
materialize storage failure error()
  -> server.storage_error

fail internal storage(
  server.transport,
  server.storage_error)

fatal StorageFailure
```

`server.storage_error` has exactly one semantic observation: the matching fatal internal-failure effect.

## Payload ownership

`store(payload)` already consumes the payload on all outcomes. The failure arm therefore must not observe, borrow, copy, release, or clean up `server.payload`.

The error binding is branch-local semantic information produced by the failed storage operation; it does not restore ownership of the transferred payload.

## Predecessor preservation

The focused verifier reruns the recognition-failure witnesses on the storage successor. Both of these must remain present and one-use:

```text
server.hello_recognition_reason : RuntimeOpaque[RecognitionReason[Hello]]
server.begin_recognition_reason : RuntimeOpaque[RecognitionReason[Begin]]
```

Thus the storage tranche extends, rather than replaces, the recognition-detail semantic successor.

## ADR-011 decision

The normalization adds:

```text
lower.storage.failure_detail
```

The decision is `SemanticRequired` and records one failure-only semantic binding/forwarding effect. It adds no payload copy, no retained proof machinery, and no new dynamic assurance check.

## Physical competence boundary

The existing `phil-runtime/phase0/storage-v1` profile returns `{status, upload-id}` and requires a null upload ID on failure. That profile therefore does not physically represent the newly explicit `StorageError` value.

A later physical tranche must revise or supersede the storage ABI so failure surfaces an exact error identity, and must separately choose:

- concrete error representation;
- provider ownership/lifetime;
- fatal diagnostic/reporting ABI;
- whether rich provider diagnostics remain runtime-local or cross a Phil-visible boundary.

No existing content-bound LLVM certificate is broadened by this semantic normalization.
