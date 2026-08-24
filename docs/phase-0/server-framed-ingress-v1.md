# Phase 0 server framed ingress and recognition-failure ABI v1

## Scope

This target makes the server-side `Hello`/`Begin` framed-ingress lifecycle physical for the semantic artifact that already preserves grammar-specific recognition failure reasons.

The runtime profile is:

```text
phil-runtime/phase0/server-framed-ingress-v1
```

It is deliberately content-bound to the `RecognitionFailureBundle` / #96 Systems artifact. Repository `main` now also contains the later storage-failure semantic successor and its proofs, but this target does **not** claim physical authority for `server.storage_error`.

## Receive-frame boundary

For each grammar `G` in `{Hello, Begin}`:

```text
phil_runtime_receive_frame_G(
  ptr transport,
  ptr pending_out,
  ptr frame_out) -> void
```

receives exactly one complete framed value or does not return normally. Normal return initializes both output slots:

- `pending_out` receives the exact opaque pending-ingress handle;
- `frame_out` receives the exact opaque frame-owner handle.

There is no ambient current transport, current frame, or current pending object.

The semantic borrowed raw view lowers to:

```text
phil_runtime_frame_borrow_view_G(ptr frame) -> ptr
```

The returned view aliases the exact frame without copying and remains valid through recognition.

## Recognition result

Recognition is:

```text
phil_runtime_recognize_G(
  ptr pending,
  ptr raw_view,
  ptr record_out,
  ptr reason_out) -> i8
```

The exact semantic pending handle and exact borrowed view are explicit inputs.

Status discipline is fail-closed:

- `1`: success; `record_out` is the grammar-specific record handle and `reason_out` is null;
- any other value: failure; `record_out` is null and `reason_out` is a valid grammar-specific `RecognitionReason[G]` handle.

Thus the source-level failure reason is produced by the same physical recognition operation that selects the failure edge. There is no later ambient lookup or reconstruction of the reason.

## Success lifecycle

On the success edge:

```text
phil_runtime_commit_ingress_G(ptr transport, ptr pending) -> void
```

commits the exact pending ingress to the exact server transport. The pending handle represents the runtime association with its received frame; no global current-frame state is required.

## Failure lifecycle

On the recognition-failure edge:

```text
phil_runtime_fail_recognition_G(ptr pending, ptr reason) -> void
phil_runtime_destroy_pending_G(ptr pending, ptr frame) -> void
```

The first call forwards the exact grammar-specific reason produced by recognition. The second destroys the exact pending/frame pair already materialized by `receive_frame_G`.

This preserves the semantic order:

```text
recognize failure(reason)
  -> fail recognition(pending, reason)
  -> destroy pending(pending, frame)
  -> fatal RecognitionFailure[G]
```

The generic `phil_cleanup()` placeholder is no longer used on these two recognition-failure paths.

## Competence boundary

This tranche fixes the physical identities and lifetime relations for:

- framed receive;
- pending and frame ownership;
- no-copy raw view;
- recognition record/reason result;
- ingress commit;
- recognition failure forwarding;
- recognition-failure pending/frame destruction.

It does not yet provide:

- the concrete wire encoding shared with the client serializer;
- physical storage-failure error detail;
- a general replacement for cleanup operations on unrelated failure paths;
- a whole-program target certified against the latest StorageFailure Systems artifact.

Concrete `Hello`/`Begin` wire bytes become the natural next integration gate between this server target and `client-control-send-v1`.
