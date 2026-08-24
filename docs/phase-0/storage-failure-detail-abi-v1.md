# Phase 0 storage failure detail ABI v1

## Scope

This target extends the `server-framed-ingress-v1` physical chain and advances source authority from the #96 recognition-failure Systems artifact to the #98 storage-failure Systems artifact.

The semantic storage edge is:

```text
store(payload)
  success(id) -> accepted(id)
  failure(err) -> fail internal(err)
```

The payload is transferred into storage before either outcome. The failure arm may therefore observe the storage error, but must not inspect, release, or otherwise reuse the payload.

## Runtime profile

```text
phil-runtime/phase0/storage-failure-detail-v1
```

The store primitive is:

```c
uint8_t phil_runtime_store_with_error(
    void *payload,
    void **upload_id_out,
    void **storage_error_out);
```

The compiler initializes both output slots to null before the call.

Status `1` means success. Every other status means failure.

On success:

- `upload_id_out` contains the exact opaque upload-id handle;
- `storage_error_out` remains null;
- payload ownership has been consumed.

On failure:

- `upload_id_out` remains null;
- `storage_error_out` contains the exact opaque storage-error handle;
- payload ownership has still been consumed.

The failure effect is:

```c
void phil_runtime_fail_storage(
    void *transport,
    void *storage_error);
```

Its arguments are the exact server transport and exact error returned by the failed store operation. The component terminates immediately after this effect.

## Fusion of semantic error materialization

The #98 Systems artifact contains a semantic operation that materializes `server.storage_error` on the dedicated storage-failure edge. At this physical boundary, that materialization is fused into the store result itself.

There is therefore no target-side nullary `materialize storage failure error` call and no ambient `current_storage_error` state.

## Ownership

The source `TermStore` consumes the exact `server.payload` owner on all outcomes. This target preserves that rule:

- the payload pointer is passed exactly once to `phil_runtime_store_with_error`;
- neither successor observes the payload;
- the storage-failure effect receives only `(server.transport, server.storage_error)`.

## Representation

`UploadId` and `StorageError` remain opaque provider-managed pointers. This profile selects neither internal layout nor wire encoding for either handle.

## Competence boundary

This target inherits the #104 explicit client control-send and server framed-ingress/recognition boundaries.

It does not yet provide the shared concrete `Hello`/`Begin` wire codec. Framing and recognition operate through explicit grammar-specific runtime primitives, but the actual frozen byte representation remains the next codec/integration obligation.

The source-to-Systems bridge and integrated native demonstrator also remain separate Phase 0 obligations.
