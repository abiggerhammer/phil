# Phase 0 client control-send ABI v1

## Scope

This target successor gives the explicit client outbound semantics from `client-outbound-semantics-v1` a physical LLVM/runtime boundary while preserving the already-lowered exact payload send.

It covers the client-side runtime operations needed to produce and send the semantic `Hello` and `Begin` records. It does **not** invent a byte layout that the frozen Phase 0 documents have not selected. Concrete byte encoding remains a runtime-provider gate; the compiler/runtime ABI fixes the exact values that serializer/framing code must consume.

The runtime ABI profile is:

```text
phil-runtime/phase0/client-control-send-v1
```

and extends:

```text
phil-runtime/phase0/transport-exact-send-v1
```

## Source authority after #98

This backend profile remains deliberately content-bound to the `client-outbound-semantics-v1` Systems artifact introduced by #94. Repository `main` now also contains the later recognition-failure and storage-failure semantic successors from #96 and #98, plus the proof harvest landed in #97, but those later Systems source digests are **not** claimed by this target.

That separation is intentional. The client-control-send profile is competent for the explicit client `Hello`/`Begin` construction, serializer/send operands, explicit offered-version identity, and exact payload send. It is not yet competent to lower the new server-side recognition-reason or storage-error identities. Those remain for later physical ABI tranches before an integrated whole-program target can be certified against the latest Systems artifact.

Merging this implementation onto current repository history therefore adds a coexisting content-bound backend target; it does not replace, regress, or broaden the authority of the latest Systems candidate or the proof-bound exact-send artifacts from #97.

## Supported versions

The source operation:

```text
supported_versions() -> client.supported_versions
```

lowers to:

```llvm
%client_supported_versions = call ptr @phil_runtime_supported_versions()
```

The pointer is an opaque provider-managed `VersionSet` handle. The provider obligation is that it denotes the exact source-level supported-version set and that the source's discharged nonempty-set contract remains true.

The handle must remain valid through the later selected-version refinement.

## Hello construction and send

The semantic sequence:

```text
construct Hello(client.supported_versions) -> client.hello
send Hello(client.transport, client.hello)
```

has no other observation of `client.hello`. The target therefore fuses record materialization and serialization/send:

```llvm
call void @phil_runtime_send_hello(
  ptr %client_transport,
  ptr %client_supported_versions)
```

The primitive must serialize and submit exactly one complete framed `Hello` corresponding to the frozen grammar and exact version-set operand. Because the source send has no recoverable failure edge, physical failure must not return normally.

No target-side `client.hello` record handle is introduced.

## Explicit version-refinement identity

Earlier physical version-choice lowering used:

```text
phil_runtime_refine_selected_version(ptr, i16)
```

and left a provider obligation that transport-local state somehow remembered the exact set previously sent in `Hello`.

That ambient equivalence is unnecessary once the client version set is explicit. This profile supersedes that operation with:

```text
phil_runtime_refine_selected_version_with_set(ptr, ptr, i16) -> i1
```

whose operands are:

1. exact client transport;
2. the **same `client.supported_versions` handle passed to `send_hello`**;
3. decoded selected version.

The runtime returns true iff the selected version is a member of that explicit set. Ambient offered-version state is forbidden.

## Payload borrow, length, kind, and digest

The semantic shared borrow:

```text
borrow client.payload -> client.payload_view
```

introduces no physical copy. The view erases to the exact existing payload-owner handle:

```text
client.payload -> client.payload.owner
```

and the target derives the Begin operands with:

```llvm
%client_declared_digest = call ptr @phil_runtime_sha256(
  ptr %client_payload_owner)

%client_payload_length = call i64 @phil_runtime_payload_length(
  ptr %client_payload_owner)

%client_payload_kind = call ptr @phil_runtime_payload_kind(
  ptr %client_payload_owner)
```

`PayloadKind` and `SHA256Digest` are opaque provider-managed pointers in this profile. The SHA-256 provider obligation is exact: the returned digest denotes SHA-256 of the bytes owned by the exact client payload handle.

## Begin construction and send

The semantic record:

```text
Begin.length    = client.payload_length
Begin.kind      = client.payload_kind
Begin.digestAlg = sha256
Begin.digest    = client.declared_digest
```

is constructed and immediately sent exactly once. The target fuses construction with serializer/send:

```llvm
call void @phil_runtime_send_begin_sha256(
  ptr %client_transport,
  i64 %client_payload_length,
  ptr %client_payload_kind,
  ptr %client_declared_digest)
```

The symbol itself fixes `digestAlg = sha256`; no target enum is required. No target-side `client.begin` handle is introduced.

As with `Hello`, runtime failure must not return normally because the source send has no recoverable failure continuation.

## Concrete framing boundary

This ABI deliberately distinguishes two claims:

- **compiler translation claim:** the exact source semantic operands reach explicit serializer/send primitives with no ambient record, transport, payload, or offered-version lookup;
- **runtime codec claim:** the provider implements the frozen `Hello` and `Begin` grammar/framing contract for those exact operands.

The first is translation-validatable in this tranche. The second remains a runtime/native integration gate until the concrete byte codec is supplied and tested end-to-end against server ingress.

This distinction avoids silently choosing a wire layout in LLVM while still eliminating the previous generic/nullary send boundary.

## Preserved exact payload send

The later payload operation remains:

```llvm
call void @phil_runtime_send_exact(
  ptr %client_transport,
  ptr %client_payload_owner)
```

with the `transport-exact-send-v1` ownership and whole-send/nonreturn contract unchanged.

## Competence boundary

This tranche does not lower server framed ingress or recognition failure detail. Those belong to the matching server-side physical boundary, where the runtime must surface the explicit recognition reasons landed in #96.

It also does not revise storage failure representation; that remains independent of this client outbound ABI.
