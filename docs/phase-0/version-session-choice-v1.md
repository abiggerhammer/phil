# Phase 0 version/unsupported session choice — Systems v1

## Purpose

This note records the semantic normalization of the Phase 0 `version(selected)` / `unsupported` protocol choice after `choose_supported` has already been represented as a local `TermRuntimeChoice` with branch-local `server.selected_version : UInt16`.

The source-level shape is:

```text
choose_supported(...) {
  none(noCommon) => select unsupported
  some(version, offered, supported) => select version(version)
}
```

The peer offers the dual choice and binds the selected version on the `version` arm.

## Server representation

The local decision remains local:

```text
server.version.choose:
  TermRuntimeChoice choose_supported {
    none -> server.unsupported
    some -> bind server.selected_version : UInt16 -> server.version
  }
```

The subsequent peer-visible protocol operations are normalized to semantic selects:

```text
server.unsupported:
  OpSessionSelect server.transport "unsupported" Nothing

server.version:
  OpSessionSelect server.transport "version" (Just server.selected_version)
```

This preserves the distinction between:

- local result constructors `none` / `some` chosen by `choose_supported`; and
- protocol labels `unsupported` / `version` selected for the peer.

## Client representation

The historical client representation:

```text
receive version/unsupported label -> client.version_branch : Bool
TermBranch client.version_branch client.version.check client.unsupported
```

is replaced by:

```text
client.entry:
  TermSessionOffer client.transport {
    unsupported -> client.unsupported
    version -> bind client.selected_version : UInt16 -> client.version.check
  }
```

The received payload identity is intentionally distinct from the server's Systems identity. Transport relates the semantic payloads; Systems does not pretend that one SSA/value identity crosses process or endpoint boundaries.

## Refinement flow

The client refinement gate now consumes exactly the branch-local received value:

```text
client.version.check:
  TermRuntimeCheck [client.selected_version] version-client-refinement
    client.version
    client.version_failure
```

Thus the semantic dataflow is explicit:

```text
choose_supported
    ↓
server.selected_version : UInt16
    ↓
select version(server.selected_version)
    ↓
peer/session boundary
    ↓
offer version(client.selected_version)
    ↓
client version refinement
```

The `unsupported` arm carries no runtime payload.

## Proof values

`noCommon`, `offered`, and `supported` remain proof/evidence authority and do not acquire runtime representations in this slice. The runtime datum that crosses the protocol boundary is only the selected `UInt16`.

## Dataflow discipline

`client.selected_version` is defined on the `version` offer edge and becomes live at `client.version.check` entry. It must not dominate or be usable from `client.unsupported`.

This uses the generic branch-edge definition semantics introduced for local runtime choices and shared with payload-bearing `TermSessionOffer` arms.

## Stage invariants

The local `choose_supported` stage invariant introduced by the predecessor remains unchanged: it still binds the exact local `none` / `some(server.selected_version)` computation. This slice does not rewrite that local-computation obligation into a protocol obligation.

The new lowering decision records the peer-visible semantic normalization separately.

## Backend competence boundary

No physical encoding is selected here.

In particular, this slice does **not** choose:

- a discriminator octet or bit pattern for `unsupported` / `version`;
- the byte order or wire layout of the `UInt16` payload;
- runtime ABI symbols;
- buffering or outer framing.

Generic LLVM lowering therefore remains fail-closed for these new semantic operations. The next target slice must explicitly choose and certify their physical representation.
