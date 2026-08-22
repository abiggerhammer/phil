# Phase 0 local runtime choice — Systems v1

## Purpose

This note records the first Systems representation for a **locally computed choice with branch-local payload data**.

The motivating source fragment is `choose_supported(serverSupported, hello.versions)`:

```text
none(noCommon)
some(version, offered, supported)
```

The historical Phase 0 Systems graph collapsed this to:

```text
choose_supported -> server.has_version : Bool
TermBranch server.has_version server.version server.unsupported
```

That representation preserved control flow but discarded the selected version.

## Representation

The successor IR adds a local-choice form distinct from peer-selected session choice:

```text
TermRuntimeChoice name inputs site {
  label -> (optional branch-local payload binding, target)
}
```

For the frozen upload demonstrator:

```text
server.version.choose:
  TermRuntimeChoice choose_supported {
    none -> server.unsupported
    some -> bind server.selected_version : UInt16 -> server.version
  }
```

The old `server.has_version : Bool` and the generic `choose_supported` output call are absent.

The existing generic `select version` operation is not normalized to `OpSessionSelect` in this slice, but it now consumes the exact branch-local runtime value:

```text
select version(server.transport, server.selected_version)
```

That is an intentional bridge to the next semantic session-choice slice.

## Local choice is not session offer

`TermRuntimeChoice` and `TermSessionOffer` are intentionally distinct even though both have labeled arms and optional branch-local payloads.

- `TermRuntimeChoice`: the running component/runtime chooses a local result constructor.
- `TermSessionOffer`: the peer chooses a protocol label.

Conflating the two would erase who has authority to choose the branch.

## Branch-edge definition

A branch payload is defined on the selected edge and becomes live at the target entry. For scalar dataflow, the binding is modeled at target index `-1`.

This matters because the `some(version)` binding must dominate `server.version` and its continuation, but must **not** dominate `server.unsupported`.

The same branch-edge rule is also applicable to future typed `TermSessionOffer` payloads.

For Phase 0, payload-bearing choice targets remain dedicated binder blocks with the choice block as their sole predecessor. General phi-like joins remain a future explicit representation problem.

## Proof values

The source arms also mention:

```text
noCommon
offered
supported
```

Those are proof/evidence values. This slice does not invent runtime representations for them. Existing assurance and erasure accounting remains responsible for their authority.

The runtime datum preserved here is only:

```text
version : UInt16
```

This is a concrete instance of the project rule that completed proof work should not automatically become runtime data.

## Backend competence boundary

No physical representation for `choose_supported` is selected here.

Generic LLVM lowering must fail closed on an unlowered `TermRuntimeChoice`; a later backend slice must explicitly choose how the local sum result and branch payload are produced.

Likewise, the wire representation of `version(selected)` is not selected here. That belongs to the subsequent session-choice normalization and physical-lowering slices.
