# Architecture instantiation production binding v1

## Status

Production-binding closeout for the executable decision surface of Certified `PHIL-ARCH-INST-001`.

## Purpose

`PHIL-ARCH-INST-001` is Certified and #394 staged a representation-neutral executable kernel for the finite decisions already present in that theorem family. This closeout checks in the exact harvested kernel and routes the corresponding production acceptance/rejection seams through it without strengthening the Certified model.

The base architecture occurrence identity used by instantiation is already production-bound through `PHIL-ARCH-ID-IMPL-001`. This slice therefore focuses on the remaining Certified instantiation decisions rather than re-proving identity construction.

## Exact extracted kernel

`src/ArchitectureInstantiationKernel.hs` is the byte-identical Rocq extraction harvested from #394:

- `decideChildSlotByFacts`;
- `decideArchitectureRequirementByFacts`;
- `decideRootRequirementByFacts`; and
- `decideArchitectureReferenceByFacts`.

The #394 extraction identity is SHA-256 `2fb3efaca94102faf4576c4a8a38e9bb148ef8de058c3e86d595fedf2daefbad`. The production-binding workflow fresh-extracts with Rocq 9.2.0 and requires byte-for-byte identity with the checked-in source before testing production.

## Production binding

`Phil.Core.Static` now reflects concrete finite native facts into the extracted kernel and maps the kernel decision back to the existing production diagnostics.

### Child occurrence slots

`normalizeChildren` reflects whether the stable `OccurrenceSlotKey` is absent from the already-normalized child map. The extracted child-slot decision owns accept-versus-duplicate. Production inserts only on `ChildSlotAccepted`; `ChildSlotDuplicate` preserves the existing `DuplicateOccurrenceSlot` diagnostic.

### Architecture requirements

For each checked requirement, production reflects exactly four facts:

1. whether an explicit disposition exists;
2. whether that disposition is `RequirementBoundTo`;
3. whether the named target occurrence exists in the checked graph; and
4. whether the exact required `InterfaceRevision` matches when one is required.

The root occurrence calls `decideRootRequirementByFacts`; other occurrences call `decideArchitectureRequirementByFacts`. The Certified kernel therefore owns accepted, unresolved, missing-target, and interface-mismatch outcomes. Native code retains the existing detailed error payloads. If a kernel rejection cannot be reconciled with the reflected native shape needed to construct its diagnostic, production terminates fail-closed rather than manufacturing success.

An absent exact interface requirement is reflected as a successful interface fact once a bound target exists, because the Certified Boolean is only a guard for an exact-interface constraint. A missing bound target remains a missing-target decision before that interface fact is consulted.

### Explicit references

Reference validation reflects whether the exact target `InstanceKey` is present in the checked graph. The extracted reference decision owns accept-versus-unknown-target; production retains the existing `UnknownArchitectureReferenceTarget` payload.

## Native representation boundary

The following remain explicit primitive implementation/correspondence foundations rather than claims of the Rocq theorem:

- `Data.Map.Strict` normalization, membership, lookup, traversal, and uniqueness behavior;
- native equality of `InstanceKey`, `OccurrenceSlotKey`, and `InterfaceRevision`;
- truth of the reflected target-existence and exact-interface-match facts;
- concrete `Text`-backed key representations;
- source occurrence-site elaboration and environment lookup; and
- concrete graph construction and traversal.

These facts select inputs to the extracted decisions; handwritten production code no longer owns the semantic accept/reject decision at the bound seams.

## Deliberate non-scope

`deriveGraphInstanceIdentity` still constructs the graph-specific outer `InstanceRevision` from the already-bound base instance revision plus canonicalized requirement/child/reference semantic bindings. The current Certified `ArchitectureInstantiation.v` model does not characterize that richer serialization. This closeout therefore does not claim Rocq ownership of `phil.instance.graph.canonical.v1`, its `SemanticForm` encoding, or collision/injectivity properties.

Architecture realization remains `PHIL-ARCH-REALIZE-001`. Runtime initialization authority is not introduced by this binding.

## Validation

The dedicated production-binding workflow must:

- recompile Certified `ArchitectureIdentity.v` and `ArchitectureInstantiation.v` plus the #394 implementation characterizations;
- fresh-extract `ArchitectureInstantiationKernel.hs` and require byte-for-byte identity with `src/ArchitectureInstantiationKernel.hs`;
- strict-typecheck the exact checked-in kernel under `-Wall -Werror`;
- execute the unchanged ten-case direct kernel control harness;
- build `lib:phil-core` and the scalar proof certifier under warnings-as-errors;
- strict-typecheck `Phil.Core.Static` and the unchanged ARCH-005/006/008/009 corpus through the production source path;
- rerun all eleven existing architecture-instantiation cases; and
- record exact kernel, production module, package description, corpus, and control-harness identities in a dedicated production-binding artifact.

An all-green exact head is sufficient to mark the Certified architecture-instantiation row `Implementation Refined` for this bounded theorem surface, while retaining the graph-specific outer revision and the native finite-map/representation facts above as explicit boundaries.
