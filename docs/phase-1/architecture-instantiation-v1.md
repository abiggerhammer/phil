# Phase 1 architecture instantiation v1

This tranche implements the first executable substrate for logic-ledger obligation `PHIL-ARCH-INST-001` and the ArchitectureInstance Semantics and Instantiation Contract.

It establishes a finite, target-abstract checked architecture graph in which:

- each new contained occurrence is generated from an exact parent `InstanceKey` and stable `OccurrenceSlotKey`;
- equal declarations and equal static arguments at distinct occurrence slots remain distinct semantic instances;
- the same stable child slot under distinct parent occurrences remains distinct;
- explicit references share an already existing `InstanceKey` and never create a second occurrence;
- identity-bearing static arguments and architecture binding choices revise `InstanceRevision` without changing stable occurrence lineage;
- every architecture-level requirement has an explicit disposition;
- a singular provider/callable/capability requirement is never satisfied by ambient search, candidate ranking, or dependency injection;
- an explicit binding names one exact semantic occurrence and may require its exact `InterfaceRevision`;
- re-export/runtime/assumption/deployment boundaries remain explicit architecture dispositions rather than unresolved holes; and
- construction is purely static graph construction and performs no runtime initialization.

The implementation deliberately retains full requirement declarations in the checked graph. Exact expected interfaces and unresolved states therefore remain available to the validation pass instead of being erased into a smaller disposition map.

The graph layer extends the stable instance identity from the preceding architecture-identity tranche with a versioned canonical semantic graph revision. It does not mutate the public `ArchitectureInstanceDescriptor` shape merely to add graph bookkeeping.

## Conformance exercised

The dedicated Phase 1 harness covers the current `ARCH-005`, `ARCH-006`, `ARCH-008`, and `ARCH-009` pressure cases, including distinct equal-looking occurrences, explicit sharing, nested generativity, stable occurrence keys under semantic edits, missing root authority, refusal of ambient provider selection, exact-interface provider binding, missing binding targets, duplicate slots, explicit re-export, and invalid sharing targets.

## Deliberate limits

This tranche does **not** claim the Rocq proof for `PHIL-ARCH-INST-001` yet. It does not introduce final source syntax, module/import semantics, provider implementation qualification, protocol projection, capability structural checking, or generic Architecture/Core → Systems lowering.

The current binding vocabulary is the architecture-level closure substrate only. Later tranches will refine typed provider/callable/protocol/capability edges as their governing checker contracts land; they must preserve the no-ambient-binding and occurrence-generativity rules established here.
