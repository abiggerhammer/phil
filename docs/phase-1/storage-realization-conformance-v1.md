# Phase 1 storage realization conformance v1

This slice implements the MEM-001–006 storage/allocation realization boundary without introducing a universal allocator, source-level `malloc`/`free`, or a target memory-space taxonomy.

## Competence boundary

`Phil.Systems.Storage` carries the storage-realization relation alongside the already-packaged Systems storage boundary and keeps three concepts mechanically distinct:

1. ordinary semantic value/resource creation;
2. explicit semantic storage-resource ownership; and
3. physical storage allocation/placement chosen by a realization.

A checked storage realization therefore binds one exact semantic subject plus exact source semantic/outcome revisions to opaque target strategy/object/revision coordinates. Physical storage coincidence is represented only as an invalid subject-binding form and always rejects.

## MEM-001 — allocation strategy is nonsemantic

Two checked realizations are semantically equivalent only when their exact semantic subject, source semantic revision, and source outcome revision agree. Physical strategy, physical storage-object identities, ArchitectureRealization revision, and cost lineage may differ.

This permits register/inline, heap, arena/region, device, DMA, persistent, or erased realizations to vary without redefining source identity, provided the other realization obligations close.

## MEM-002 / MEM-003 — allocation failure cannot widen source semantics

A possibly failing physical allocation is admitted only through one explicit disposition:

- exact mapping to a source-declared storage failure;
- checked capacity evidence proving the physical failure unreachable;
- an explicit accepted allocation/capacity assumption;
- an explicit deployment requirement; or
- rejection.

An unaccounted physical failure is rejected. Mapping to a failure not present in the exact source failure surface also rejects.

## MEM-004 / MEM-005 — semantic closure and physical reclamation are separate

`checkSemanticStorageTerminalClosure` reasons only about explicit semantic storage owners. A live semantic owner blocks terminal closure; released owners and exact contract-permitted terminal dispositions may close.

`checkPhysicalStorageReclamation` separately checks realization storage objects. Physical reclamation may be required or exact profile-scoped retention may be permitted. A physical leak is a realization defect, but it does not retroactively change an already-closed source semantic terminal fact.

## MEM-006 — storage cost lineage

Storage costs reuse the existing Systems `CostClass` and `CostShape` vocabulary. A checked lineage must bind the exact semantic subject and exact physical object domain of the checked realization and carry at least one attributable storage fact through allocation count, peak live memory, bytes copied, residency references, or cleanup references.

Different valid storage strategies may therefore expose materially different cost lineage while remaining the same source semantic computation.

## Validation

`test/Phase1StorageRealizationMain.hs` contains 18 focused cases covering:

- ordinary and explicit-storage allocation-strategy nonsemanticity;
- rejection of physical-object coincidence as semantic identity;
- distinct semantic subjects remaining distinct even over one physical object;
- allocation-failure mapping, capacity evidence, assumptions, deployment requirements, and unaccounted-failure rejection;
- semantic storage terminal closure;
- physical leak/profile-reclamation separation; and
- distinct but attributable storage cost lineage.

The implementation is target-neutral. Concrete allocator behavior, capacity/evidence truth, target layout/address spaces, runtime reclamation correctness, and Haskell implementation equivalence remain explicit realization/evidence boundaries for later proof and implementation-refinement work.
