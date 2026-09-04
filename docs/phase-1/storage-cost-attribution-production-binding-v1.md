# Storage Cost Attribution production binding v1

`PHIL-MEM-COST-001` was Certified by the Storage Cost Attribution proof and its machine-facing correspondence surface was staged by PR #679. This closeout binds production MEM-006 storage-cost acceptance to the exact extracted kernel while continuing to reuse the already production-bound Systems runtime-cost graph for contribution/final-charge authority.

## Exact kernel

The checked-in copies are byte-identical to the #679 extraction artifact:

- `generated/StorageCostAttributionKernel.hs`
- `src/StorageCostAttributionKernel.hs`
- SHA-256: `9b2ba9be6582f34288da985c7e9f07c559cc29d4c493ac17fee982edab3942a2`

The extracted file is 2,084 bytes and ends with two newline bytes.

The kernel exposes six gates:

1. exact storage semantic subject;
2. exact physical-storage object domain;
3. attributable storage cost via allocation count, peak live memory, bytes copied, residency reference, or cleanup reference;
4. aggregate storage-cost lineage validity;
5. storage-to-runtime contribution/charge/class/shape binding; and
6. Certified storage-cost composition from realization validity, runtime-graph validity, and lineage validity.

## Production composition

`Phil.Systems.StorageCostAttributionCertification` composes existing production authorities rather than replacing them.

### Storage lineage

`checkStorageCostLineageCertified` first calls the unchanged `checkStorageCostLineage`. Native diagnostics therefore keep precedence for:

- subject mismatch;
- physical-domain mismatch;
- malformed residency/cleanup identities; and
- missing attributable storage facts.

Only after native success does the bridge independently reflect the exact checked semantic subject, exact checked physical-object set, the three `CostShape` memory fields, and nonempty residency/cleanup reference sets. It then requires the exact extracted subject, domain, attribution, and aggregate-lineage gates. A native-success/kernel-reject disagreement fails closed with the reflected facts.

### Runtime-cost binding

The proof-facing `StorageRuntimeCostBinding` is represented concretely by one existing SYS-018 `CostContributionIdentity` and its `CostChargeIdentity`.

`checkStorageRuntimeCostBindingCertified` first calls `verifyStageClosureBundle`. That is already the production integration point for the complete native SYS-015/016/018 chain and the exact `SystemsRuntimeGraphKernel`. The bridge then reads the verified `CostAttributionStageBundle` from the StageClosure next-stage chain and requires:

- the selected contribution exists;
- its functional contribution→charge map entry equals the requested final charge;
- the contribution's `CostClass` equals the storage lineage's class; and
- the contribution's complete `CostShape` equals the storage lineage's shape.

Those facts are then required to pass the exact extracted storage/runtime binding gate. No second cost graph or duplicate charge registry is introduced.

### Certified composition

`certifyStorageCostAttribution` composes:

1. implementation-refined `checkStorageRealizationCertified` (MEM-001);
2. native-first and kernel-gated MEM-006 storage lineage;
3. production-bound `verifyStageClosureBundle`, including the runtime-cost graph;
4. the exact storage→runtime contribution/charge/class/shape binding; and
5. the exact extracted `decideCertifiedStorageCostAttributionByFacts` outer gate.

A green exact-head merge promotes `PHIL-MEM-COST-001` from **Certified** to **Implementation Refined**.

## What this does not claim

This closeout still does not assert one universal numeric memory-cost model. The following remain selected ADR-011 profile/correspondence/TCB boundaries:

- concrete numeric allocation, peak-live-memory, copy, residency, or cleanup values;
- target/provider meanings of those categories;
- correctness and completeness of concrete `Map`, `Set`, list, and `Text` enumeration;
- truth/provenance of selected `CostClass` and `CostShape` profile data;
- allocator/runtime/provider behavior;
- canonical hashing and serialization outside the already-certified stage chain;
- Rocq extraction/compiler correctness, GHC correctness, and runtime correctness.

Different valid storage strategies may therefore retain different valid cost lineage while preserving the same source semantic identity.

## CI closeout

The dedicated production-binding workflow must:

- freshly compile the Certified storage realization, runtime graph, storage-cost proof, and #679 implementation correspondence under Rocq 9.2.0;
- freshly extract `StorageCostAttributionKernel.hs`;
- require SHA-256 `9b2ba9be6582f34288da985c7e9f07c559cc29d4c493ac17fee982edab3942a2` and byte-compare both checked-in copies;
- build the broad Haskell regression surface;
- strict-typecheck the native storage/cost/runtime integration and the new bridge;
- execute the unchanged 22 direct #679 kernel controls through the production mirror;
- rerun the implementation-refined MEM-001 production bridge;
- rerun the direct Systems runtime-graph controls;
- execute real production MEM-006 binding controls through `uploadStageClosureBundle`; and
- rerun the unchanged MEM-001--006, SYS-018, and final StageClosure corpora.
