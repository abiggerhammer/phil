# Storage Cost Attribution implementation refinement v1

`PHIL-MEM-COST-001` is already Certified by `proof/Phil/Core/StorageCostAttribution.v`. This slice stages its representation-neutral executable correspondence without changing production behavior.

## Staged decision surface

`StorageCostAttributionImplementation.v` exposes six Boolean gates.

1. `decideStorageCostSubjectExactByFacts` reflects exact semantic-subject lineage.
2. `decideStorageCostPhysicalDomainExactByFacts` reflects equality of the lineage physical-object domain and the checked realization domain.
3. `decideAttributableStorageCostByFacts` accepts when at least one Certified storage-cost witness is present: allocation count, peak live memory, bytes copied, residency reference, or cleanup reference.
4. `decideStorageCostLineageValidByFacts` composes subject exactness, physical-domain exactness, and attributable-cost presence.
5. `decideStorageRuntimeCostBindingByFacts` requires exact contribution-to-charge membership plus exact selected cost class and shape. The Rocq correspondence also proves that accepted facts construct a `StorageRuntimeCostBinding`.
6. `decideCertifiedStorageCostAttributionByFacts` composes the already-Certified storage realization, already-Certified runtime-cost graph, and valid storage lineage for a fixed valid storage/runtime binding.

The fifth and sixth gates deliberately do not duplicate the generic Systems runtime-cost graph. `PHIL-SYS-RUNTIME-GRAPH-001` is already production-bound through `verifyStageClosureBundle`, where SYS-015/016/018 verify contribution/charge identity, nonduplication, and compatible shared-charge class/shape.

## Direct controls

`app/StorageCostAttributionDecisionCorrespondenceMain.hs` exercises:

- subject exact / mismatch;
- physical domain exact / mismatch;
- each of the five independent attributable-cost witness classes;
- no-attribution rejection;
- each lineage conjunct independently;
- contribution/charge membership, class, and shape independently; and
- each Certified aggregate predecessor independently.

## Production boundary

This staging slice does not modify `src/Phil/Systems/Storage.hs`, `src/Phil/Systems/CostAttribution.hs`, or StageClosure production behavior. A later production-binding slice must connect the exact extracted kernel to concrete `StorageCostLineage`, checked StorageRealization, and the already-refined Systems cost-attribution graph.

The following remain explicit correspondence/evidence boundaries:

- concrete `Text`, `Set`, `Map`, list and finite-enumeration representation;
- exact semantic-subject and physical-object-domain reflection;
- concrete presence/nonemptiness checks for residency and cleanup references;
- the selected meanings and numeric values of allocation count, peak live memory, bytes copied, residency, and cleanup data;
- selected `CostClass` and `CostShape` profile facts;
- concrete identification of which Systems contribution/charge corresponds to a storage lineage;
- canonical hashing, Rocq extraction, GHC, runtime, allocator, and target-profile correctness.

Until the exact extracted kernel is bound to production, the ledger Evidence Level remains **Certified**.
