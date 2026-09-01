# Phase 1 storage cost attribution proof v1

`PHIL-MEM-COST-001` certifies the Phase 1 boundary between storage realization and the already-certified Systems runtime cost graph.

## Claim

For a checked storage realization, accepted storage cost lineage is attached to the exact Phil semantic subject and the exact physical storage-object domain selected by that realization. The lineage must contain at least one storage-attributable fact: allocation count, peak live memory, bytes copied, a residency reference, or a cleanup reference.

Different valid physical storage strategies may therefore carry different cost lineage while preserving the same source semantic identity. Physical placement and strategy remain realization facts rather than semantic identity.

When a storage cost contribution is bound into the certified Systems runtime-cost graph, its contribution-to-final-charge identity is functional. Compatible shared physical work may share one final charge, but only when the selected cost class and cost shape agree exactly. A claim does not gain a second charge merely because several claims use the same physical work.

## Certified predecessors

The proof composes:

- `PHIL-MEM-REALIZE-001` / `proof/Phil/Core/StorageRealization.v`, which proves that physical storage strategy/object choice does not establish or rewrite Phil semantic identity; and
- `PHIL-SYS-RUNTIME-GRAPH-001` / `proof/Phil/Core/SystemsRuntimeGraph.v`, which proves exact many-to-many claim/site lineage, site-owned contribution identity, functional contribution-to-charge identity, and exact class/shape compatibility for shared charges.

## Normalized proof model

`proof/Phil/Core/StorageCostAttribution.v` models:

- exact storage semantic subject;
- exact physical storage-object domain;
- selected cost class and shape;
- presence of allocation-count, peak-live-memory, and bytes-copied facts;
- residency and cleanup references; and
- an exact storage-contribution/final-charge binding into the certified runtime graph.

The proof establishes:

1. subject mismatch rejects the lineage;
2. physical-domain mismatch rejects the lineage;
3. lineage with no attributable storage fact rejects;
4. one storage contribution has exactly one final charge identity;
5. shared storage charges require exactly matching cost class and shape;
6. alternate physical storage strategies preserve source semantic identity even when their valid cost lineage differs; and
7. certified storage-cost attribution inherits exact semantic identity from `PHIL-MEM-REALIZE-001`.

## Haskell correspondence

The dedicated workflow strict-typechecks `src/Phil/Systems/Storage.hs` and `src/Phil/Systems/CostAttribution.hs`, then reruns the unchanged storage-realization and Systems cost-attribution corpora.

`checkStorageCostLineage` is the concrete MEM-006 boundary. It requires the exact checked storage semantic subject, the exact checked physical object set, valid residency/cleanup identities, and at least one attributable storage fact. The existing MEM-006 corpus checks that alternate storage strategies preserve semantic identity while retaining distinct cost lineage, and that missing attribution rejects.

The Systems cost-attribution corpus remains the concrete correspondence for the certified contribution/final-charge graph used by this proof.

## Explicit non-claims

This theorem does **not** define one universal physical-memory cost model. Numeric values, allocator metadata precision, residency semantics, pinning/device accounting, cleanup/region-teardown prices, and target-specific cost categories remain selected ADR-011 profile facts and verifier inputs.

The theorem proves lineage and nonduplication structure: cost must remain attributable to the exact realization mechanisms that incurred it, and a physical contribution cannot be counted twice under distinct final charge identities.
