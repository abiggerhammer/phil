# Phase 1 storage allocation-failure proof v1

`PHIL-MEM-FAIL-001` certifies the bounded MEM-002/MEM-003 rule that physical storage realization may not silently widen Phil source failure semantics.

The proof composes the already-Certified `PHIL-MEM-REALIZE-001` storage-realization boundary with an explicit allocation-failure disposition. A physical allocation that cannot fail adds no source failure. A potentially failing allocation is admissible only when it is represented as exactly one of:

- an exact failure already present in the declared source failure surface;
- an explicit checked-capacity evidence reference claiming the failure is unreachable;
- an explicit assumption reference; or
- an explicit deployment requirement reference.

`StorageFailureUnaccounted` is uninhabited in the accepted relation. Mapping a physical allocation failure into an infallible source surface is impossible, and mapping to an undeclared source failure is impossible. Changing only the physical-failure disposition does not rewrite the source semantic identity inherited from `PHIL-MEM-REALIZE-001`.

This is intentionally not the general target-independent partiality theorem. `PHIL-SYS-PARTIALITY-001` remains open for arbitrary lower-level UB, traps, capacity failures, and target validity conditions. Here we certify only the storage/allocation relation already implemented and exercised by MEM-002/MEM-003.

## Correspondence boundary

The production checker is `checkStorageRealization` / `validateFailureDisposition` in `src/Phil/Systems/Storage.hs`. The unchanged `test/Phase1StorageRealizationMain.hs` corpus includes six focused MEM-002/MEM-003 cases covering unaccounted failure rejection, exact source-failure mapping, undeclared mapping rejection, checked-capacity evidence, explicit allocation assumption, and explicit deployment capacity requirement.

Concrete `Text` and `Set` representation, nonempty identity checks, diagnostic payloads/order, truth and competence of capacity evidence, applicability/truth of assumptions and deployment requirements, concrete allocator/OOM/overcommit/eviction behavior, target runtime correctness, and the Haskell/Rocq toolchains remain explicit evidence or TCB boundaries.
