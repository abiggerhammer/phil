# Phase 1 storage realization implementation refinement v1

This slice stages machine implementation refinement for `PHIL-MEM-REALIZE-001` without changing production storage realization semantics.

## Certified decision surface

`proof/Phil/Core/StorageRealizationImplementation.v` factors `StorageRealizationValid` into seven representation-neutral Boolean facts:

1. the semantic-subject binding uses an admitted checked subject basis;
2. one exact semantic subject is present;
3. the source semantic revision is nonzero;
4. the source outcome revision is nonzero;
5. the selected physical storage strategy is nonzero;
6. the selected realization semantics revision is nonzero; and
7. every selected physical storage object identifier is nonzero.

The proof establishes that the conjunction of those seven facts is equivalent to the Certified `StorageRealizationValid` relation. `StorageRealizationImplementationExtraction.v` extracts that decision as `StorageRealizationKernel.hs`.

The exact physical strategy, physical object set, architecture realization revision, and allocator/provider facts remain nonsemantic coordinates. Semantic identity remains the exact subject plus exact source semantic/outcome revisions, as proved by the Certified MEM-001 model.

## Direct controls

`app/StorageRealizationDecisionCorrespondenceMain.hs` checks the freshly extracted kernel directly. The all-true vector must accept, and independently falsifying each of the seven facts must reject.

The dedicated storage-realization proof workflow also reruns the unchanged 18-case `Phase1StorageRealizationMain.hs` corpus, including the four focused MEM-001 cases for strategy nonsemanticity, physical-coincidence rejection, and distinct semantic subjects over shared physical storage.

## Boundary retained for production binding

This slice does not modify `src/Phil/Systems/Storage.hs` and does not yet make `checkStorageRealization` kernel-gated. Concrete `Text`/`Set` representation, finite enumeration, nonempty-key validation, physical-object validation, allocation-failure handling, native diagnostics, allocator/provider truth, target memory facts, and extraction/compiler/runtime correctness remain explicit native/evidence/TCB boundaries.

A later exact-kernel production-binding slice will reflect these seven proof-model facts from the concrete `StorageRealizationRelation`, preserve native diagnostic precedence, and require the extracted classifier on every native-success MEM-001 path. Until then the ledger evidence level remains **Certified**.
