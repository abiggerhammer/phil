# Phase 1 storage terminal closure implementation refinement v1

This slice stages machine implementation refinement for `PHIL-MEM-CLOSURE-001` without changing production storage or process-terminal behavior.

## Certified decision surfaces

`proof/Phil/Core/StorageTerminalClosureImplementation.v` factors the Certified terminal-closure model into separate representation-neutral Boolean gates.

Semantic storage closure mirrors `SemanticStorageClosure`:

- a live semantic storage owner always rejects;
- a released semantic storage owner accepts;
- a terminal disposition accepts exactly when that owner/disposition pair is permitted;
- a semantic owner collection accepts exactly when owner keys are unique and every owner is closed.

Physical reclamation mirrors `PhysicalStorageReclamationAccepted` independently:

- reclaimed storage accepts;
- leaked storage rejects realization/profile certification;
- retained storage accepts only when retention is permitted and the selected profile matches exactly;
- a physical-state collection accepts exactly when physical object keys are unique and every state is accepted.

The process composition gate requires the Certified stage-identity fact, the already implementation-refined MEM-001 realization fact, and semantic storage closure. The root composition gate requires the ordinary Certified root-terminal fact and all-static-process semantic storage closure.

**Physical reclamation is not an input to either semantic terminal composition gate.** This preserves the Certified theorem that a later reclamation failure may reject realization/profile certification without retroactively rewriting an already-established Phil process/root terminal fact.

## Extraction and direct controls

`StorageTerminalClosureImplementationExtraction.v` extracts the ten gates as `StorageTerminalClosureKernel.hs` using ordinary `Prelude.Bool`. `app/StorageTerminalClosureDecisionCorrespondenceMain.hs` checks acceptance and rejection controls for every semantic-owner and physical-state family, collection uniqueness/closure, and process/root predecessor composition.

The dedicated Storage Terminal Closure workflow also reruns the unchanged storage realization and process terminal corpora. Production `src/Phil/Systems/Storage.hs` and `src/Phil/Core/ProcessLifecycle.hs` remain unchanged in this staging slice.

## Retained boundary

Concrete `Text`/`Map`/`Set` representation, finite owner/object enumeration, exact permitted-disposition lookup, profile truth, owner/object key validation, native diagnostic ordering, ordinary process/root terminal certification, provider/runtime reclamation truth, and extraction/compiler/runtime correctness remain explicit native/evidence/TCB boundaries.

A later production-binding slice will reflect the semantic and physical facts independently from the existing Haskell checkers, preserve native diagnostics, require the exact extracted gates on native-success paths, and keep physical reclamation outside Phil root terminality. Until that binding lands, the ledger evidence level remains **Certified**.
