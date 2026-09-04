# Phase 1 storage allocation failure implementation refinement v1

This slice stages machine implementation refinement for `PHIL-MEM-FAIL-001` / MEM-002--003 without changing production `Phil.Systems.Storage` behavior.

## Certified decision surface

`StorageAllocationFailureImplementation.v` keeps the already implementation-refined `PHIL-MEM-REALIZE-001` predecessor as one Boolean fact and factors the remaining Certified `StorageFailureDispositionValid` case split into small executable gates:

- outer failure-realization validity = base storage realization valid and failure disposition valid;
- `PhysicalAllocationCannotFail` accepts;
- `StorageFailureMapsToSource` requires a nonzero failure identity and exact membership in the admitted source failure surface;
- `StorageFailureProvedUnreachable` requires a nonzero checked-capacity evidence identity;
- `StorageFailureAssumption` requires a nonzero explicit assumption identity;
- `StorageFailureDeploymentRequirement` requires a nonzero explicit deployment-requirement identity; and
- `StorageFailureUnaccounted` rejects unconditionally.

The correspondence proof establishes each gate against the existing Certified `StorageAllocationFailure.v` model. It deliberately does not duplicate the seven MEM-001 facts inside this kernel. The eventual production binding will obtain predecessor acceptance from the already-bound MEM-001 certification surface.

`StorageAllocationFailureImplementationExtraction.v` extracts these decisions as `StorageAllocationFailureKernel.hs` using ordinary `Prelude.Bool`.

## Direct controls

`app/StorageAllocationFailureDecisionCorrespondenceMain.hs` checks the freshly extracted kernel directly. It covers valid outer composition, invalid predecessor and disposition rejection, each accepted disposition class, each identity/declaration rejection, and unconditional rejection of unaccounted allocation failure.

The dedicated workflow also reruns the implementation-refined MEM-001 production controls and the unchanged 18-case `Phase1StorageRealizationMain.hs` corpus, including all six MEM-002--003 cases.

## Boundaries retained for production binding

This staging slice does not modify `src/Phil/Systems/Storage.hs`. Concrete `Text`/`Set` representation, finite source-failure membership, nonempty-key validation, capacity-evidence truth, assumption/deployment applicability, allocator/OOM/abort/overcommit/retry/eviction behavior, native diagnostic reconstruction, target-runtime behavior, extraction/toolchain correctness, and GHC/runtime correctness remain explicit native/evidence/TCB boundaries.

A later production-binding slice will preserve native diagnostic precedence, require the already-refined MEM-001 predecessor kernel, independently reflect the selected allocation-failure disposition, and require the exact extracted MEM-FAIL kernel on every native-success path. Until then `PHIL-MEM-FAIL-001` remains **Certified**.
