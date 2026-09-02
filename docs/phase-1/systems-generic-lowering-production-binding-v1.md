# PHIL-SYS-GENERIC-001 production binding

This closeout binds the already-Certified generic Systems lowering theorem to the exact executable kernel staged by PR #551.

## Exact staged kernel

- staging exact green head: `3b3adc8e6753f7511336ca78e4d6583962ec0d3b`
- staging merge: `c172ce0caba1e27e62f571c253f8e0bb379394f4`
- exact `SystemsGenericLoweringKernel.hs` SHA-256: `af042ab8cfd60ea84140485b9097dd380eff7c7e7122835be3f8174d7e89b8f8`
- checked-in raw copy: `generated/SystemsGenericLoweringKernel.hs`
- production mirror: `src/SystemsGenericLoweringKernel.hs`

Both checked-in copies must remain byte-identical to a fresh Rocq 9.2.0 extraction.

## Production ownership

The concrete `lowerGenericSystems` producer remains responsible for checked-Core validation, exact Systems/StageContract/lowering-ledger construction, canonical `SemanticForm` and digest construction, realization-context interpretation, and detailed `GenericLoweringError` diagnostics. The framed-upload and Steve adapters remain witness-neutral callers of that one producer.

The extracted kernel owns only the normalized Certified admission relation from `SystemsGenericLowering.v`: nonzero/present context revision, verifier profile, realization references, realization semantics, exact normalized producer/result correspondence, and the already-Certified final StageClosure relation.

The kernel is therefore admitted at the end of `verifyStageClosureBundle`, after native detailed verification and the already-bound `SystemsStageClosureKernel` have accepted. The first five Boolean facts are the finite-correspondence boundary checked by the unchanged generic producer/witness corpora; the sixth is supplied only after the actual final StageClosure decision has accepted. Any impossible disagreement fails closed through the existing certified-kernel invariant path.

## Closeout gate

`Phase 1 Generic Systems Lowering Production Binding`:

- recompiles the Certified predecessors, `PHIL-SYS-GENERIC-001`, and implementation-correspondence theorem under Rocq 9.2.0;
- fresh-extracts `SystemsGenericLoweringKernel.hs` and requires SHA-256 `af042ab8cfd60ea84140485b9097dd380eff7c7e7122835be3f8174d7e89b8f8`;
- byte-compares fresh extraction with both checked-in kernel copies;
- strict-typechecks the production kernel, unchanged generic producer/witness adapters, and final StageClosure integration;
- executes the 7 direct controls through the production mirror;
- reruns the unchanged focused generic-lowering corpus and generic StageContract corpus; and
- reruns the unchanged final StageClosure corpus through the actual integration point.

Concrete Haskell `Text`/revision/`Map`/`Set`/list/IR representation, canonical serialization and hashing, detailed lowering construction and diagnostics, witness adaptation, and Rocq/GHC correctness remain explicit correspondence/evidence/TCB boundaries.

A fully green exact-head closeout permits `PHIL-SYS-GENERIC-001` to move from `Discharged / Certified` to `Discharged / Implementation Refined`.
