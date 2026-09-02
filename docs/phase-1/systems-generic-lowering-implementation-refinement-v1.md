# PHIL-SYS-GENERIC-001 implementation refinement staging

This slice stages mechanical implementation refinement for the already-Certified generic Architecture/Core → Systems lowering obligation without changing production behavior.

## Certified executable surface

`SystemsGenericLowering.v` defines `GenericLoweringAccepted` as two things:

1. an explicit realization context is valid, requiring nonzero context revision, verifier-profile revision, realization-reference revision, and realization-semantic revision; and
2. the result is exactly `lowerGenericSystemsModel input context`.

`CertifiedGenericSystemsLowering` additionally composes the already-Certified `SystemsStageClosurePreserved` relation.

The implementation-refinement kernel therefore owns exactly six normalized admission facts, in fail-closed order:

- context revision present;
- verifier profile present;
- realization references present;
- realization semantics present;
- concrete result corresponds exactly to the normalized generic lowering model; and
- Certified StageClosure accepted.

Acceptance of those six facts is proved equivalent to `CertifiedGenericSystemsLowering` under explicit Boolean reflection hypotheses.

The existing identity-sensitivity and witness-neutrality results do not need additional runtime gates: they follow from exact correspondence to `lowerGenericSystemsModel`, whose input/result types contain no witness/program discriminator and whose witness adapter erases presentation labels before lowering.

## Preserved correspondence boundary

The extracted kernel deliberately does **not** claim ownership of concrete Haskell representation or construction. These remain native correspondence boundaries:

- `Text`, `Map`, `Set`, list, and IR representation;
- canonical `SemanticForm` serialization and digest construction;
- concrete checked Architecture/Core validation;
- detailed function/value/block/decision/runtime-site diagnostics;
- exact `SystemsProgram`, `StageContract`, lowering-ledger, `ArchitectureRealization`, and `Phase1StageBundle` construction;
- framed-upload and Steve witness adapters; and
- Rocq/GHC/toolchain correctness.

## Staging gate

The existing `Phase 1 Generic Systems Lowering Proofs` workflow is extended to:

- recompile the Certified predecessors and `PHIL-SYS-GENERIC-001` under Rocq 9.2.0;
- compile the implementation-correspondence theorem;
- fresh-extract `SystemsGenericLoweringKernel.hs` with Coq `bool` mapped directly to `Prelude.Bool`;
- strict-typecheck the extracted kernel;
- execute 7 direct controls covering acceptance and every normalized failure class;
- strict-typecheck the unchanged `lowerGenericSystems` producer and witness adapters; and
- rerun the unchanged focused generic-lowering and generic StageContract corpora.

A green staging matrix leaves `PHIL-SYS-GENERIC-001` at `Discharged / Certified`. A separate exact-kernel production-binding closeout is required before promotion to `Implementation Refined`.
