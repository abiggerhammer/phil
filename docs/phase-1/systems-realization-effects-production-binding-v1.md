# Systems realization effects production binding v1

`PHIL-SYS-REALIZE-001` is already Certified and its representation-neutral decision surface was staged in PR #537. This closeout binds successful production StageClosure acceptance to that exact extracted kernel.

## Exact kernel

The staged raw kernel SHA-256 is:

`1bf83a057b435b29783f0c2a455606a7bd3ce3649a9cbd5e28f5b09955e25852`

The raw checked-in artifact is `generated/SystemsRealizationEffectsKernel.hs`. The production mirror is `src/SystemsRealizationEffectsKernel.hs`. Coq `bool` is extracted directly to `Prelude.Bool`, so the two files are intended to be byte-identical.

## Production binding

`verifyStageClosureBundle` already invokes `verifyNextStageRequirementStageBundle`. That verifier recursively checks the complete concrete realization-effects chain, including target strengthening (SYS-014), target-inserted staging consequences (SYS-017), and explicit next-stage export (SYS-019), together with the intermediate runtime/cost layers.

After that native chain succeeds, production now requires:

1. `decideTargetStrengtheningByFacts` to accept the verified SYS-014 fact surface;
2. `decideStagingEffectByFacts` to accept the verified SYS-017 fact surface;
3. `decideNextStageExportByFacts` to accept the verified SYS-019 fact surface; and
4. `decideSystemsRealizationEffectsByFacts` to accept their composition with the already-bound Stage Closure predecessor.

The native verifiers remain the finite-correspondence layer that derives concrete facts and detailed diagnostic payloads. The extracted kernel owns the final normalized semantic admission. An impossible disagreement after native verification fails closed.

## Preserved boundary

Concrete `Text`, key/revision, `Map`, `Set`, list, lowering/runtime-site/profile/subject/cost-shape derivation, canonical revision construction, exact diagnostics, target/profile-specific ABI/layout/aliasing/machine facts, external evidence truth, backend/runtime behavior, and Rocq/GHC correctness remain explicit correspondence/evidence/TCB boundaries.

`PHIL-SYS-STAGE-CLOSURE-001` is already production-bound through `SystemsStageClosureKernel`; this closeout composes that predecessor rather than duplicating it.

## Closeout gate

The dedicated production-binding workflow must:

- fresh-extract `SystemsRealizationEffectsKernel.hs` under Rocq 9.2.0;
- require SHA-256 `1bf83a057b435b29783f0c2a455606a7bd3ce3649a9cbd5e28f5b09955e25852`;
- byte-compare both checked-in kernel copies against the fresh extraction;
- strict-typecheck the kernel and bound `StageClosure` path using only already-documented inherited warning exemptions;
- execute the same 33 direct kernel controls;
- rerun the unchanged 68-case SYS-014/017/019 corpus; and
- rerun the unchanged 20-case final StageClosure corpus through the production integration point.

Only a fully green exact-head closeout permits promotion to `Discharged / Implementation Refined`.
