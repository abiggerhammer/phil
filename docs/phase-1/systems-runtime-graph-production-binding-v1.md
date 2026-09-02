# Systems runtime graph production binding v1

`PHIL-SYS-RUNTIME-GRAPH-001` is already Certified and its representation-neutral decision surface was staged in PR #543. This closeout binds successful final Systems StageClosure admission to that exact extracted kernel without replacing the concrete SYS-015/016/018 verifiers.

## Exact kernel

The staged raw kernel SHA-256 is:

`6e61c312addbbfc15135105c5282b1610901e3c4d82fadf4596ad0644e3f18de`

The raw checked-in artifact is `generated/SystemsRuntimeGraphKernel.hs`. The production mirror is `src/SystemsRuntimeGraphKernel.hs`. They are byte-identical to fresh Rocq extraction, including the extracted file's trailing bytes.

## Production binding

`verifyStageClosureBundle` already invokes `verifyNextStageRequirementStageBundle`. That verifier recursively checks the complete Systems realization chain, including:

- SYS-015 runtime claim/site graph construction and exact reverse/cost registries;
- SYS-016 reusable primitive/profile identity with site/claim/subject/physical-cost separation;
- SYS-017 staging effects;
- SYS-018 contribution-to-charge attribution with exact class/shape compatibility; and
- the later next-stage export surface.

After that native chain succeeds, final StageClosure admission now also requires:

1. `decideRuntimeClaimGraphByFacts` to accept the verified SYS-015 surface;
2. `decideRuntimePrimitiveReuseByFacts` to accept the verified SYS-016 contribution-separation surface together with the separately Certified `PHIL-LLVM-RUNTIME-SYM-001` predecessor;
3. `decideRuntimeCostAttributionByFacts` to accept the verified SYS-018 shared-charge compatibility surface; and
4. `decideSystemsRuntimeGraphByFacts` to accept their cumulative composition.

The native verifiers remain the finite-correspondence layer and retain existing typed diagnostics and ordering. The extracted kernel owns the final normalized semantic admission. An impossible disagreement after native verification fails closed.

## Runtime-symbol predecessor boundary

The second SYS-016 kernel fact composes `PHIL-LLVM-RUNTIME-SYM-001`: linker-visible runtime symbol identity is a physical primitive/signature property, not a Systems `Map`/`Set` fact. This closeout therefore keeps that fact as an explicit Certified predecessor boundary instead of pretending that the Systems graph verifier dynamically derives LLVM symbol identity.

The closeout gate recompiles `RuntimeSymbolIdentity.v` and reruns the ordinary `phil-llvm-tests`, including the existing physical-runtime-symbol checks. LLVM lowering/runtime behavior and Haskell-to-proof-model correspondence remain explicit boundaries.

## Preserved boundary

Concrete `Text`, revision, `Map`, `Set`, list, claim/site/profile/subject/contribution/charge enumeration, canonical stage serialization, selected runtime/profile evidence and numeric cost data, exact diagnostics, LLVM lowering/runtime behavior, and Rocq/GHC correctness remain explicit correspondence/evidence/TCB boundaries.

## Closeout gate

The dedicated production-binding workflow must:

- recompile the Certified runtime and runtime-symbol predecessors, `SystemsRuntimeGraph.v`, and implementation correspondence under Rocq 9.2.0;
- fresh-extract `SystemsRuntimeGraphKernel.hs` and require SHA-256 `6e61c312addbbfc15135105c5282b1610901e3c4d82fadf4596ad0644e3f18de`;
- byte-compare both checked-in kernel copies against fresh extraction;
- strict-typecheck the production StageClosure integration;
- execute the same 12 direct kernel controls through the production mirror;
- rerun the unchanged 77-case SYS-015/016/018 corpus;
- rerun the unchanged 20-case final StageClosure corpus through the actual integration point; and
- rerun `phil-llvm-tests` for the explicit runtime-symbol predecessor boundary.

Only a fully green exact-head closeout permits promotion to `Discharged / Implementation Refined`.
