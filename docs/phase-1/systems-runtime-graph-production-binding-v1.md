# Systems runtime graph production binding v1

`PHIL-SYS-RUNTIME-GRAPH-001` is already Certified and its representation-neutral decision surface was staged in PR #543. This closeout binds successful final Systems StageClosure admission to that exact extracted kernel without replacing the concrete SYS-015/016/018 verifiers.

The later target-portability audit generalized one proof predecessor without changing the extracted decision surface: SYS-016 now composes target-neutral `PHIL-TARGET-RUNTIME-PRIM-001`, while `PHIL-LLVM-RUNTIME-SYM-001` remains an LLVM-specific refinement of that relation.

## Exact kernel

The staged raw kernel SHA-256 is:

`6e61c312addbbfc15135105c5282b1610901e3c4d82fadf4596ad0644e3f18de`

The raw checked-in artifact is `generated/SystemsRuntimeGraphKernel.hs`. The production mirror is `src/SystemsRuntimeGraphKernel.hs`. They are byte-identical to fresh Rocq extraction, including the extracted file's trailing bytes.

The target-neutral predecessor lives entirely in proof-facing `Prop` structure and does not change the four extracted Boolean classifiers, so this kernel identity is expected to remain stable; the production-binding workflow verifies that claim by fresh extraction and byte comparison rather than assuming it.

## Production binding

`verifyStageClosureBundle` already invokes `verifyNextStageRequirementStageBundle`. That verifier recursively checks the complete Systems realization chain, including:

- SYS-015 runtime claim/site graph construction and exact reverse/cost registries;
- SYS-016 reusable primitive/profile identity with site/claim/subject/physical-cost separation;
- SYS-017 staging effects;
- SYS-018 contribution-to-charge attribution with exact class/shape compatibility; and
- the later next-stage export surface.

After that native chain succeeds, final StageClosure admission also requires:

1. `decideRuntimeClaimGraphByFacts` to accept the verified SYS-015 surface;
2. `decideRuntimePrimitiveReuseByFacts` to accept the verified SYS-016 contribution-separation surface together with target-neutral `PHIL-TARGET-RUNTIME-PRIM-001` entry identity;
3. `decideRuntimeCostAttributionByFacts` to accept the verified SYS-018 shared-charge compatibility surface; and
4. `decideSystemsRuntimeGraphByFacts` to accept their cumulative composition.

The native verifiers remain the finite-correspondence layer and retain existing typed diagnostics and ordering. The extracted kernel owns the final normalized semantic admission. An impossible disagreement after native verification fails closed.

## Target-entry refinement boundary

The second SYS-016 kernel fact is no longer defined in terms of linker-visible symbols. `PHIL-TARGET-RUNTIME-PRIM-001` requires an exact target-visible entry identity derived from the selected physical primitive and target profile/signature, independent of assurance revision/evidence/use identity or claim-set cardinality.

Concrete targets refine that entry relation separately. LLVM still uses `PHIL-LLVM-RUNTIME-SYM-001`, where the target entry is a linker-visible runtime symbol and the theorem additionally preserves one physical LLVM call for the singleton runtime-site case. A WebAssembly profile may instead use an import/function/table identity; an EVM profile may use an opcode/precompile/runtime entry; an SBF profile may use a syscall or CPI target.

The closeout gate still recompiles `RuntimeSymbolIdentity.v` and reruns `phil-llvm-tests` as an LLVM target-refinement regression, but LLVM is no longer a semantic predecessor of the generic Systems runtime graph.

## Preserved boundary

Concrete `Text`, revision, `Map`, `Set`, list, claim/site/profile/subject/contribution/charge enumeration, canonical stage serialization, selected runtime/profile evidence and numeric cost data, exact diagnostics, target-specific entry/calling-convention behavior, backend/runtime behavior, and Rocq/GHC correctness remain explicit correspondence/evidence/TCB boundaries.

## Closeout gate

The dedicated production-binding workflow must:

- recompile the Certified runtime predecessor, target-neutral runtime-primitive identity, `SystemsRuntimeGraph.v`, and implementation correspondence under Rocq 9.2.0;
- also recompile `RuntimeSymbolIdentity.v` as the retained LLVM target refinement;
- fresh-extract `SystemsRuntimeGraphKernel.hs` and require SHA-256 `6e61c312addbbfc15135105c5282b1610901e3c4d82fadf4596ad0644e3f18de`;
- byte-compare both checked-in kernel copies against fresh extraction;
- strict-typecheck the production StageClosure integration;
- execute the same 12 direct kernel controls through the production mirror;
- rerun the unchanged 77-case SYS-015/016/018 corpus;
- rerun the unchanged 20-case final StageClosure corpus through the actual integration point; and
- rerun `phil-llvm-tests` as the LLVM target-refinement regression.

Only a fully green exact-head closeout permits the generalized proof surface to retain `Discharged / Implementation Refined` status.
