# Phase 1 callable lowering correspondence v1

Status: implementation note for the CALL-016 tranche.

This slice implements the callable-specific StageContract correspondence required by the Callable and Closure Checking Contract and the Phase 1 conformance matrix.

## Governing rule

Target representation does not define callable semantics.

A callable may lower to a direct call, code pointer plus environment, defunctionalized tag, inlined body, device/kernel handle, runtime trampoline, or another representation only when StageContract validation preserves the source callable facts and explicitly accounts for target-introduced realization consequences.

CALL-016 is therefore checked in `Phil.Systems.CallableLowering`, not in the source callable checker or LLVM backend.

## Source semantic projection

`SourceCallableLoweringFacts` records the bounded Phase 1 source facts that this checker preserves:

- exact callable `InterfaceRevision`;
- exact first-class callable ownership occurrence when one exists;
- closure structural mode;
- canonical captured source occurrences;
- per-capture stable subject identity and authority relation;
- callee transition;
- caller-supplied authority requirements;
- captured/internal authority;
- public semantic may-effect bound;
- modeled caller-visible failures; and
- live scoped-loan identities.

Environment slot order, pointer address, backend symbol, and target layout are deliberately absent from this source semantic projection.

## Target projection

`TargetCallableLoweringFacts` records both:

1. the target's claimed projection of those source semantic facts; and
2. realization-specific effects, failures, assumptions, carriers, and costs introduced by the selected target representation.

The representation and its opaque inspection identity are not compared with source callable identity. Changing a code pointer or choosing a different representation therefore does not by itself change the semantic correspondence result.

Conversely, equal pointer/symbol/tag representation cannot repair a changed contract revision, callable occurrence, structural mode, capture subject, authority relation, callee transition, source effect bound, source failure surface, or loan-validity projection.

## Realization accounting

`CallableRealizationAccounting` is the callable-specific projection of an accepted StageContract realization relation. In this bounded slice every target-introduced consequence must match the corresponding accounted set/cost shape exactly:

- target-introduced semantic/runtime effects;
- target-introduced modeled failures;
- target/runtime assumptions;
- runtime enforcement/representation carriers; and
- attributable target cost.

This record is not evidence that arbitrary additional target behavior is safe merely because it is listed. The semantic truth and admissibility of target-specific effects, failures, assumptions, carriers, and costs remain governed by ADR-020 and the wider StageContract/realization checker. This slice mechanically verifies preservation and complete explicit accounting once that competent relation supplies the facts.

## CALL-016 conformance

The dedicated harness demonstrates:

- code-pointer-plus-environment lowering with explicit allocation/runtime accounting;
- target representation and pointer identity are nonsemantic;
- raw pointer coincidence cannot repair semantic mismatch;
- callable occurrence and structural mode preservation;
- captured subject/authority preservation;
- callee-transition preservation;
- caller and captured/internal authority preservation;
- semantic effect/failure preservation;
- live-loan preservation / expired-loan exclusion;
- explicit accounting for target effects, failures, assumptions, carriers, and allocation cost; and
- order-independent canonical maps/sets.

The harness runs as a named step in the existing shared Haskell `build-and-test` CI job.

## Still deferred

This slice does not implement generic architecture-to-Systems lowering, the complete generalized StageContract schema, target strengthening for arbitrary source facts, provider realization, actual closure conversion in LLVM, machine-layout verification, carrier coverage, full cost refinement, or Rocq proof.

It closes the bounded CALL-016 callable representation-preservation case and provides a concrete StageContract-side pattern for later generic lowering work.
