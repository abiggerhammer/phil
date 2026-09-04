# Phase 1 concurrency execution-realization implementation refinement v1

This document stages machine implementation refinement for `PHIL-CONC-LOWER-001` above the existing Certified theorem in `proof/Phil/Core/ConcurrencyExecutionRealization.v` and the existing CONC-009 implementation in `Phil.Systems.ProcessRealization`.

Production behavior is unchanged by this staging slice.

## Exact machine decision surface

`ConcurrencyExecutionRealizationImplementation.v` retains all seventeen fields of `ProcessExecutionRealizationValid`, grouped by competent authority rather than flattened into an opaque aggregate.

### Process / lowering-decision facts — 5

1. exact source-process ↔ nonempty physical-realization coverage;
2. no empty physical execution identity;
3. exact referenced-execution ↔ lowering-decision coverage;
4. every referenced execution decision has an explicit cost classification;
5. every execution assumption is declared in the StageContract.

### Event / causality facts — 4

1. exact source-event ↔ physical-event coverage;
2. no empty physical event identity;
3. physical event identity is injective over source events;
4. every source causal edge survives as a physical causal path.

### Semantic preservation facts — 5

1. restricted owners are exact;
2. process-scoped effect/authority/failure facts are exact;
3. source semantic facts remain declared in the StageContract;
4. source process terminal facts are exact;
5. realized assumptions equal the StageContract assumption set exactly.

### Explicit trace facts — 3

1. process→physical-execution entries are trace-bound;
2. source-event→physical-event entries are trace-bound;
3. physical-causality entries are trace-bound.

An outer gate composes those four groups. The extraction therefore produces five `Prelude.Bool` decision functions. The direct harness exercises 26 controls: all-true acceptance for each group and the outer aggregate, plus one-at-a-time rejection of every field and every outer group.

## What remains deliberately legal

The theorem and extracted decision surface do **not** require a one-to-one process/worker relation. One source process may use several physical execution mechanisms, and several source processes may share one worker/task/thread/event loop/accelerator stage. Physical execution identity remains representation metadata and never substitutes for `ProcessKey`.

Likewise, scheduler order is not an input fact. Source causality is preserved only through explicit source-event correspondence and physical causal paths.

## Current native authority

`src/Phil/Systems/ProcessRealization.hs` remains unchanged. `verifyProcessExecutionRealization` already checks the concrete `Map`/`Set`/`Text` representation corresponding to the seventeen theorem fields:

- exact process-domain mapping and nonempty execution IDs;
- exact lowering-decision coverage, cost, and assumptions;
- exact event-domain mapping, nonempty physical IDs, injectivity, and causal reachability;
- exact restricted owners, semantic facts, terminal facts, and StageContract assumptions;
- explicit process, event, and physical-causality trace entries.

The unchanged eight-case CONC-009 corpus remains the behavioral correspondence oracle.

## Refined predecessor chain

The staging workflow recompiles the Certified concurrency and Systems proof predecessors and reruns the production-refined `PHIL-CONC-TERM-001` terminal harness from #700. This matters specifically for terminal preservation: completion of one physical worker must never stand in for certified terminal closure of every source process mapped to it.

`PHIL-CONC-ACTIVATE-001` and `PHIL-CONC-RENDEZVOUS-001` remain transitively represented by that terminal production predecessor, while `PHIL-CONC-SEM-001`, Systems StageContract closure, Systems control preservation, and Systems realization/effect preservation retain their existing Certified authorities.

## Production-binding requirement

This slice remains **Certified**, not Implementation Refined.

A later production-binding slice must not trust the public `ProcessRuntimeState` constructor accepted by the current native CONC-009 function. It must either:

- consume the opaque `CertifiedTerminalRuntime` produced by the #700 production-refined terminal boundary; or
- independently reflect the equivalent terminal/runtime facts before invoking the exact execution-realization kernel.

The production binding must also fresh-extract this exact kernel, byte-compare checked-in copies, preserve native `ProcessRealizationError` diagnostic precedence, and fail closed on any native-success/kernel-reject disagreement.

## Retained boundaries and non-claims

Concrete `Text`/`Map`/`Set` representation, `ProcessKey` and `ProcessEventKey` construction, physical path search, lowering-ledger lookup, StageContract trace serialization, source extraction into the realization checker, extraction/GHC/runtime correctness, and target-profile-specific cost values remain correspondence or realization boundaries.

No scheduler fairness, deadlock freedom, eventual progress, timing/deadline behavior, buffering/IPC correctness, locking/atomic correctness, OS worker correctness, accelerator/device correctness, or quantitative performance claim is added. DEP-002 / `PHIL-ASSURE-CARRIER-001` continues to own profile-gated RuntimeBound carrier transfer rather than being inferred from execution realization.
