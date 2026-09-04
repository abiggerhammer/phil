# Phase 1 concurrency execution-realization production binding v1

This slice production-binds `PHIL-CONC-LOWER-001` to the exact machine decision surface staged by #704.

## Exact kernel

The production tree contains byte-identical copies of the freshly extracted #704 kernel at:

- `generated/ConcurrencyExecutionRealizationKernel.hs`
- `src/ConcurrencyExecutionRealizationKernel.hs`

The exact kernel is 2,248 bytes, has two trailing newline bytes, and has SHA-256:

`0fa44b0fa81334793b5df469422aeb6f44d387f877f8ca16dfce3f82af32540e`

The production workflow re-extracts the kernel from Rocq 9.2.0 on every relevant pull request, checks its byte count and SHA-256, and byte-compares both checked-in copies before any Haskell production correspondence job may run.

## Production composition

`Phil.Systems.ProcessRealizationCertification` is the production bridge.

The bridge deliberately does not accept a caller-supplied `ProcessNetwork`, restricted-owner index, or raw `ProcessRuntimeState` as source authority. Instead it consumes:

- the opaque production-refined `CertifiedRendezvousActivation` predecessor from #693, from which it derives the exact activated process network and restricted-owner index;
- the opaque production-refined `CertifiedTerminalRuntime` predecessor from #700, whose runtime state has crossed the exact terminal/failure/stuck kernel boundary;
- the source `ProcessPartialOrder`, process-scoped semantic facts, `StageContract`, and `LoweringLedger` supplied by their existing competent source/Systems layers;
- the candidate `ProcessExecutionRealization`.

The native `verifyProcessExecutionRealization` checker runs first. It receives the certified activation network, the certified activation restricted-owner index, and the certified terminal runtime. Any native diagnostic therefore remains the first production failure authority.

Only native success reaches the exact #704 kernel.

## Reflected theorem groups

The production bridge independently reflects all seventeen `ProcessExecutionRealizationValid` fields into the same four groups staged by #704.

### Process / lowering-decision facts

The five reflected facts are:

1. exact source-process mapping coverage, with at least one physical execution for every source process and no invented source process;
2. no empty physical execution identity;
3. exact referenced-execution / lowering-decision coverage;
4. exact lowering-decision identity with explicit cost classification;
5. every execution-decision assumption declared in the `StageContract`.

Many-to-many realization remains legal. One source process may use several target execution mechanisms, and several source processes may share one target execution mechanism. This never creates source identity equality.

### Event / causality facts

The four reflected facts are:

1. exact source-event mapping coverage;
2. no empty physical event identity;
3. injective source-event to physical-event correspondence;
4. preservation of every source causal edge as a path in the physical causal graph.

Physical-path reachability is recomputed independently in the production bridge from the concrete target causal-edge set.

### Semantic-preservation facts

The five reflected facts are:

1. the realization restricted-owner map equals the owner map derived from the production-refined activation state;
2. process-scoped effect/authority/failure facts are exact;
3. every source process fact remains declared in the `StageContract`;
4. realization terminal facts equal the terminal facts extracted from the opaque #700 certified runtime;
5. realization assumptions equal the `StageContract` assumption set.

This is the key production strengthening over the original CONC-009 API: a caller-built `ProcessRuntimeState` cannot be substituted for the terminal predecessor, and a caller-built restricted-owner source map cannot be substituted for the certified activation predecessor.

### Explicit trace facts

The three reflected facts require the concrete `StageContract.trace_relation` to contain every process-realization entry, every source-event correspondence, and every physical-causality entry using the existing canonical renderers.

The outer exact-kernel gate accepts only if all four grouped gates accept.

## Failure behavior

The production bridge is native-first and fail-closed:

- native identity, causality, ownership, terminal, decision/cost, assumption, and trace diagnostics are preserved unchanged;
- a native-success / reflected-fact disagreement fails closed at the corresponding exact kernel group;
- any disagreement among the four group results fails closed at the outer kernel gate;
- no scheduler-order Boolean is supplied to the kernel.

The production control harness covers a fully certified many-to-many realization; native diagnostic precedence for source-identity, causality, restricted-owner, terminal, cost, and trace drift; one injected disagreement in each of the four exact groups; and an injected outer-gate disagreement.

The workflow additionally reruns the #687 activation, #693 rendezvous, and #700 terminal production harnesses, the #704 twenty-six direct extracted-kernel controls, and the unchanged eight-case CONC-009 corpus.

## Remaining boundaries and non-claims

This production binding certifies preservation *of the supplied source execution-realization semantics*. It does not turn target execution metadata into source semantics and does not prove target machinery correct.

The following remain explicit boundaries owned elsewhere or by target evidence:

- construction and completeness of the supplied source `ProcessPartialOrder` beyond the already established concurrency semantics;
- construction/authority of process-scoped source semantic facts and the Systems `StageContract` / `LoweringLedger` inputs;
- concrete `Text` / `Map` / `Set` / list representation and serialization;
- `ProcessKey`, `ProcessEventKey`, physical execution/event key construction;
- extraction, GHC compilation, and runtime correctness;
- scheduler fairness, deadlock freedom, eventual progress, timing/deadlines;
- buffering, IPC, locking, atomic, OS worker/thread/process, accelerator/device correctness;
- quantitative performance or cost accuracy beyond explicit classification/accounting;
- runtime assurance-carrier transfer, which remains the separate DEP-002 / `PHIL-ASSURE-CARRIER-001` authority.

Target worker/task/PID/thread/event-loop/device identity remains representation metadata, never source `ProcessKey` identity.
