# Phase 1 concurrency execution-realization proof v1

`PHIL-CONC-LOWER-001` certifies the normalized semantic boundary implemented by CONC-009 in `Phil.Systems.ProcessRealization`.

The source concurrency model is already established by the Certified concurrency and Systems predecessors. This theorem addresses only the next question: what must remain true when those source processes are mapped onto physical workers, tasks, threads, processes, event loops, accelerator stages, or other target execution mechanisms?

## Certified claim

A valid execution realization preserves the exact source semantic identities and relations while allowing an otherwise many-to-many physical mapping:

- every exact source `ProcessKey` has at least one physical execution mechanism, and no non-source process can appear merely because a worker has a convenient name;
- source process identity and physical execution identity are different semantic sorts;
- every source process event has exactly one nonempty physical event correspondence;
- distinct source events cannot collapse to one physical event identity;
- every source causal edge remains represented by a physical causal path;
- the complete restricted-owner index is unchanged;
- process-scoped effect, authority, and failure facts are unchanged and remain declared in the StageContract;
- process terminal facts remain exact, so completion of one shared worker cannot stand in for terminal closure of every source process using it;
- every referenced physical execution mechanism has an exact lowering-decision identity and an explicit cost classification;
- every lowering assumption used by physical execution is declared in the StageContract, and the realized assumption set is exactly the StageContract assumption set;
- process mapping, event mapping, and physical-causality entries remain explicit trace relations.

The theorem deliberately permits one source process to be split across several physical mechanisms and several source processes to share one physical mechanism. Neither direction creates a semantic identity equality.

## Composition boundary

The proof is harvested above these already Certified predecessors:

- `PHIL-CONC-SEM-001` — source concurrency safety semantics;
- `PHIL-CONC-TERM-001` — local and root terminal closure/failure isolation;
- `PHIL-SYS-STAGE-CLOSURE-001` — exact source disposition and target justification closure;
- `PHIL-SYS-CONTROL-001` — resource/control/protocol preservation;
- `PHIL-SYS-REALIZE-001` — explicit target strengthening, effects, costs, and next-stage requirements.

The dedicated workflow recompiles those exact proof sources before `ConcurrencyExecutionRealization.v` and records their identities in the proof artifact.

## Explicit non-claims

This proof does **not** establish scheduler fairness, deadlock freedom, eventual progress, timing/deadline behavior, buffering/IPC correctness, locking or atomic correctness, OS thread/process correctness, accelerator/device execution correctness, or quantitative performance.

Concrete `Text`/`Map`/`Set` representation, `ProcessKey`/event construction, physical graph path search, lowering-ledger lookup, StageContract trace serialization, and target-specific cost values remain correspondence or target-profile boundaries. Runtime-enforced carrier preservation across process split/domain transfer remains separately owned by the DEP-002 / `PHIL-ASSURE-CARRIER-001` profile-gated obligation and is not silently inferred here.
