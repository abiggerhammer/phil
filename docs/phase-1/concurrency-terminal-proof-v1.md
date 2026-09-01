# Phase 1 concurrency terminal proof boundary

`PHIL-CONC-TERM-001` closes the final Phase 1 concurrency safety aggregate above the already Certified activation and rendezvous layers.

The normalized Rocq model in `proof/Phil/Core/ConcurrencyTerminal.v` proves four boundaries:

1. **Local terminal closure.** A process terminal fact contains an already-certified `LocalProcessTerminalFact`, so resource/loan closure follows from `ProcessTerminal.v`. It additionally requires no live endpoint occurrence and no `ResourceObligation.PendingObligation` in the process-local payload. `Closed` and `Failed` are the only admitted terminal controls.
2. **Failure isolation.** A fatal process transition may change the actor, but every distinct peer retains the exact same execution status, endpoint revision, cleanup revision, outcome revision, and obligation revision. This refines the peer-status isolation already present in `PHIL-CONC-SEM-001`.
3. **Root terminal closure.** The root requires a terminal fact for every exact static `ProcessOccurrence`, admits no terminal fact for a ProcessKey outside that population, requires all static process statuses terminal, and separately closes root resources, root obligations, and pending observables. Explicit `external` participant classification cannot manufacture an internal ProcessKey.
4. **Stuck is not terminal.** Enabled source-semantic steps are only local process steps or Certified exact internal rendezvous steps. A live network with no enabled local/rendezvous step and no valid root terminal fact is stuck/nonterminal. No scheduler order, fairness, eventual response, deadline, or deadlock-freedom property is inferred.

## Certified predecessors

The proof composes:

- `PHIL-CONC-ACTIVATE-001` / `ConcurrencyActivation.v` for the exact static process population and explicit participant classification;
- `PHIL-CONC-RENDEZVOUS-001` / `ConcurrencyRendezvous.v` for exact internal rendezvous as the only communication step admitted into the enabled-step model;
- `PHIL-PROC-TERM-001` / `ProcessTerminal.v` for local resource and loan closure; and
- `PHIL-RES-OBL-001` / `ResourceObligation.v` for the exact pending-obligation predicate that cannot be laundered away by reconvergence.

## Correspondence boundary

The companion Haskell job does not alter production code. It strictly typechecks `src/Phil/Core/ProcessLifecycle.hs` and reruns the unchanged CONC-007/008 lifecycle corpora plus the explicit internal/external participant corpus. These tests retain responsibility for concrete `Map`/`Set` representation, exact endpoint-map emptiness, explicit disposal behavior, process-local obligation maps, root residue representation, and source/runtime extraction.

Physical transport behavior, scheduler fairness, liveness, deadlock freedom, deadlines, eventual response, and target/runtime cleanup remain outside this safety theorem.
