# PHIL-CONC-TERM-001 implementation refinement staging

This slice stages a machine decision surface for the already Certified `PHIL-CONC-TERM-001` theorem without changing production lifecycle behavior.

## Exact staged authorities

`ConcurrencyTerminalImplementation.v` extracts four grouped Boolean gates:

1. **Process-local terminal closure** — resource/loan closure, no pending local obligations, no live endpoints, and a genuinely terminal `Closed` or `Failed` control. The proof shows these facts are sufficient to construct an exact `CertifiedProcessTerminalFact` and are also necessary for one.
2. **Fatal-process isolation** — the actor was running, becomes failed, and every distinct peer's complete semantic state remains byte-for-byte/extentionally unchanged in the normalized model.
3. **Root terminal closure** — root resources, obligations, and observables are closed; every static process has exactly one matching certified terminal fact with no extra process fact; and every static process status is terminated.
4. **Stuck/nonterminal separation** — the root is not terminal, at least one static process is still running, and there is no enabled source-semantic local or Certified internal-rendezvous step.

The direct Haskell harness has 20 controls: one accepting control for each group plus one rejection for every reflected field.

## Predecessor composition

This slice treats `PHIL-CONC-ACTIVATE-001` and `PHIL-CONC-RENDEZVOUS-001` as predecessor authorities. Their implementation-refined production harnesses are rerun unchanged. The terminal staging proof does not create a second process-population, activation, participant, protocol, Message, rendezvous, ownership-transfer, or causality semantics.

In particular, the `no enabled semantic step` fact remains source-semantic: local steps refer to static process identity and internal communication refers to `ExactInternalRendezvous`. Scheduler availability, worker availability, target thread state, and fairness are not substitutes for this fact.

## Native correspondence boundary

Production remains `src/Phil/Core/ProcessLifecycle.hs` in this staging slice. Its existing authority already checks:

- declared/fatal terminal resource and loan closure through `ensureComplete`;
- live endpoint closure;
- process-local open obligations;
- exact fatal peer status/context/obligation noninterference;
- exact all-process terminal fact construction;
- root resource/obligation/observable residue;
- enabled local/rendezvous process identity; and
- `NetworkStuck` versus `NetworkTerminal` classification.

Concrete `Map`/`Set`/`Text`, `ProcessKey`, `ProtocolContext`, obligation-set, enabled-transition, source-to-runtime extraction, and native diagnostic correspondence remain implementation boundaries. A later production-binding slice must reflect successful native facts into the exact extracted kernel, preserve native diagnostics first, and fail closed if native success disagrees with the kernel.

## Explicit nonclaims

Nothing in this refinement establishes scheduler fairness, deadlock freedom, eventual response, deadlines, implicit peer cancellation, physical cleanup, transport progress, or target/runtime scheduling correctness. Stuck/deadlocked is deliberately distinct from terminal success.

A green staging run keeps the ledger evidence level at **Certified** until the production bridge lands.
