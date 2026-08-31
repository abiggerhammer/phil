# Phase 1 concurrency semantics proof v1

`PHIL-CONC-SEM-001` certifies the bounded safety semantics of the static Phase 1 process network already implemented by CONC-001–011.

The Rocq model covers:

- a finite explicit process population with stable nonzero process identities and exactly one activation target per process;
- functional ownership of restricted semantic subjects, so structural wrappers cannot manufacture a second owner;
- exact synchronous internal rendezvous only for an admitted semantic Message, with restricted ownership transferred sender→receiver;
- source causality generated only by local program order, rendezvous, and explicit architecture causality—not scheduler order;
- process failure isolation: a failing process becomes failed without fabricating peer cancellation, cleanup, progression, or terminal state;
- local terminal facts only after the existing `ProcessTerminal` resource/loan closure boundary;
- root terminal closure only when every static process has an exact terminal fact, while a nonterminal state with no enabled transition is stuck/deadlocked rather than terminal;
- physical thread/task/process/event-loop/accelerator selection as an execution realization choice that does not revise source concurrency identity;
- preservation of the checked ArchitectureInstance identity supplied by certified `PHIL-SYS-GENERIC-001`.

The proof intentionally does **not** establish fairness, deadlock freedom, eventual response, deadlines, or scheduler guarantees. Those remain optional explicit assurance claims.

Concrete Haskell `Map`/`Set`/`Text` representation, `ProcessKey` serialization, source-to-architecture process extraction, Message-admission implementation, and physical execution runtime behavior remain explicit correspondence/realization boundaries. The companion workflow recompiles the certified Rocq predecessors and reruns the unchanged CONC-001–011 Haskell conformance corpus.
