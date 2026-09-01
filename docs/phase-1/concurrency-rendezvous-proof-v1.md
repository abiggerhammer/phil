# Phase 1 concurrency rendezvous proof boundary

`PHIL-CONC-RENDEZVOUS-001` certifies the synchronous internal rendezvous layer above the already Certified concurrency activation and protocol obligations.

The normalized Rocq model in `proof/Phil/Core/ConcurrencyRendezvous.v` composes:

- `PHIL-CONC-SEM-001` for the bounded process-network safety envelope;
- `PHIL-CONC-ACTIVATE-001` for explicit internal participant ownership by activated static `ProcessOccurrence`s;
- `PHIL-PROT-ID-001` and `PHIL-PROT-PROJ-001` for exact binary protocol instance, opposite role, and dual-session identity;
- `PHIL-PROT-STEP-001` for exact predecessor removal, fresh successor installation, and stale-predecessor rejection;
- `PHIL-PROT-MSG-001` for exact Message admissibility before restricted ownership transfer; and
- `PHIL-RES-JOIN-001` as the existing resource-conservation boundary used by the executable process machinery.

A certified rendezvous requires both endpoint sides to be admitted by their exact current local protocol state. The current sessions are exact duals, and the supplied successor sessions are exact duals. Each successful side removes its exact predecessor occurrence and installs one fresh successor while preserving protocol instance and role identity.

For a restricted payload, Message admissibility is an independent premise and cannot be manufactured by ownership. Successful transfer moves the exact restricted subject from the sender `ProcessKey` to the receiver `ProcessKey`. Both processes must already be explicitly classified internal and belong to the activated static population.

Source causality gains the rendezvous edge because of the semantic synchronization itself. Scheduler or declaration order remains nonsemantic and cannot substitute for that edge.

This proof does **not** claim physical transport correctness, fairness, deadlock freedom, eventual response, deadlines, or any scheduler guarantee. Concrete `Map`/`Set`/`Text` representation, `ProcessKey` and role-occurrence encoding, source-to-architecture extraction, physical boundary/transport behavior, and the exact Haskell correspondence remain explicit implementation boundaries checked by CI.
