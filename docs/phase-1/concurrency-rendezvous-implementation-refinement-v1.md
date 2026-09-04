# Phase 1 concurrency rendezvous implementation refinement v1

`PHIL-CONC-RENDEZVOUS-001` is already Certified by `proof/Phil/Core/ConcurrencyRendezvous.v`. This staging slice adds a machine-facing decision correspondence without changing production rendezvous behavior.

## Exact decision surface

`proof/Phil/Core/ConcurrencyRendezvousImplementation.v` preserves all twenty-one fields of `ExactInternalRendezvous`, grouped by the authority that must supply each fact:

1. **Endpoint / binary-protocol facts** — binary instance well-formedness, sender and receiver predecessor→successor progression, exact instance and role on both sides, exact dual current sessions, and exact dual successor sessions.
2. **Participant facts** — the participant-classification predecessor is valid, both exact role occurrences name the exact internal sender/receiver processes, and those role occurrences agree with the endpoint roles.
3. **Message / coarse-rendezvous facts** — the independently competent ADR-016 Message contract accepts, the coarse synchronous rendezvous/ownership relation is valid, and its instance, roles, and process identities agree exactly with the endpoint/participant witnesses.

`decideExactInternalRendezvousByFacts` accepts exactly when all three groups accept. The Rocq correspondence theorem proves this grouped decision equivalent to `ExactInternalRendezvous`.

The existing theorem `accepted_rendezvous_causality_is_semantic_not_scheduler_order` remains derived from the accepted exact rendezvous: source causality comes from the rendezvous relation itself, while scheduler-only order remains nonsemantic. The extracted ABI therefore does not take scheduler order as an input fact.

## Extracted kernel

`ConcurrencyRendezvousImplementationExtraction.v` extracts four Prelude.Bool-compatible gates to `ConcurrencyRendezvousKernel.hs`:

- `decideRendezvousEndpointFactsByFacts`
- `decideRendezvousParticipantFactsByFacts`
- `decideRendezvousMessageCoarseFactsByFacts`
- `decideExactInternalRendezvousByFacts`

`app/ConcurrencyRendezvousDecisionCorrespondenceMain.hs` executes 28 direct controls: each group accepts when all of its facts are true, each one of the twenty-one theorem fields independently rejects when false, the outer aggregate accepts all three valid groups, and each invalid group independently rejects.

## Existing authorities remain authoritative

This staging slice does not duplicate the native or already-refined competent layers:

- `PHIL-CONC-ACTIVATE-001` remains the authority for exact active/static internal-participant classification and is now production-bound through `ConcurrencyActivationCertification`.
- protocol identity/projection/progression remains owned by the existing protocol checkers and proofs.
- ADR-016 Message admissibility remains an independent prerequisite; structural mode or successful transport does not manufacture Message competence.
- `ProcessRendezvous` remains the native synchronous communication / restricted transfer checker.
- `ProcessCausality` remains the concrete finite partial-order checker; declaration, scheduler, Haskell evaluation, and worker order remain nonsemantic.

## Retained correspondence boundaries

Concrete `Map`/`Set`/`Text` traversal, `ProcessKey` and role-occurrence encoding, source→architecture extraction, exact reflection from native endpoint/protocol/ownership state into the grouped booleans, and extraction/GHC/runtime correctness remain correspondence boundaries. Physical transport timing, fairness, deadlock freedom, deadlines, and eventual response are outside this safety theorem.

## Production status

Production `ProcessRendezvous.hs` and `ProcessCausality.hs` are unchanged by this staging slice. The logic-ledger evidence level therefore remains **Certified** until an exact-kernel production-binding slice lands with native diagnostic precedence and fail-closed disagreement.
