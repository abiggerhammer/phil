# R10/R16 follow-up: restricted live succession and activation lineage

## Audit source and scope

This slice addresses two linked P1 findings from **Phil Phase 1 follow-up audit —
2026-09-20 — 4cf858f**:

- **R10 partial:** the certified unrestricted successor used the live state, but
  the restricted-message wrapper still reconstructed initial activation state
  and therefore could not certify a second restricted message.
- **R16:** a genuine certified predecessor could be combined with a different
  independently valid activation because no exact activation lineage was stored
  in the predecessor token or checked at successor entry.

The implementation base is the R1 landing at `aa2db63e78173437addf99b377bad6c71fb1ea84`.

## Native restricted successor

`ProcessRendezvous` now exposes
`checkRestrictedProcessRendezvousSuccessor`. It shares the exact restricted
transfer implementation with initial admission, but uses the live-side
rendezvous checker rather than the immutable initial projection.

The transition still performs one atomic pure update:

1. require a send/receive rendezvous and affine/linear transfer mode;
2. require the exact current sender ownership of the payload occurrence;
3. check both current endpoint actions and the exact transfer message contract;
4. validate the current live endpoint instance/role/session relation;
5. consume the sender binding and insert exactly one receiver binding;
6. advance both endpoint occurrence owners; and
7. move the same payload occurrence in the global owner index.

Initial `checkRestrictedProcessRendezvous` remains unchanged in meaning and
continues to use initial projection validation.

## Certified activation lineage

`CertifiedRendezvousResult` now privately retains the exact
`CertifiedRendezvousActivation` authority that certified the transition. The
constructor and lineage field remain outside the public export surface.

Both successor wrappers require equality with that retained activation before
attempting any transition:

- `certifyProcessRendezvousSuccessor`; and
- new `certifyRestrictedProcessRendezvousSuccessor`.

The live-to-terminal bridge is bound too: `CertifiedTerminalRuntime` retains the
activation it was initialized from, and `certifyEnabledRendezvousStep` rejects a
rendezvous from any other activation lineage before treating it as an enabled
semantic step.

A mismatch fails with
`ConcurrencyRendezvousActivationLineageMismatch`. Equality here is the full
opaque activation witness, not merely process names, protocol instance, role
assignments, or endpoint sessions.

The accepted successor stores the same activation authority again, so lineage
is transitive across an arbitrary certified chain.

## Regression evidence

The new permanent R10/R16 corpus covers:

- a restricted linear-payload request followed by an opposite-direction
  restricted reply;
- exact payload occurrence movement and sender/receiver local names;
- both endpoint owners advancing through the second successor;
- opposite-direction causality on the reply;
- the transfer-free successor failing closed for a message that requires a
  restricted transfer;
- stale endpoint-name rejection on the restricted successor;
- donor-activation rejection on both unrestricted and restricted successor
  APIs;
- a positive control in which the donor activation runs its own genuine
  request/reply chain and preserves its additional owner;
- terminal-runtime rejection of a rendezvous certified under a donor activation; and
- the initial restricted wrapper continuing to reject already-advanced live
  contexts rather than being weakened into a successor path.

The donor activation uses the same graph, process keys, protocol, roles, and
endpoint bindings but adds a distinct linear activation occurrence. This is the
R16 composition pressure case: a cross-activation predecessor must reject even
when all ordinary endpoint facts could otherwise remain compatible.

## Assurance boundary

The existing R10 Rocq proofs are recompiled unchanged. This implementation
slice does not claim that the proof artifacts already certify activation-token
provenance or the newly added restricted live wrapper. The permanent workflow
strict-typechecks and executes the new Haskell corpus alongside the original
R10 and exact-rendezvous predecessor controls.

At authoring, exact-head CI has not completed. No local GHC, Cabal, or Rocq
execution is claimed. No generated kernel or Certified-ledger status changes.

R17/R18 release verification remain separate audit repairs.
