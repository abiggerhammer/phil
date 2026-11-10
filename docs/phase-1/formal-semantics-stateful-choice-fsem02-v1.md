# FSEM-02 / source-checked stateful choice and endpoint owner ledger

**Non-normative. FSEM-02 remains open.** This is a bounded extension of
[source joint select/offer replay](formal-semantics-source-joint-choice-fsem02-v1.md)
(#1688), not a new source or proof authority. It changes neither the Phase 1
EBNF nor the trusted computing base. Tracking issue: #1613.

## Judgment, checked inputs and transition

Inputs are two independently parsed complete Grammar-v1 component shapes,
their exact caller-supplied declaration roots, one separately source-checked
closed binary protocol family and its exact instance/roles, an externally
supplied matching peer choice, active Core process keys/network, a fresh offer
successor name, and a **ProcessCommunicationState** whose resource contexts and
restricted-owner index originate from `activateProcessState` and
`communicationStateFromActivation`. The test actually constructs and checks
that production activation boundary. A valid prior stateful transition may
also supply the input state; no arbitrary caller-synthesized owner map is
certified by the adapter.

Write the explicit non-normative step as

`(S_client, S_offer, network, protocolContexts, ownerIndex, chosen, peer)
  --select/offer--> (protocolContexts', ownerIndex')`

only when the production source checker accepts the Client's parsed
`select chosen; close successor` and the Server's complete source
`offer { Go => return unit; Cancel => return unit }` catalog, the peer
label equals `chosen`, the source offer replay accepts its selected arm,
and the *production* `checkProcessCommunicationState` jointly advances
the exact projected dual session heads and their two uniquely identified
owner occurrences. The result must have exactly the same protocol-context
map as the independently checked source/Core joint replay. In one atomic
pure `Either` transition, both old local linear endpoints disappear, both
fresh successors have the selected terminal `End` obligation, and both
activation-derived occurrence keys retain their identity but point to the
new owner-local endpoint names. Unrelated affine/linear occurrences remain
unchanged. The source's `close` is **not executed**; closure is a separate
source/production obligation.

A rejection returns only an exact error class and **no successor state**:
the existing source parsing/projection/replay errors are wrapped as
`GrammarV1StatefulChoiceSourceError`; invalid ledger ownership is wrapped
as `GrammarV1StatefulChoiceOwnerError` (including
`RendezvousEndpointOccurrenceUnknown` and
`RendezvousEndpointOccurrenceAmbiguous`); unexpected difference between
the source Core and stateful projections is
`GrammarV1StatefulChoiceContextDivergence`. No fallback opaque admission
or guessed role/owner/name occurs.

## Executable witnesses, trace/replay, proof assumptions

`test/Phase1FSEM02SourceJointChoiceMain.hs` now constructs actual production
activation contracts for both checked session endpoints, plus an independent
affine spectator. The existing complete parsed source `Go` and `Cancel`
fixtures are accepted and checked against exact owner-key/name transitions,
process-context parity, end-outcome preservation and deterministic replay.
Minimally rejected `wrong-body.phil` has exactly
`GrammarV1ComponentOfferArmBodyUnsupported`, before any owner transition.
Adversarial tests additionally reject missing, stolen and ambiguous owner
occurrences; reused stale source predecessors; and wrong session heads.
The exact owner-key set and nonparticipant spectator are checked unchanged.

The Rocq 9.2 `FSEM02StatefulSourceChoice.v` finite-key functional ledger
model proves: aliasing the two selected occurrence keys rejects; an absent
client occurrence rejects; successful model owner renaming preserves both
exact occurrence keys and **every** nonparticipant key; and combined success
implies both the previously proved conditional local-resource joint step
and the owner-model step. It builds on `FSEM02JointSourceChoice.v`, which
in turn uses `SessionStep.v`, and keeps the separate process facts of
`ConcurrencySemantics.v` outside the theorem. No new
`Admitted`/`Axiom`/`Parameter` statements are added.

**Trust premises and nonclaims:** The source components are not one
admitted combined architecture/root. The owner-index proof uses an extensional
function and an explicit valid-ledger premise; it is not an extracted
Haskell `Map` refinement, and duplicate process/name aliases are checked
in Haskell rather than proved globally in this functional model. Neither
general send/receive payload transfer, source offer-arm execution,
source-to-Core elaboration preservation, network scheduling, unrestricted
process progress, nor normative semantic graduation is established. FSEM-02,
FSEM-05/06/07, and architecture/assurance obligations remain open.


For the distinct, still-open source-choice terminal endpoint obligation, see [the bounded selected-client close bridge](formal-semantics-selected-client-close-fsem02-v1.md). This consumes only the source-selected client's End endpoint after stateful joint choice, **not** the offerer's unit-return arm or the architecture root.
