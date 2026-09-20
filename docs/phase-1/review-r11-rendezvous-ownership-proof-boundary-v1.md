# PHIL-P1-REVIEW-R11 proof boundary

This slice certifies Astra Review R11: a transfer-free rendezvous still depends on the concrete endpoint-owner ledger and may not manufacture endpoint ownership from protocol context alone.

The existing `PHIL-CONC-RENDEZVOUS-001` theorem remains the protocol/session authority. R11 closes a different implementation boundary in `Phil.Core.ProcessRendezvous`: before an endpoint owner can advance, the owner index must contain **exactly one** occurrence currently owned by the expected `ProcessKey` under the expected predecessor endpoint name.

The normalized proof captures the same three-way resolution as `advanceEndpointOwner`:

- no matching owner entry → reject;
- exactly one matching owner entry → advance that same occurrence identity to the requested successor name;
- more than one matching owner entry → reject as ambiguous.

An accepted update preserves the occurrence key and exact process identity. Only the local endpoint name changes from predecessor to successor. Protocol acceptance by itself is therefore insufficient to authorize an owner-ledger update.

This matters for transfer-free rendezvous as much as restricted payload rendezvous. Endpoint occurrences are restricted activation resources even when no message payload moves, so both sides' endpoint owners must advance atomically with the protocol transition.

The concrete correspondence is:

- `communicationStateFromActivation` seeds the owner ledger from the activation partition;
- `checkProcessCommunicationState` checks the protocol transition and then calls `advanceRendezvousEndpointOwners`;
- `advanceEndpointOwner` searches the owner index for entries matching the exact process/predecessor pair;
- zero matches produce `RendezvousEndpointOccurrenceUnknown`;
- one match updates that exact occurrence key to `(process, successor)`; and
- multiple matches produce `RendezvousEndpointOccurrenceAmbiguous`.

The permanent R11 regression deletes a genuine endpoint occurrence from an otherwise-valid transfer-free rendezvous state and requires rejection with the exact process/predecessor identity. The dedicated gate also replays restricted-message ownership controls, exact rendezvous controls, and the production binding harness.

Concrete `Map` traversal and iteration order, `ActivationOccurrenceKey`/`ProcessKey`/`Name` representation, activation-to-owner-index construction, diagnostic ordering, GHC/runtime correctness, and Rocq/toolchain correctness remain explicit implementation boundaries.
