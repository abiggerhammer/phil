# FSEM-02 / bounded source select–offer joint choice

**Non-normative. FSEM-02 is open.** This is one bounded source/production/model
slice after the source-offer branch replay merged in #1686. It changes neither
the Phase 1 EBNF nor the accepted authority/TCB. Tracking: #1613.

## Explicit judgment and trust inputs

Two independently parsed **complete** Grammar-v1 sources provide a Client
component `let chosen = select Go on endpoint; close chosen;` (or `Cancel`)
and a Server component whose offer arms each have the exactly checked
`return unit` body. Both source protocol declarations must check into the
*same* concrete binary protocol family; the caller instantiates that family
under the strict generic policy and supplies the precise instance/roles.
The test parses both programs, checks both projections and proves equality
of the closed source protocol families before instantiation. **It does not
pretend that these separate source architectures constitute a single admitted
root program.**

The production adapter `ComponentChoiceRendezvous` takes the separately
checked source component declarations, their exact declaration roots, checked
`BinaryProtocolInstance`, explicit Client/Server roles, active process keys,
a checked external `ProcessNetwork`, its current process-local protocol
contexts, an explicit peer-selected label, and an externally supplied fresh
server successor name. The Client predecessor and successor are derived only
from the checked source binder identities; the Server predecessor is derived
only from source offer coverage. The peer label **must exactly agree** with
the Client source-selected label. The offered arm must pass the existing
`ComponentOfferReplay` coverage/projection/live-head check.

The adapter then calls the **existing production**
`checkProcessCommunication ... (JointProcessRendezvous
(SelectOfferRendezvous ...))`: one joint Core transition checks both active
processes, exact instance and roles, dual live session heads, two local
steps, and atomic return of both process-local successor contexts. It also
checks that the resulting offered context agrees exactly with its independent
source-offer precheck. On failure no modified context map is returned. The
source literal `close chosen` is **not executed** by this adapter: the live
successor's `End` obligation is retained.

## Exposed rejection and replay observations

The strict Haskell conformance test checks accepted `Go` and `Cancel`
sources (the second has a separate parsed fixture), exact two-sided
predecessor removal/successor insertion, terminal outcomes, role/instance
retention, no unexpected process contexts, and deterministic first-step
replay. Negative cases: explicit mismatched peer label
`GrammarV1JointChoicePeerLabelMismatch`; a complete source fixture changing
one offered return-unit body to return-true
`GrammarV1OfferReplayCoverageError GrammarV1ComponentOfferArmBodyUnsupported`;
an unknown source label `GrammarV1OfferReplayUnlistedLabel`;
post-step stale predecessor `ProtocolEndpointUnknown`; a wrong selector
session head `RendezvousProjectionSessionMismatch`; and an incorrect
selector role `RendezvousProtocolRoleMismatch`. These are tested exact
constructors, not a fallback opaque rejection. The checked process-network
test graph is built with the production architecture-instantiation,
process-elaboration, and activation APIs, but *not from a combined source
architecture*.

The Rocq 9.2 `FSEM02JointSourceChoice.v` rule admits a paired local resource
step only when an **external** peer choice equals the selected label, the
label is in the checked offer catalog, and **both** modeled local steps
succeed. Machine-checked theorems reject mismatched/unlisted peer choices
and conditionally establish consumption of *both exact predecessor names*
and typed insertion of *both continuation successors*.
The resource proof uses the existing `SessionStep.v` lemmas through
`FSEM02ProtocolHeadProgression.v`. The production Core joint-checker's
network/duality/role facts and the distinct
`ConcurrencySemantics.v` ownership facts remain separate authority.

## What is NOT established

This is a joint **Core local-process** rendezvous with source-shape witnesses,
not a general Grammar-v1 evaluator, source offer-arm execution, scheduler,
external I/O or full network trace. It uses the endpoint-only
`checkProcessCommunication` interface, **not**
`checkProcessCommunicationState`: it does not advance the
activation-derived restricted endpoint-owner ledger, certify an architecture
root, or transfer any affine/linear payload. The peer choice and process
population are explicit inputs, not inferred facts. The Rocq theorem is
conditional and does not prove Haskell implementation refinement,
`RendezvousValid`, `satisfies C`, or general progress. FSEM-02 remains
open for ownership-ledger/source-architecture correspondence, restricted
message transfer and remaining source-to-Rocq evidence. FSEM-05/06/07 have
their own much stronger exit criteria.
