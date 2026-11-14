# FSEM-02 — crosswired process-local terminal End contexts (non-normative)

**Witness boundary.** The independently checked accepted Go/Done and
Cancel/Cancel Select/Offer fixtures are
`test/fixtures/fsem02-source-choice-v1/accepted.phil`,
`test/fixtures/fsem02-source-joint-choice-v1/client-cancel.phil` and
`test/fixtures/fsem02-source-offer-v1/accepted.phil`. The separate complete
minimally rejected source `fsem02-source-offer-replay-v1/wrong-body.phil`
continues to produce the exact
`GrammarV1ComponentOfferArmBodyUnsupported` class without an opaque fallback.

## Actual native End checker and state transition

`test/Phase1FSEM02SourceJointChoiceMain.hs` constructs the actual
source-derived checked joint Select/Offer successor, including distinct
Client/Server End names, the two exact endpoint-owner occurrences, process-local
checked protocol contexts and the borrowed affine spectator. It then swaps
**only** Client and Server entries of the native protocol-context map.
This is an *adversarial Core test input*, never an admitted source-level
context transfer.

Both processes remain active, and both possess a **unique exact owner**.
Nevertheless, attempted native End Close must return the specific
`EndpointClosureProtocolError process (ProtocolEndpointUnknown endpoint)`
for either process. The error cannot retire an endpoint. Context *presence*
and an owner occurrence are insufficient to authorize a process-local End.

The test externally restores only the original separately checked Client
context and closes Client while Server remains miswired; then performs the
symmetric Server-first experiment. In both paths the still-miswired peer
rejects precisely, its owner persists, and the affine spectator is framed.
After restoring the second original context, the two End Close orders reach
exactly the same full native state as the independently checked close diamond.
No accepted source step is asserted for these explicit repairs.

## Conditional Rocq and nonclaims

`proof/Phil/Core/FSEM02ChoiceCrosswiredContextGate.v` composes the existing
finite owner/cardinality/nominal model with an independent, **externally
supplied** process-local context observation. With one owner, a wrong context
cannot produce a retired successor even if nominal authorization is asserted.
Zero and multiple owners continue to refuse at their earlier gates. Correct
context alone still cannot grant nominal authority; a separately granted
and successful retirement is required. The propositions quantify over arbitrary
finite supplied owner ledgers and are conditional after any separately
established peer-state transition.

Rocq collapses native protocol error subtypes into a refusal result; Haskell
tests alone check the exact `ProtocolEndpointUnknown` diagnostic.
Native Map enumeration/lookup representation, context provenance and actual
source-to-Rocq refinement are not proved. External protocol instance, role,
activation, terminal outcome, selected-root authority, scheduler and assurance
premises are unchanged. No normative syntax, TCB or other lane changes.
**FSEM-02 remains OPEN and non-normative.**
