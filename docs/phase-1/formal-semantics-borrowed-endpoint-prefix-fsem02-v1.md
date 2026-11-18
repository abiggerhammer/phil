# FSEM-02: exact borrowed endpoint-prefix refusal before restricted payload transfer

**Non-normative bounded production-source/Core conformance and conditional Rocq 9.2 model.** Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613), extending the distinct payload-owner loan gate (#1898), not rewriting accepted semantics or external authority.

## Source, premises and transition

The [production restricted source replay](../../src/Phil/Surface/GrammarV1/ComponentRestrictedRendezvous.hs) independently checks the complete [accepted Grammar-v1 Send/Receive source](../../test/fixtures/fsem02-restricted-source-transfer-v1/accepted.phil). Its Core transition checks sender `ProtocolSendRequest` and then receiver `ProtocolReceiveRequest`; [`Session.consumeEndpoint`](../../src/Phil/Core/Session.hs) invokes actual `consumeLinear` on each exact linear predecessor. Only after successful endpoint progression does [`checkRestrictedProcessRendezvous`](../../src/Phil/Core/ProcessRendezvous.hs) consume the sender payload and insert the receiver's exact resource. The transition is pure `Either`: any refusal returns no successor.

Independently supplied binary protocol instance and two roles, concrete message boundary contract, exact declaration-rooted process/endpoint/payload occurrence identities, original activation/owner ledger, projected heads, selected-root, disposal, and assurance authority remain **premises**. Source spelling confers none of them; loans below are explicit adversarial test inputs rather than claimed valid fresh activations.

## Exact four-fault repair ladder

The [native Haskell regression](../../test/Phase1FSEM02RestrictedSourceTransferMain.hs) uses real `startSharedLoan` to borrow **both** source endpoint predecessor owners and the distinct sender payload owner, while `insertBinding` occupies the exact receiver destination. It checks:

1. All faults: sender endpoint first refuses with exact `RendezvousProtocolError sender (ProtocolSessionError (SessionResourceError (OwnerBorrowed senderEndpoint)))`.
2. End only the sender endpoint loan: exact *receiver* endpoint `OwnerBorrowed` error, with receiver process/name.
3. End both endpoint loans: exact sender payload `RestrictedMessageSenderResourceError ... OwnerBorrowed`.
4. End all three loans: exact receiver destination `RestrictedMessageReceiverResourceError ... DuplicateBinding`.
5. Remove the independent collision too: the original accepted source/activation state is restored exactly and the previously checked authorized transfer preserves endpoint successor and payload ownership plus affine spectator.

At the fully hostile state, changing only `close done;` to `close endpoint;` in the complete sender source still yields exactly `GrammarV1ComponentSendCloseCloseMismatch`, ahead of all Core faults. No arbitrary parse failure substitutes for the expected class.

Ten [conditional Rocq lemmas](../../proof/Phil/Core/FSEM02BorrowedEndpointPrefix.v) establish the same finite admission/refusal priority, absence of partial successors and conditional transfer/spectator preservation. Boolean gate observations are **not** a representation proof of real Haskell maps/sets, full source-to-Core simulation, extracted semantics or universal preservation theorem. [SessionStep.v](../../proof/Phil/Core/SessionStep.v) and [ConcurrencySemantics.v](../../proof/Phil/Core/ConcurrencySemantics.v) retain their independent existing meaning.

[Strict focused pre-PR gate](../../.github/workflows/fsem02-borrowed-endpoint-prefix-preflight.yml) checks warning-free GHC 9.6.7 actual parsed-source Haskell execution and Rocq 9.2 with no new admissions. Broad exact-HEAD required checks, a fresh post-ready claim guard and normal protected expected-HEAD squash merge remain mandatory.

**Nonclaims:** no proof that hostile states were activation-accepted, no source-derived nominal/protocol/disposal authority, no general Haskell↔Rocq refinement, no normative rule adoption, and no FSEM-02 closure.
