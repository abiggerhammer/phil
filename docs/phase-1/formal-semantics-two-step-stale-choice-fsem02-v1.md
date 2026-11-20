# FSEM-02 — two-step cross-family stale Choice refusal (bounded v1)

**Status: non-normative and conditional.** This extends the [two-step stale Ping prefix](formal-semantics-two-step-stale-prefix-fsem02-v1.md), tracking [#1613](https://github.com/abiggerhammer/phil/issues/1613). It does not close FSEM-02.

## Exact transition and failure

Let the first request be either Ping Send/Receive or Choice Select/Offer, with separately supplied source and rendezvous admissions, exact typed continuing heads, and a successful paired resource transition `first : (S0,R0) ↦ (S1,R1)`. By `fsem02SuccessfulRequestConsumesBothExactPredecessors`, both first-step predecessor bindings are absent in `S1,R1`.

For a second **Choice Select/Offer**, even if its own admission flags are true, reusing the original **selector** predecessor or original **offer** predecessor forces that second model transition to `None`. `fsem02FamilyChoiceMissingSelectorPredecessorRejects` and `fsem02FamilyChoiceMissingOfferPredecessorRejects` prove these local negative gates for arbitrary source-label catalog and branch values.

`fsem02TwoStepStaleSelectorChoiceRefusesWithoutRollback` and `fsem02TwoStepStaleOfferChoiceRefusesWithoutRollback` lift both refusals through the two-step replay to exactly `FSEM02SecondRefused (S1,R1)`. **Refusal cannot roll back the successfully committed first transition.** The suffix does not create new endpoints or modify the committed pair.

## Actual executable source controls

Focused strict Haskell CI runs production `test/Phase1FSEM02ProtocolProgressionMain.hs` and `test/Phase1FSEM02SourceJointChoiceMain.hs` under GHC 9.6.7 `-Wall -Werror`, with `phil-core` built `-Werror`. The first checks real accepted Ping from `test/fixtures/fsem02-protocol-progression-v1/accepted.phil` and minimally rejected `stale-close.phil` with exact `GrammarV1ComponentSendCloseCloseMismatch`. The second independently parses accepted Client Go/Cancel source, `test/fixtures/fsem02-source-offer-v1/accepted.phil`, plus minimally wrong offer body `test/fixtures/fsem02-source-offer-replay-v1/wrong-body.phil`: it checks exact `GrammarV1OfferReplayCoverageError GrammarV1ComponentOfferArmBodyUnsupported` inside the joint source error, and a second Select/Offer attempt against consumed native predecessors is rejected by `ProtocolEndpointUnknown` with the exact original endpoint name. A wrong peer label and unlisted source arm have separate exact classes. CI recompiles imported Rocq 9.2 models plus `FSEM02TwoStepStaleChoicePrefix.v`; no new `Admitted`, `Axiom`, or `Parameter`.

## Trust boundary

These Haskell programs are **separately** source-checked; they are not one combined Ping→Choice or Choice→Choice source program. Native failure classes are independently tested and are not encoded by the Rocq option-valued replay. Protocol instance, role, process activation, selected root, peer, owner, disposal, assurance, typed continuation, source admission and `RendezvousValid` remain external premises. No general native Map/Set↔Rocq Context simulation, `TyEndpoint` refinement, or scheduler/termination guarantee follows. No normative syntax or TCB changes.
