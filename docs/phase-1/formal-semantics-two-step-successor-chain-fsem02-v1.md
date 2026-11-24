# FSEM-02: two-step successor chaining and independent admission gates (non-normative)

**Status:** bounded, conditional review evidence. This is not a normative language rule, general source-program operational semantics, a complete protocol authority proof, or Haskell/Rocq refinement.

## Exact rule and transition

Let `R1` and `R2` be requests in the existing tagged `FSEM02PairedReplayRequest` model; either may designate Ping (send/receive) or Choice (select/offer). `R1` executes from two starting `ResourceContext` values to a pair of committed contexts `M`. `R2` executes from `M` to `F`. All four source and rendezvous admission booleans and the corresponding well-formed continuation-head premises are independently supplied; they do **not** follow from syntax.

For an admitted two-step success, if the second request names **exactly** each peer's first-step successor as its predecessor, the first step's predecessor is absent from each peer's committed linear bindings, and the first step's successor is absent from each peer's final linear bindings. This is a *consumption* theorem for two generations of endpoints. It does not forbid the second step from allocating a new key with the same spelling as an earlier, already-consumed key; such a freshness restriction would require a separate premise.

If step one is admitted but step two lacks either source acceptance or rendezvous admission, step two refuses and the two committed step-one contexts are retained *exactly*. If step one lacks source acceptance, the initial pair is retained. Rejection is `None` in the conditional model, not a proof that native code produces a particular diagnostic class.

## Machine-checked obligations

`proof/Phil/Core/FSEM02TwoStepSuccessorChain.v` imports the existing `FSEM02PairedTwoStepOutcomes.v` and `FSEM02TwoStepStalePrefix.v`. Its four theorems are:

- `fsem02TwoStepChainedSuccessConsumesBothGenerations`
- `fsem02TwoStepSecondUnadmittedSourcePreservesCommittedPrefix`
- `fsem02TwoStepSecondUnadmittedRendezvousPreservesCommittedPrefix`
- `fsem02TwoStepFirstUnadmittedSourcePreservesInitial`

The proof reuses exact per-family predecessor-consumption theorems and the previously established success/admission characterization. No `Admitted`, `Axiom` or `Parameter` is introduced.

The dedicated CI runs strict native GHC 9.6.7 `-Wall -Werror` checks over `test/Phase1FSEM02ProtocolProgressionMain.hs` and `test/Phase1FSEM02SourceJointChoiceMain.hs`, which separately exercise actual complete-source accepted Ping and Go/Cancel Choice witnesses and exact rejected cases (including `GrammarV1ComponentSendCloseCloseMismatch`, `GrammarV1OfferReplayCoverageError GrammarV1ComponentOfferArmBodyUnsupported`, and `ProtocolEndpointUnknown`). It also compiles the Rocq dependency closure under Rocq 9.2.0.

## Independent premises and scope limits

Original protocol instance, role/peer membership, activation, external rendezvous, ownership, disposal, selected root and assurance authority are **external**. `fsem02ReqSourceAccepted` is an input representing independently checked source acceptance, not a proof of it. Tests run separate complete-source witnesses, not a combined two-step Grammar-v1 program; they do not certify that the native checker implements this exact two-step model for every resource map. No fairness, scheduler guarantees, general `Map`/`Set` correspondence, general compiler correctness, normative graduation or FSEM-02 completion follows.

**Next missing seam:** produce an actual native two-step source/Core resource-state trace and an independently checked model observation or simulation relation, rather than equating these conditional model theorems with implementation behavior.
