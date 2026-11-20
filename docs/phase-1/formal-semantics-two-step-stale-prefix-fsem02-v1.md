# FSEM-02 — two-step cross-family stale-predecessor refusal (bounded v1)

**Non-normative and conditional; FSEM-02 remains open.** Tracks [issue #1613](https://github.com/abiggerhammer/phil/issues/1613) and extends the [paired two-step outcome replay](formal-semantics-paired-two-step-outcomes-fsem02-v1.md) without claiming full source-to-Rocq refinement.

## Narrow transition rule and proof

For a source/rendezvous-admitted first model step, either Ping Send/Receive or Choice Select/Offer, with separately established continuing-head premises, both linear predecessor bindings are consumed. The successor is not a replacement for the old name. The new theorem `fsem02SuccessfulRequestConsumesBothExactPredecessors` lifts the two existing per-family consumption lemmas to the tagged request interface.

If a second **Ping** request on the committed contexts names either first-step predecessor again (sender or receiver), it must return `None` even if its own source/rendezvous admission flags are supplied. The two `fsem02TwoStepStale*PingRefusesWithoutRollback` theorems establish the exact `FSEM02SecondRefused(committed)` result, retaining the first step's complete, actual model successor pair. Neither proof assumes a rollback or invents a fresh endpoint. This is a bounded stale-reuse property, not a theorem about arbitrary sequential Phil source programs.

## Executable source controls

Dedicated focused CI runs the **actual** production Haskell `test/Phase1FSEM02ProtocolProgressionMain.hs` and `test/Phase1FSEM02SourceJointChoiceMain.hs` under GHC 9.6.7 `-Wall -Werror`. The Ping suite reads the accepted complete `test/fixtures/fsem02-protocol-progression-v1/accepted.phil` and minimally rejected `stale-close.phil` (exact `GrammarV1ComponentSendCloseCloseMismatch`); it checks consumed exact predecessors and stale Core errors. The Choice suite reads accepted Go/Cancel complete source witnesses and minimally rejected wrong-body/unknown-arm witnesses with precise native error classes. These are **separate native programs**; their checks do not magically establish a combined Ping/Choice source witness or the Rocq/native mapping. The Rocq 9.2 job compiles the imported semantic bridges plus this module and rejects any new `Admitted`, `Axiom` or `Parameter`.

## Premises and remaining gaps

The result depends on independently supplied source admission, rendezvous validity, typed continuing-head/choice-arm premises and exact chosen predecessor names. Nominal instance, activation, selected root, process owner, disposal and assurance authority are **not** inferred from surface syntax or Boolean flags. The model's `None` does not identify production diagnostic classes. Native `Map`/`Set` state to Rocq resource-context simulation, `TyEndpoint` correspondence, an actual mixed-family source program, scheduler/progress and broader Phase 1 formal semantics remain open. No normative grammar or trust-boundary change is made.
