# FSEM-02: both one-sided End-close prefix ledgers (bounded v1)

**Status: non-normative, FSEM-02 remains open.** Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613). This extends the [source-relative Select/Offer successor trace](formal-semantics-choice-source-successor-trace-fsem02-v1.md) with independently verified **intermediate one-sided** terminal owner states rather than only ready/final states. No normative syntax or TCB change.

## Partial judgment and explicit trusted inputs

Given two separately parsed and source-checked complete Grammar-v1 Client Select/Close and Server Offer/Return programs, an admitted binary protocol instance, externally supplied roles, processes, root and activation, the **original** live Core communication state, selected peer label, distinct occurrence identities, external Server continuation identity, and **two independently authorized terminal outcomes**:

```text
Σ₀ -- actual checked joint Select/Offer --> Σ₁
Σ₁ -- authorized Client End --> Σc -- authorized Server End --> Σcs
Σ₁ -- authorized Server End --> Σs -- authorized Client End --> Σsc

Owners(Σ₁): original owner map with exactly two successor endpoint names
Owners(Σc): Owners(Σ₁) minus Client occurrence; Server remains live
Owners(Σs): Owners(Σ₁) minus Server occurrence; Client remains live
Owners(Σcs) = Owners(Σsc) = Owners(Σ₁) minus both occurrences
All unrelated affine owner occurrences are preserved at every prefix.
```

Production `grammarV1CheckChoiceSourceSuccessorTrace` in [ComponentChoiceStatefulRendezvous.hs](../../src/Phil/Surface/GrammarV1/ComponentChoiceStatefulRendezvous.hs) first rechecks source and executes both independent Core closure orders. This slice also extracts the two **actual native one-sided** owner maps, checks their complete equality to the exact expected original-to-successor-minus-one projections, and records them in `choiceSourceTraceAfterClientOwners` and `choiceSourceTraceAfterPeerOwners`. Unexpected differences produce the precise `ChoiceSourceTraceClientFirstPrefixOwnerMismatch` or `ChoiceSourceTracePeerFirstPrefixOwnerMismatch`, never opaque success or a stateful fallback. Successful terminal equality still compares **all** Core protocol/ownership state.

## Accepted/rejected source and native witnesses

`test/Phase1FSEM02SourceJointChoiceMain.hs` independently parses the existing Go/Done and Cancel/Cancel complete-source fixtures and checks original, ready, each one-sided End prefix and terminal whole owner-map projections. It checks that the opposite endpoint stays live and an affine spectator retains exactly its original owner in both prefixes, while two repeated native Core calls reclose the locally retired endpoint with exact `EndpointClosureOccurrenceUnknown` (correct process and endpoint). This is repeatable deterministic finite replay, not a universal simulation theorem.

The complete-source `test/fixtures/fsem02-source-offer-replay-v1/wrong-body.phil` is minimally rejected by the source checker as `GrammarV1ComponentOfferArmBodyUnsupported`, not generic parse failure. A wrong externally supplied Client End outcome produces the exact native `CloseOutcomeMismatch Done Cancel` under its nested source/diamond error constructors, **without exposing any successful prefix**. Earlier stale-source, wrong-head, aliased and fabricated occurrence rejections remain in the same strict suite.

## Conditional Rocq theorem and trust boundary

[ FSEM02ChoiceClosePrefixLedgers.v](../../proof/Phil/Core/FSEM02ChoiceClosePrefixLedgers.v) composes the existing `FSEM02StatefulSourceChoice`, `FSEM02SelectedClientClose`, `FSEM02ExplicitPeerClose` and `FSEM02TerminalCloseDiamond` lemmas (ultimately relying on the bounded `SessionStep.v` and `ConcurrencySemantics.v` models). Under successful source/model choice **and all four separately authorized modeled End steps**, Rocq 9.2 proves exact one-sided retirements, preservation of the opposite endpoint, spectator equality from the **original** owner ledger, and equality of the terminal owner functions. Separate conditional theorems reject a second identical retirement from either one-sided state. No `Axiom`, `Admitted` or `Parameter` is introduced.

**Nonclaims:** No source Server `return unit` disposal authority, root validity/selected-root discharge, assurance, guessed nominal authority, scheduler fairness, all-Haskell `Map`↔Rocq implementation refinement, whole-source operational semantics, or normative graduation. FSEM-02 stays open. The strict branch preflight is `.github/workflows/fsem02-choice-close-prefix-ledgers-preflight.yml`; broad PR CI, fresh post-ready exact-claim guard, protected merge and claim release are separate gates.
