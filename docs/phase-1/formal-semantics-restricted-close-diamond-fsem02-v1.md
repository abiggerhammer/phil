# FSEM-02: restricted send/receive terminal End close order diamond (bounded v1)

**Status: non-normative, incomplete FSEM-02.** Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613). Extends [checked restricted source owner transfer](formal-semantics-restricted-source-transfer-fsem02-v1.md), [source close](formal-semantics-source-terminal-close-fsem02-v1.md), and [source terminal obligations](formal-semantics-source-terminal-obligations-fsem02-v1.md). The corresponding select/offer diamond is separately tracked in [the choice-order slice](formal-semantics-terminal-close-diamond-fsem02-v1.md).

## Narrow source/configuration judgment

For an actual parsed Grammar-v1 send/close component and receive/close component, with exact declaration roots, the externally supplied accepted binary protocol instance, nominal roles/processes, active network, payload activation occurrence, original live communication state `Σ₀`, and two **independently authorized** terminal End outcomes, the production adapter `grammarV1CheckRestrictedSourceCloseDiamond` requires:

```text
source + Σ₀ -- checked typed restricted send/receive --> Σ₁
Σ₁ -- sender End close --> Σs -- receiver End close --> Σsr
Σ₁ -- receiver End close --> Σr -- sender End close --> Σrs
accept iff Σsr == Σrs, as full Core ProcessCommunicationState
otherwise exact source/Core error or divergence, no success state
```

The first transition invokes the **real** `grammarV1CheckRestrictedSourceRendezvous` from the original `Σ₀`, not merely a cached or rewritten rendezvous carrier. That source checker checks the declared send/receive source binder, payload type/mode, receiver written type and name, and actual native restricted rendezvous. The forward pair rechecks the source closes and invokes the real `closeProcessEndpointState` twice; the reverse pair independently invokes that same Core close twice in opposite order. Comparison is over **all** native protocol/resource contexts and activation owner identities; the endpoint-close operations do **not** dispose the transferred restricted payload, nor the affine spectator. Every error returns `Left` without a successful successor.

The source's `close` expressions constrain **which successor names** are to be closed, but do not create protocol instance, activated network, admitted restricted message boundary contract, nominal role/process identity, eligible End outcome, root selection, explicit resource disposal, or assurance authority. Those are named external inputs/premises, not inferred from spelling or source shape. The experiment does not select a scheduler or prove all interleavings commute.

## Executable evidence and exact negative classes

`test/Phase1FSEM02RestrictedSourceTransferMain.hs` uses the complete accepted `test/fixtures/fsem02-restricted-source-transfer-v1/accepted.phil` and minimally rejected `rejected-stale-close.phil`. The latter changes the source close's successor identity and must fail exactly with `RestrictedSourceCloseDiamondRendezvousError (RestrictedSourceSendError (GrammarV1ComponentSendCloseCloseMismatch ...))`, not an unrelated parsing or implementation failure.

The full-state replay compares independently checked source rendezvous, independently run sender-first and receiver-first native closures, exact retirement of both endpoint occurrences, preservation of the transferred linear `Bytes[8]` under the receiver's resolved binder, and preservation of an unrelated sender-owned affine spectator. Negative checks reject the consumed predecessor as `RestrictedMessageOwnerMismatch`, an incorrect Send session head through `RendezvousProtocolError`, a mismatched peer End outcome as `CloseOutcomeMismatch`, and a duplicated receiver-first close as `EndpointClosureOccurrenceUnknown`.

## Rocq rule and trust boundary

`proof/Phil/Core/FSEM02RestrictedCloseDiamond.v` composes `FSEM02SelectedClientClose.v`, `FSEM02ExplicitPeerClose.v`, `FSEM02TerminalCloseDiamond.v`, and the restricted transfer owner-ledger model. Under distinct endpoint occurrences, an independently established receiver-owned transferred payload, and explicit **success of all four individual owner-retirement steps**, `fsem02RestrictedCloseOrderDiamondPayloadAndFrame` proves exact retirement of both endpoints, transferred-payload preservation, spectator frame, and pointwise equality of the two final owner ledgers. `fsem02RestrictedCloseOrderRejectsStaleReceiver` proves the modeled missing-owner rejection. Native Core `SessionStep.v` and `ConcurrencySemantics.v` remain the separate session/protocol abstraction boundaries.

This is a conditional finite Rocq owner-ledger theorem plus tested production Haskell/Syntax correspondence; it is **not** universal Haskell-to-Rocq refinement or a proof that arbitrary source programs satisfy the listed premises. It does not prove global protocol progress, fairness, scheduler independence, terminal disposal, root validity, effects, assurance or normative Phase 1 authority. No TCB or syntax changes are made.

Run the branch-only warning-free Haskell / Rocq 9.2 focused preflight before opening a draft PR. Complete broad exact-head checks, fresh post-ready FSEM Slice Claim Guard and protected mergeability remain separate mandatory gates.
