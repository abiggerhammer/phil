# FSEM-02: explicitly authorized peer End closure after source choice (bounded v1)

**Non-normative, not FSEM-02 completion.** Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613), building on [source-checked Client close](formal-semantics-selected-client-close-fsem02-v1.md). No normative syntax, TCB or external authority changes.

## Exact judgment and trust premise

A complete parsed Grammar-v1 Client `select L; close chosen` and independently parsed complete Server `offer endpoint { ... => { return unit; } }` must both pass the checked source path. A caller independently supplies a **closed binary protocol instance**, exact Client/Server roles and activated network, activation-derived owner occurrences and communication state, selected peer label, fresh Server successor identity, and *two explicit terminal outcome inputs*. The server End disposition is an **external Core action authorization**: `return unit` does **not** mean `close serverNext`, authorize disposal, or discharge root obligations.

```text
source-checked select/offer + activation-derived Σ₀ + checked instance/roles
  -- stateful joint select/offer --> Σ₁
source Client 'close chosen', exact Client End outcome
  -- native Client close --> Σ₂
externally authorized Server End outcome and explicit Server successor
  -- native Server close --> Σ₃ | exact rejection (no successor)
```

`grammarV1CloseStatefulSourceChoiceExplicitPeer` replays both earlier transitions independently from the **original** state (not cached post-state) and then invokes actual `closeProcessEndpointState` for the server. Success retires the exact two distinct endpoint owner occurrences, leaves the affine spectator and unrelated ownership untouched, and yields the same complete state as independent native Core replay. In a failing branch, the `Either` carries the specific source/client or server-Core error and returns no progressed state.

## Executable evidence

The parsed accepted source witnesses `test/fixtures/fsem02-source-choice-v1/accepted.phil`, `test/fixtures/fsem02-source-joint-choice-v1/client-cancel.phil`, and `test/fixtures/fsem02-source-offer-v1/accepted.phil` exercise Go/Done and Cancel/Cancel against activated Core state. The minimally rejected `test/fixtures/fsem02-source-offer-replay-v1/wrong-body.phil` changes a literal `return unit` to `return true` and rejects **exactly** `GrammarV1ComponentOfferArmBodyUnsupported` before either close; separate checks reject wrong peer terminal outcome as `CloseOutcomeMismatch Done Cancel` and stale duplicate peer closure as `EndpointClosureOccurrenceUnknown`. `test/Phase1FSEM02SourceJointChoiceMain.hs` checks deterministic replay, exact full-state equality, and spectator frame.

`proof/Phil/Core/FSEM02ExplicitPeerClose.v` gives a finite functional owner-ledger model with conditional exact-live-owner matching, missing-owner rejection, two distinct retirements, arbitrary spectator frame, and duplicate-close rejection. The conditions are explicit: source selection validity, actual activation ledger fidelity, separately supplied Server terminal authority, and Haskell-to-model representation correspondence **remain premises**. These Rocq 9.2 theorems are **not** universal Haskell-to-Rocq refinement, server source-arm execution, architecture selected-root completeness, process-local disposal authority, or assurance discharge. No `Admitted`, `Axiom` or `Parameter` is introduced.

Focused warning-free Haskell/source and Rocq checks are required on branch before a draft PR. Protected exact-head CI and fresh post-ready FSEM claim guard remain mandatory.
