# FSEM-02: terminal End close order diamond (bounded v1)

**Status: non-normative, not FSEM-02 completion.** Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613); extends [explicit peer closure](formal-semantics-explicit-peer-close-fsem02-v1.md). No changed syntax, TCB, normative authority or process-root discharge.

## Scoped operational judgment

A complete parsed Grammar-v1 Client `select L; close chosen` and Server `offer ... { return unit; }` undergo exact source coverage and the existing production stateful select/offer rendezvous. The caller supplies the activated network, **original** ProcessCommunicationState, closed binary protocol instance and roles, selected peer label, fresh Server endpoint identity, and **independently authorized Client/Server terminal outcomes**. The literal Server `return unit` is *not* an endpoint-disposal authorization.

For `Σ₁` the exact checked state after one rendezvous, and separately authorized terminal closures `C` and `S`:

```text
checked source + Σ₀ -- select/offer --> Σ₁
  Σ₁ -- Client End C --> ΣC -- Server End S --> ΣCS
  Σ₁ -- Server End S --> ΣS -- Client End C --> ΣSC
  accept iff ΣCS == ΣSC (complete native state)
  otherwise reject exact source/Core error or divergence, no result state
```

`grammarV1CheckSourceChoiceCloseDiamond` independently rechecks the original source and activation-derived predecessor in both paths; both directions execute actual `closeProcessEndpointState`. It checks **full native equality** (all protocol contexts, resource maps/sets, and restricted owner ledger), not merely a two-key projection. It does not infer a scheduler, select root, dispose endpoint on behalf of source Server, or make an opaque fallback.

## Evidence and limits

`test/Phase1FSEM02SourceJointChoiceMain.hs` runs the complete accepted Go and Cancel Grammar-v1 sources from `test/fixtures/fsem02-source-choice-v1/accepted.phil`, `test/fixtures/fsem02-source-joint-choice-v1/client-cancel.phil`, and `test/fixtures/fsem02-source-offer-v1/accepted.phil`, with exact full-state replay, retired owners, and affine spectator frame. The minimally rejected complete `test/fixtures/fsem02-source-offer-replay-v1/wrong-body.phil` changes one offer arm from `return unit` to `return true` and must fail specifically as `GrammarV1ComponentOfferArmBodyUnsupported`. Wrong Client/Server terminal outcomes retain the original `CloseOutcomeMismatch` and associated process identity; stale source predecessor and duplicate Server closure retain their precise endpoint errors.

`proof/Phil/Core/FSEM02TerminalCloseDiamond.v` uses the existing `FSEM02SelectedClientClose.v` and `FSEM02ExplicitPeerClose.v` models. Under distinct occurrence keys and both successful individually modeled orders, it proves **pointwise equality of the final finite owner ledgers**. It does **not** prove the actual Haskell Core close functions commute for arbitrary states, successful closure existence, universal Haskell-to-Rocq refinement, source Server offer-arm evaluation, architecture/root admission, explicit disposition authority, effects, assurance, fairness, liveness or normative Phase 1 semantics. These are separate premises/obligations.

Run focused warning-free Haskell source/native and Rocq 9.2 (no Admitted/Axiom/Parameter) checks on the pushed work branch before opening a draft PR. Full exact-head CI and fresh post-ready FSEM Slice Claim Guard remain mandatory.
