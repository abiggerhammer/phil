# FSEM-02: source Select/Offer typed heads and two End prefix states (bounded v1)

**Status: non-normative draft; not FSEM-02 completion.** Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613). Builds on the [source-relative choice successor/owner trace](formal-semantics-choice-close-prefix-ledgers-fsem02-v1.md), without modifying admitted grammar, source authority or the TCB.

## Partial judgment and independent evidence

For **two separately parsed, production-checked complete** Client Select/Close and Server Offer/Return sources; an explicitly admitted binary protocol instance; externally supplied role/process and distinct endpoint occurrence identities; the **original** activation-derived communication state; selected source/peer label, separately supplied Server continuation name, and **two external End outcomes**:

```text
Σ0 -- source checked Select/Offer; atomic Core progression --> Σready
  Client: Select{label:End(outcome)} endpoint_old
       -> terminal endpoint_client_next
  Server: Offer{label:End(outcome)} endpoint_old
       -> terminal endpoint_server_next

Σready -- authorized Client End --> Σclient-first
Σready -- authorized Server End --> Σserver-first
Both authorized orders terminate at equal complete native states.
```

New production `grammarV1CheckChoiceTypedPrefix` in [ComponentChoiceStatefulRendezvous.hs](../../src/Phil/Surface/GrammarV1/ComponentChoiceStatefulRendezvous.hs) **reexecutes from the supplied original**, using the previously source-checked full diamond/owner trace, then **independently** calls `Phil.Core.Protocol.checkProtocolAction` for exact old Client `ProtocolSelectRequest`, old Server `ProtocolOfferRequest`, and both distinct `ProtocolCloseRequest` End outcomes. It demands that each locally replayed **complete ProtocolContext** (endpoint bindings and actual linear, affine and loan resource maps) equals the context observed in the real atomic Core rendezvous, both one-sided close states, and complete terminal state. Context mismatch is a distinct typed error per state/process; no cached successor is silently accepted.

This comparison establishes finite *executable conformance* between two production Core execution routes and exact checked-source binders. It does **not** independently elaborate a combined source architecture, derive Server close authority from `return unit`, prove universally valid Haskell-to-Rocq refinement, or identify `SessionStep.endpointType` with native `TyEndpoint`.

## Witnesses and failures

`test/Phase1FSEM02SourceJointChoiceMain.hs` parses the complete Go/Done and Cancel/Cancel Client/Server source fixtures in `test/fixtures/fsem02-source-*` and checks deterministic equality of the independently replayed four local transition records against the actual native states, including original predecessor identity, exact `TyEndpoint (End outcome)` terminal successor, absence of any close successor, surviving peer in each first-close state, and unchanged affine spectator ownership.

The **minimally rejected** complete source `test/fixtures/fsem02-source-offer-replay-v1/wrong-body.phil` is refused with the precise nested `GrammarV1ComponentOfferArmBodyUnsupported` class. Source replay against an already consumed offer predecessor must produce `ProtocolEndpointUnknown`. An externally wrong peer End outcome produces `CloseOutcomeMismatch Done Cancel`. Wrong live Select head produces `RendezvousProjectionSessionMismatch`. All rejections are nested in `ChoiceTypedPrefixSourceError` and expose no successful typed prefix. Tests check constructor identities, not generic failure.

## Conditional Rocq proof scope

[ FSEM02ChoiceTypedHeadPrefix.v](../../proof/Phil/Core/FSEM02ChoiceTypedHeadPrefix.v) composes `FSEM02JointSourceChoice` and `FSEM02ChoiceClosePrefixLedgers` with local `SessionStep` and `FSEM02ProtocolHeadProgression`. Under an explicit `offeredContinuation chosen branches = Some (End outcome)`, admitted joint source/model success, distinct owners and **four separately authorized modeled close steps**, it proves consumption of both exact old endpoint resources, both abstract End-continuation successor resource tokens, one-sided owner retirement with the opposite endpoint still live, unchanged original spectators, and final owner-function equality. A separate theorem rejects a missing offered branch even if the source label appears to be listed. No `Admitted`, `Axiom` or `Parameter` is added.

**Trust premises and nonclaims:** production source parser/binder/projection; externally admitted protocol instance, roles, message boundary and activated process network; externally supplied nonaliasing occurrences, Server successor, selected label and two End/disposal authorizations; architecture/root/assurance competence; historical proof token modeling and toolchain. Not a full Phase 1 source evaluator, compiler-correctness result, scheduler/fairness/deadlock theorem, universal Haskell-to-Rocq simulation, or normative semantics. FSEM-02 remains open.

**CI gates:** `.github/workflows/fsem02-choice-typed-head-prefix-preflight.yml` is intended as a strict GHC 9.6.7 / Rocq 9.2 on-branch preflight; independent broad exact-head required checks, fresh post-ready claim guard, protected expected-head merge and claim release remain separate.
