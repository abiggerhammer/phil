# FSEM-02 — two-sided borrowed spectator frame on paired Choice (bounded v1)

**Status:** non-normative FSEM-02 work, tracked by [#1613](https://github.com/abiggerhammer/phil/issues/1613). No change to accepted Phase 1 grammar, TCB or semantic authority.

## Scope and concrete transition

Starting from independently checked Go and Cancel Client Select and Server Offer source, with an **externally admitted** protocol instance, process network, peer label and two pre-existing Core resource contexts, the production Haskell regression `pairedLocalChoiceJointEquality` executes both local `checkProtocolAction` transitions and an independent synchronous `grammarV1CheckJointSourceChoice`. It compares the **entire** two-process native resource context Map, including each endpoint's consumed predecessor, typed selected successor, nominal instance and role, and affine spectators.

The added case equips the Server context with a separately supplied affine spectator carrying an **active shared loan**, in addition to the previously borrowed Client spectator. This is not authority inferred from source syntax. Both Go and Cancel must preserve the two separate affine binding maps and loan sets, with no new or lost process context. Stale Client/Server endpoints and a mismatched peer label still reject with their exact production classes; replay from the original context remains successful. The complete-source minimally rejected offer body is still checked as exact `GrammarV1ComponentOfferArmBodyUnsupported`, not any parser failure.

**Accepted executable sources:** `test/fixtures/fsem02-source-choice-v1/accepted.phil` (Go), `test/fixtures/fsem02-source-joint-choice-v1/client-cancel.phil` (Cancel), and the independently parsed `test/fixtures/fsem02-source-offer-v1/accepted.phil`. **Minimally rejected:** `test/fixtures/fsem02-source-offer-replay-v1/wrong-body.phil`; also `test/fixtures/fsem02-source-choice-v1/unknown-label.phil` for exact unlisted-arm refusal. Executed by `test/Phase1FSEM02SourceJointChoiceMain.hs` under strict GHC 9.6.7.

## Rocq proof boundary

`proof/Phil/Core/FSEM02PairedChoiceJointBridge.v` adds `fsem02PairedChoiceFramesBothLocalLoanSetsAndLinearSpectators`. Under independent source-acceptance and rendezvous-admission gates, a successful paired source Choice replay and externally established selected continuation, it proves both local `SessionStep` resource transitions preserve their own **complete shared-loan functions** and every linear binding other than their respective exact predecessor and successor names. These are universal *within the proof-side abstract ResourceContext representation*, not native Haskell universality. The proof imports existing `FSEM02JointSourceChoice.v`, `FSEM02ProtocolHeadProgression.v`, `SessionStep.v` and `ConcurrencySemantics.v`, and adds no `Axiom`, `Admitted` or `Parameter`.

The finite Haskell Go/Cancel test establishes observed two-sided *affine* and loan preservation and equality of actual native local/joint Maps. It does **not** establish general Haskell↔Rocq map/set refinement or an identification of abstract `SessionStep.endpointType` with native `TyEndpoint`. Protocol/role instance, actual activation, disposal, source-offer coverage, peer choice, selected root, runtime scheduling, effect or assurance authority, and `RendezvousValid` are all independently justified inputs when used, not derived from the paired model.

## Gates and status

The branch-specific preflight `.github/workflows/fsem02-choice-dual-spectator-frame-preflight.yml` runs strict native `-Werror` source/Core Go/Cancel accepted/rejected witnesses and Rocq 9.2 compilation, with no new admission. Prior successful paired Choice bridge [#1938](https://github.com/abiggerhammer/phil/pull/1938) is the predecessor. No PR merge is permitted without **all required exact-head checks**, fresh post-ready FSEM claim guard, protected expected-HEAD squash, and exact audited claim release. FSEM-02 is not complete or normative.
