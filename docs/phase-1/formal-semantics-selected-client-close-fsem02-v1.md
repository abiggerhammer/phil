# FSEM-02: exact source-selected client close after stateful choice (bounded v1)

**Status: non-normative; FSEM-02 remains open.** Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613). Follows [stateful choice and owner ledger](formal-semantics-stateful-choice-fsem02-v1.md). This opt-in bridge does not change the accepted EBNF, semantic authority, TCB, or the separately owned FSEM-01 lane.

## Judgment and supplied authority

The source client is the exact parsed Grammar-v1 fragment `let chosen = select L on endpoint; close chosen;`; the peer is the independently parsed total duplicate-free payload-free `offer` catalog, with each arm `return unit`. Production binder checking resolves the client predecessor and close successor to their **actual declaration-rooted identities**. The caller separately supplies the closed binary protocol instance, Client/Server role keys, activated two-process network, activation-derived communication state (protocol and global owner-occurrence maps), selected peer label, fresh server successor identity and client terminal outcome. None of these external authorities is inferred from source spelling.

```text
checked SelectClose(client, L, next); checked OfferCatalog(server, L);
activated Σ, instance/roles/processes, peer=L, outcome=O
  -- joint stateful select/offer --> Σ₁
Σ₁[client.next : End O], unique owner(client,next)
  -- source close next / native closeProcessEndpointState --> Σ₂
```

The new `grammarV1CloseStatefulSourceChoiceClient` re-executes `grammarV1CheckStatefulSourceChoice` from the original activation-derived state, independently deriving `next` from the checked source. It then invokes actual Core `closeProcessEndpointState` on that live continuation. Success retires **only** the chosen client's terminal endpoint/resource and its one activation occurrence. It preserves the live Server `End O` continuation, Server occurrence identity, other process contexts, and the independently activated affine spectator. No cached successor is accepted as authority. Failure is an exact `GrammarV1StatefulChoiceClientCloseSourceError` or `...CoreError` and produces no successor.

The server's `return unit` is **not** an endpoint close, a source `dispose`, or authorization to close a peer: its live terminal endpoint remains. Root completion, process-local resource disposal, assurance discharge, and external architecture/peer admission remain separate obligations.

## Executable accepted/rejected witnesses

`test/Phase1FSEM02SourceJointChoiceMain.hs` now exercises the existing *complete parsed programs* `test/fixtures/fsem02-source-choice-v1/accepted.phil` (Go => Done) and `test/fixtures/fsem02-source-joint-choice-v1/client-cancel.phil` (Cancel => Cancel) against actual production joint rendezvous, owner ledger and native client close. It checks deterministic replay, complete state equality with an independent Core close, exact client occurrence retirement, still-open server End and spectator preservation.

A minimally rejected complete source `test/fixtures/fsem02-source-offer-replay-v1/wrong-body.phil` changes a single source arm from `return unit` to `return true`. The adapter rejects exactly `GrammarV1ComponentOfferArmBodyUnsupported` under the source/coverage error wrapper, **before** any close. Further executable negatives reject an incorrect client End outcome as `ProtocolSessionError (CloseOutcomeMismatch Done Cancel)`, stale select/offer predecessors, missing activated client occurrence, and second use of a consumed client endpoint as `EndpointClosureOccurrenceUnknown`. No rejection returns a state.

## Proof and limits

`proof/Phil/Core/FSEM02SelectedClientClose.v` models conditional exact owner removal for the selected client, proves missing-owner rejection, exact-before ownership and arbitrary-spectator preservation, and composes this with the existing `FSEM02StatefulSourceChoice.v` and `SessionStep.v` to establish conditional client resource consumption while preserving the offer successor occurrence and other owner keys. The proof is a finite functional owner model; Haskell's `Map` equality, source binder projection, unique activation evidence, real Core close and SessionStep's abstract endpoint token have **not** been universally related by refinement. `ConcurrencySemantics.v` separately retains rendezvous authority, not a scheduler/fairness theorem.

Focused work-branch checks: `.github/workflows/fsem02-choice-client-close-preflight.yml`, two independent warning-free Haskell/parsed-source and Rocq 9.2/no-admission jobs. All branch protection and fresh ready-for-review claim-guard checks remain required before merge. **Not proved:** source offer arm execution, peer close, full source architecture/root validity, generalized resource and effect semantics, Haskell-to-Rocq refinement, FSEM-02 completion or normative graduation.
