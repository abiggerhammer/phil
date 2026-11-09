# FSEM-02 / checked source terminal endpoint closure (bounded)

**Status: non-normative.** Tracked in [#1613](https://github.com/abiggerhammer/phil/issues/1613). Does not change the Phase 1 [surface EBNF](../../grammar/phase1-surface.ebnf), semantic contracts, nominal authority, or TCB. This slice *extends*, rather than replaces, the [restricted source send/receive owner-transfer evidence](formal-semantics-restricted-source-transfer-fsem02-v1.md).

## Judgment and exact authority boundary

`(sourceSendClose, sourceReceiveClose, checkedRendezvous, activatedNetwork, processKeys, instanceRevision, roles, outcomes) --close sender; close receiver--> state'`

The only admitted source shapes are the two **actual parsed** Grammar-v1 component bodies `let done = send payload on endpoint; close done;` and `let (done, received) = receive Bytes[8] on endpoint; close done;`. Their `close` operands must resolve to the exact **fresh successor binders**, not the consumed predecessor. `grammarV1CheckRestrictedSourceClose` rechecks each source declaration-rooted plan against the *already checked* `GrammarV1RestrictedSourceTransition` and rejects plan mismatch or unsupported body rather than reinterpreting source spelling. It consumes the rendezvous transition's **actual** post-send/receive state.

The caller supplies exact activated network and process identities, checked protocol instance revision, both nominal role keys and both expected terminal outcomes. Parsing alone supplies **none** of that authority. The existing production `closeProcessEndpointState` checks active membership, unique activation-owned endpoint occurrence, exact protocol role/revision, session `End` outcome and linear endpoint resource correspondence. In sequence, the first check retires the sender's source-resolved successor; the second retires the receiver's. Only the final state is returned, so a failed second check does not return a partial success. Each successful close removes precisely one owner occurrence and one endpoint binding/resource; no unrelated owner is changed.

**Rejection classes:** source wrong close binder → `RestrictedSourceCloseSenderError (GrammarV1ComponentSendCloseCloseMismatch ...)`; absent/previously retired receiver owner → `RestrictedSourceCloseReceiverCoreError (EndpointClosureOccurrenceUnknown ...)`; incorrect terminal outcome → `ProtocolSessionError (CloseOutcomeMismatch ...)`; incorrect session-head agreement → `ProtocolEndpointSessionMismatch`; incorrect role → `ProtocolRoleMismatch`. Stale repeated close is an `EndpointClosureOccurrenceUnknown` sender error. All failures return `Left` with **no successor state**.

## Independent evidence and nonclaims

The accepted and minimally rejected executable source witnesses remain `test/fixtures/fsem02-restricted-source-transfer-v1/accepted.phil` and `rejected-stale-close.phil`: the negative changes only `close done` into `close endpoint`. `test/Phase1FSEM02RestrictedSourceTransferMain.hs` now replays the accepted rendezvous followed by **both actual source-close commands**, checks deterministic replay, exact owner-map double deletion, actual Core protocol/resource consumption, preservation of restricted received `Bytes[8]` payload and affine spectator, and rejects stale/missing-owner/head/role/outcome and wrong-source cases at exact error classes.

`proof/Phil/Core/FSEM02SourceClose.v` models conditional owner-ledger pair retirement with explicit `sourceValid`/`headsValid` premises and proves exact two-key removal, rejection on missing owners and arbitrary-spectator preservation. Its separate paired resource theorem composes these model results with `SessionStep.closeEndpointResource_success_exact`. The prior `ConcurrencySemantics.v` and `FSEM02RestrictedSourceTransfer.v` establish different bounded premises; these models do **not** establish a universal extracted source→Haskell→Rocq simulation. No new `Admitted`, `Axiom` or `Parameter`.

**Not proved:** source architecture/root admission, discharge of receiver's still-live restricted payload, process terminal facts, assurance/obligations, network fairness, deadlock freedom, full Phase 1 source execution, universal Haskell↔Rocq refinement or normative language semantics. A successful endpoint close does not itself make a process or root terminal.

Focused exact-head pre-PR checks: `.github/workflows/fsem02-source-terminal-close-preflight.yml` executes warning-free Haskell production and accepted/rejected source witnesses plus Rocq 9.2 dependency compilation and new-admissions scan **before** opening broad PR CI.
