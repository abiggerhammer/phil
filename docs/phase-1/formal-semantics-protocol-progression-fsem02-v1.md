# FSEM-02 / exact local protocol-head progression (bounded v1)

**Status: non-normative; subject to exact-head CI.** Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613). No Phase 1 syntax, TCB, or semantic authority is changed.

## Judgment and admitted inputs

The proposed local judgment is

```text
Sigma ; P(instance, role, occurrence, head) ; Delta
  |- action(current, successor?, payload?, label?, outcome?)
  ==> (P', Delta') | rejected(error)
```

`Sigma` supplies an already checked protocol family/projection; `P` carries exact
instance/role/endpoint identity, `Delta` carries actual linear resources, and
`action` supplies the external action/label/outcome. For this slice, accepted
source-derived actions are Ping send, receive and terminal close. The separately
checked Core-only offer case supplies an explicit protocol instance and role;
it does **not** assert source-level offer elaboration.

- **Send** at `Send(x:T,S)` and **receive** at `Receive(x:T,S)`: exact
  current `TyEndpoint` and instance/role must agree; consume current linear
  endpoint once; allocate a distinct, fresh successor with continuation `S`.
  A permitted message occurrence must be checked separately by the producer
  and the rendezvous/message-admission boundary.
- **Offer(label)** at `Offer{...label:S...}`: the label must exist uniquely;
  the same consume/fresh-successor rule applies to that branch's `S`.
- **Close(outcome)** at `End(expected)`: exact outcome equality; consume
  predecessor with no successor. A nonterminal head cannot close.
- **Rejected** is a precise `ProtocolCheckError` or source checker error, not
  a fictional successor state. Wrong local head gives
  `ProtocolSessionError (UnexpectedSessionAction ...)`; stale predecessor
  gives `ProtocolEndpointUnknown name`; duplicate successor gives
  `SuccessorReusesEndpointName`; missing offer label gives
  `UnknownSessionLabel`; wrong terminal outcome gives `CloseOutcomeMismatch`.

## Independently executable witnesses and tests

- `test/fixtures/fsem02-protocol-progression-v1/accepted.phil` is a
  whole-source Ping with selected root, two activated endpoints and an
  explicit external `entry payload : U8`. It is parsed, has its binary
  family instantiated and role projections checked, and supplies both
  source-resolved endpoint/successor binder identities to **actual**
  `Phil.Core.Protocol.checkProtocolAction` send/receive/close calls.
  The integration test checks exact `TyEndpoint` successor, predecessor
  removal in both production maps, exact instance/role propagation, terminal
  absence, and stale replay errors.
- `test/fixtures/fsem02-protocol-progression-v1/stale-close.phil` differs
  by **one source operand** (`close endpoint;` rather than
  `close done;`). The production source binder checker must report exactly
  `GrammarV1ComponentSendCloseCloseMismatch(done, endpoint)`, **not**
  merely parse failure. This negative has an otherwise still-recognized
  complete source program.
- `test/Phase1FSEM02ProtocolProgressionMain.hs` also exercises real Core
  offer, wrong session head, wrong close outcome, self-successor rejection,
  plus second-action stale send/receive errors. Existing
  `test/Phase1INT008SourcePingTerminalMain.hs` separately drives the
  whole-source Ping through the existing production synchronous rendezvous
  and terminal network checks. The new local test **does not itself claim**
  the rendezvous is a consequence of a static typing theorem.

## Rocq contract and remaining obligations

`proof/Phil/Core/FSEM02ProtocolHeadProgression.v` defines a computable
head/action selector for send/receive/offer/close and proves: successful
continuation consumes the predecessor and inserts the specified successor;
successful close consumes without successor; wrong heads, absent offer labels,
wrong close outcomes, same-name successors and stale linear owners cannot
succeed. It conditionally composes local consumption with
`ConcurrencySemantics.restricted_rendezvous_transfers_exact_owner`
**given `RendezvousValid`**. It reuses
`SessionStep.continueEndpointResource_success_exact` and
`closeEndpointResource_success_exact`, whose `endpointType` is an existing
abstract proof-side token, **not** a proved `TyEndpoint` equality.
No new `Admitted`, `Axiom`, or `Parameter` is added.

**Trust premises / nonclaims:** the finite source parser and checked-binder
projection; source-derived binary-family/projection inputs; Haskell
`Data.Map` identities; Type/Error equality across code and model; checked
`RendezvousValid` for physical/message ownership transfer; and the abstract
`Ty` token used in the historical SessionStep proof. No universal
Haskell↔Rocq state-refinement theorem, source-to-runtime simulation,
payload-copy/move theorem, full source-level offer checking, cancellation
semantics, fairness, deadlock freedom, full FSEM-02 closure, or normative
graduation is claimed. Further FSEM-02 slices must address generalized
restricted message ownership transfer, source offer/select elaboration and
source-to-Rocq refinement/evidence before the family is considered complete.

Focused pre-PR checks: `.github/workflows/fsem02-exact-head-preflight.yml`
(2 independent Haskell and Rocq 9.2 jobs). Any PR must also pass exact-head
claim-guard, branch protections and all applicable CI.


### Additional bounded terminal peer step (FSEM-02)

[Explicit Server End Core close after checked Client choice/close](formal-semantics-explicit-peer-close-fsem02-v1.md) separately requires externally supplied Server terminal authority; an offer arm's `return unit` does not count as source endpoint closure, process/root completion, or normative semantics.

### Additional bounded terminal order evidence (FSEM-02)

[Source-checked, explicitly authorized terminal End close order diamond](formal-semantics-terminal-close-diamond-fsem02-v1.md) independently replays Client-then-Server and Server-then-Client native Core closes, and accepts only complete successor equality. Server endpoint disposal remains externally supplied, not source `return unit` authority. This is finite checked conformance and a conditional owner-ledger theorem, not universal refinement or FSEM-02 completion.
