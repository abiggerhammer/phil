# FSEM-02: mixed Ping rendezvous and terminal Close partial orders

**Status:** non-normative bounded production source/Core conformance, with separately conditional Rocq finite-map laws. Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613). This extends the [three-pair all-rendezvous-first 4,320 schedules](formal-semantics-source-ping-three-disjoint-terminal-fsem02-v1.md).

## Actual executable obligation

The accepted [Grammar-v1 Ping source](../../test/fixtures/fsem02-protocol-progression-v1/accepted.phil) is parsed with the production checker; Client/Server Send/Receive predecessor and successor binders, terminal heads and duality are checked. The minimally rejected [stale-Close source](../../test/fixtures/fsem02-protocol-progression-v1/stale-close.phil) must produce exactly `GrammarV1ComponentSendCloseCloseMismatch`.

An independently constructed architecture activates three disjoint Client/Server process pairs with original linear endpoint owners and the checked binary protocol instance. Each of the **nine events** is either one joint production `checkProcessCommunication` Ping rendezvous or one of six production `checkProtocolAction` terminal Closes. Only the *same pair's* rendezvous must precede its own two Closes. Every legal order is executed: **9! / 3^3 = 13,440 schedules**, including full closure of a pair before another pair even rendezvouses. Every step must consume the exact live typed predecessor and owner; every complete process/resource map must equal the canonical fully retired state, preserving an independent borrowed affine spectator.

The negative witness additionally probes premature Close of live Send/Receive predecessors, both initially and after an unrelated pair's committed Close. It must refuse with exactly `ProtocolSessionError (UnexpectedSessionAction CloseAction <actual head>)`. This result does not infer disposal permission from source spelling. Other existing tests continue to check stale, wrong-outcome, replay and nominal identity errors.

## Proof boundary

[Six conditional Rocq 9.2 theorems](../../proof/Phil/Core/FSEM02PingMixedRendezvousClose.v) prove finite-map commutation of an independently admitted local Close with an unrelated two-process update, commutation of two Closes past the unrelated pair, independent-site recording and spectator framing, and refusal/retry no-rollback behavior. Model site keys are `nat` surrogates, not certified native `ProcessKey` encodings.

This is finite Haskell conformance, **not universal Haskell-to-Rocq refinement** or a general nine-event scheduler theorem. Protocol instance, role grants, architecture activation, terminal disposal, selected root, environment and assurance are all **external premises**. The admitted conditional relation to [SessionStep.v](../../proof/Phil/Core/SessionStep.v) and [ConcurrencySemantics.v](../../proof/Phil/Core/ConcurrencySemantics.v) is not normative. No TCB, grammar or branch-protection change. **FSEM-02 remains open.**
