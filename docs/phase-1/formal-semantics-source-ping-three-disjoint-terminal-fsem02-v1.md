# FSEM-02: three independent Ping rendezvous and six-End Close scheduling

**Status:** non-normative bounded source/native conformance plus separately conditional Rocq finite-map lemmas. Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613). Extends the two-pair [24-order slice](formal-semantics-source-ping-disjoint-terminal-interleavings-fsem02-v1.md) and its [prefix fault/retry slice](formal-semantics-source-ping-close-prefix-fault-retry-fsem02-v1.md).

## Exact bounded judgment and evidence

Independently parse and check the admitted Grammar-v1 [Ping program](../../test/fixtures/fsem02-protocol-progression-v1/accepted.phil), its checked Client/Server Send/Receive predecessor and successor occurrences, its dual local heads, and the supplied nominal binary protocol instance. Parse the minimally rejected [stale-Close source](../../test/fixtures/fsem02-protocol-progression-v1/stale-close.phil) and require exactly `GrammarV1ComponentSendCloseCloseMismatch`.

Supply **three disjoint pairs of active process sites** in a specifically constructed architecture graph, with original Core endpoint/linear-resource state. No source spelling grants architecture/activation or nominal authority. The production regression executes all 3! = 6 orders of the three actual `checkProcessCommunication` Ping rendezvous. Every order must consume exactly the source-derived typed predecessor and introduce one exact `TyEndpoint (End Done)` at each of the six sites, yielding an identical process map.

For each rendezvous order, execute all 6! = 720 local terminal Close orders (4,320 fully checked schedules). Require every successful production `checkProtocolAction` Close to consume exactly the live typed End owner with no successor and every final map to be equal. Require exact `ProtocolEndpointUnknown` on repeated Closes, `RendezvousEndpointNotOwnedByProcess` on stale Ping replays, and `ProtocolSessionError (CloseOutcomeMismatch Done Wrong)` on a live wrong-outcome Close. No failed attempt produces a successor map. A separately borrowed affine Server-C spectator must remain unchanged, and valid replay after a refused outcome must converge.

## Conditional proof and explicit nonclaims

[Seven Rocq 9.2 finite-map theorems](../../proof/Phil/Core/FSEM02PingTripleDisjointTerminal.v) cover triple update framing, two exact key observations, two adjacent swap equalities, refusal preserving committed state, and valid retry. They build on `FSEM02PingClosePrefixFaultRetry.v`; site keys are `nat` surrogates rather than proven native `ProcessKey` encodings. Their admission flag is an **external input**.

This does **not** prove 4,320 Haskell traces as a refinement, a general n-pair scheduler theorem, unbounded execution, fairness, or liveness. Protocol activation, instance/role authority, terminal disposal, selected root and assurance remain external premises. Neither [SessionStep.v](../../proof/Phil/Core/SessionStep.v) nor [ConcurrencySemantics.v](../../proof/Phil/Core/ConcurrencySemantics.v) is promoted to normative Phase 1 semantics. **FSEM-02 remains open and non-normative.**
