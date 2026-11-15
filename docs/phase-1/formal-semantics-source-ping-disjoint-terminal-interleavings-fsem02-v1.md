# FSEM-02: disjoint Ping terminal Close interleavings

**Status:** bounded non-normative production Haskell source-conformance with separate conditional Rocq 9.2 finite-map lemmas. Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613).

## New boundary checked

The [disjoint Ping pair slice](formal-semantics-source-ping-disjoint-pairs-fsem02-v1.md) established first-step Send/Receive order commutation. The [shared-Client terminal slice](formal-semantics-source-ping-shared-client-terminal-close-fsem02-v1.md) established two End Close orders for one pair competing with another. Neither exhaustively checked the **four independent local Close orders after both disjoint pairs succeed**. This finite slice enumerates all 4! = 24 interleavings, not an arbitrary scheduler theorem.

## Actual source/production witnesses

The test in [Phase1FSEM02ProtocolProgressionMain.hs](../../test/Phase1FSEM02ProtocolProgressionMain.hs) parses the real Grammar-v1 [accepted Ping fixture](../../test/fixtures/fsem02-protocol-progression-v1/accepted.phil) and independently verifies the minimally rejected [stale-close source](../../test/fixtures/fsem02-protocol-progression-v1/stale-close.phil) fails with exact GrammarV1ComponentSendCloseCloseMismatch. The same checked Client/Server predecessor and successor plan is externally instantiated twice at four independently active sites. This does **not** mean the two-component source fixture itself authorizes four components.

Production checkProcessCommunication must progress either pair first, leave the untouched pair unchanged and yield the identical complete map for both A/B schedules. All four final End endpoint/linear owners are checked exactly. Then each of 24 permutations of production checkProtocolAction terminal Close consumes its own typed End, creates no replacement, and must leave the same complete process map. Each site's repeated Close rejects with exact ProtocolEndpointUnknown; both stale joint Send/Receive requests reject with exact RendezvousEndpointNotOwnedByProcess and Client predecessor identity. A separately checked wrong-outcome Close after one committed Close must reject with exact CloseOutcomeMismatch without advancing the state; subsequent valid retries must reach the same completed map. An affine/active-shared-loan spectator in Server B must survive all orders.

Four-site activation, protocol instance/role grants, terminal outcomes, process disposal, selected root and assurance are supplied externally, not inferred from source spelling.

## Proof boundary

[The conditional Rocq model](../../proof/Phil/Core/FSEM02PingDisjointTerminalInterleavings.v) composes the existing [disjoint-pair finite step model](../../proof/Phil/Core/FSEM02PingDisjointPairs.v) with four **externally supplied** closed resource contexts. Six lemmas cover pair-order commutation, first/second refusal producing no successor, two exact closed slots and preservation of any uninvolved process key. The Rocq model does **not** prove 24 native Close permutations, real Haskell Map/ProcessKey fidelity, success of native Send/Receive validation, or a universal Source-to-Rocq simulation. Native permutations are separately tested finite conformance evidence.

The existing [SessionStep.v](../../proof/Phil/Core/SessionStep.v) and [ConcurrencySemantics.v](../../proof/Phil/Core/ConcurrencySemantics.v) are reference abstractions, not new normative semantic authority. No grammar, proof TCB, required CI, other hamster lane or Phase 1 normative rule changes. FSEM-02 remains open.
