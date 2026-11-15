# FSEM-02: exact Close fault classification at every mixed Ping prefix

**Status:** non-normative bounded production-source/Core conformance and separately conditional Rocq phase laws. Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613); extends the [13,440 mixed Ping/Close schedules](formal-semantics-source-ping-mixed-interleavings-fsem02-v1.md), which previously checked only selected premature-Close prefixes.

## Checked executable obligations

The production [accepted source fixture](../../test/fixtures/fsem02-protocol-progression-v1/accepted.phil) is parsed for exact Client/Server Send/Receive, End successor and nominal Ping projection. The minimal [rejected stale-Close fixture](../../test/fixtures/fsem02-protocol-progression-v1/stale-close.phil) must still reject with precisely `GrammarV1ComponentSendCloseCloseMismatch` (expected `done`, actual `endpoint`). Independent external architecture activation and the selected checked binary protocol instance are premises.

The Haskell regression replays **all 13,440 legal orders** of three disjoint Ping rendezvous and six terminal Closes (a pair's Ping must precede its own Closes). At **each of ten boundaries** (before nine events and at the terminal state), it probes **each of six process endpoints** through actual production `checkProtocolAction`, checking the binding and linear owner against the exact phase:

- **Pre-Ping Send/Receive:** premature Close of the live predecessor rejects with `ProtocolSessionError (UnexpectedSessionAction (CloseAction Done) actualHead)`, where the actual head is the source-derived Send or Receive.
- **Post-Ping live End:** a Close carrying the deliberately incorrect `FSEM02.BadTerminal` rejects with exact `ProtocolSessionError (CloseOutcomeMismatch Done FSEM02.BadTerminal)`.
- **Retired End:** another Close rejects with `ProtocolEndpointUnknown` naming the exact retired successor. The predecessor and successor must both be absent from linear ownership.

This is **806,400 deliberately invalid probes**, followed by every legal suffix from the original committed prefix, with the final state equal to the canonical six-process terminal map. The independent borrowed affine spectator must be unchanged at every prefix. Rejections are pure checker results, not invented state-mutating steps; no failure is permitted to advance the scheduler or recreate an owner.

## Proof boundary and omissions

[Eight Rocq 9.2 theorems](../../proof/Phil/Core/FSEM02PingMixedPrefixFault.v) classify an injected bad Close by an abstract three-phase ledger, prove ledger preservation under refusal, independent-site framing/commutation and retry after failure. They are **conditional phase laws**, not extraction or an implementation-refinement theorem. `nat` keys are model surrogates, not a proved encoding of native `ProcessKey`; neither source-to-phase representation correspondence nor diagnostic-priority completeness is established.

This does **not** grant protocol instance, role, architecture/root, terminal disposal, selected-root, scheduler/environment, or assurance authority from source syntax. It does not prove universal source-to-Rocq simulation, deadlock freedom, fairness, global type soundness, or FSEM-02 completion. See [SessionStep.v](../../proof/Phil/Core/SessionStep.v) and [ConcurrencySemantics.v](../../proof/Phil/Core/ConcurrencySemantics.v) for related non-identical abstractions. **FSEM-02 remains open and non-normative.**
