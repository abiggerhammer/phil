# FSEM-02: disjoint Ping terminal Close prefix fault/retry

**Status:** non-normative bounded source/production conformance plus separate conditional Rocq 9.2 finite-map results. [Tracking issue #1613](https://github.com/abiggerhammer/phil/issues/1613).

## Specific gap

The [four-End interleaving slice](formal-semantics-source-ping-disjoint-terminal-interleavings-fsem02-v1.md) verifies all 24 legal Close orders and one rejected wrong-outcome probe after a single Close. It does not exercise invalid Close attempts at **every prefix**. This slice treats rejection as an observable transition outcome with a committed-prefix state that cannot be rolled back by an unrelated failed attempt.

## Production and source witnesses

The [production regression](../../test/Phase1FSEM02ProtocolProgressionMain.hs) continues to parse independently the accepted [Grammar-v1 Ping program](../../test/fixtures/fsem02-protocol-progression-v1/accepted.phil) and minimally rejected [stale-Close program](../../test/fixtures/fsem02-protocol-progression-v1/stale-close.phil), requiring the exact `GrammarV1ComponentSendCloseCloseMismatch` rejection class. The externally activated two-Ping-pair network is **not** granted by the source fixture.

After both disjoint actual `checkProcessCommunication` rendezvous, the test enumerates each of the 24 terminal Close permutations and all five prefix lengths (120 schedule-prefix observations, including initial and terminal). At every prefix it executes four deliberately bad `checkProtocolAction` Close attempts (480 probes): a *live* typed End with an invalid outcome must refuse with exact `ProtocolSessionError (CloseOutcomeMismatch Done Wrong)`; a *retired* endpoint must refuse first with exact `ProtocolEndpointUnknown`. It checks actual endpoint context/identity, process population, exact stale predecessor refusals, survival of the active affine loan on Server B, and successful replay of the remaining legal Close suffix to the same complete terminal context.

A bad request yields a Haskell `Left` and no successor context. Reapplying a valid request to the same immutable prefix witnesses absence of rollback/hidden mutation in this finite pure API; this does **not** establish atomicity of arbitrary external effectful backends.

## Conditional proof boundary

The [Rocq model](../../proof/Phil/Core/FSEM02PingClosePrefixFaultRetry.v) takes an explicit *external* boolean admission decision for one Close attempt and finite nat-key process-map contexts. Six machine-checkable results cover failed-prefix preservation, exact successful slot, arbitrary unrelated-site frame, disjoint write commutation, refusal after a prior committed write, and retry after refusal. They do **not** establish native error ordering, completeness of actual admission decisions, Haskell `ProcessKey` representation fidelity, or a general 24-schedule simulation theorem.

Typed End heads, nominal protocol instance/roles, process activation, terminal outcome grants/disposal, selected root and assurance remain external authorities. [`SessionStep.v`](../../proof/Phil/Core/SessionStep.v) and [`ConcurrencySemantics.v`](../../proof/Phil/Core/ConcurrencySemantics.v) remain existing abstractions; no syntax, TCB, global progress/fairness, or normative graduation is asserted. **FSEM-02 stays open.**
