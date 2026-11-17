# FSEM-02 — dual projected-head / dual linear-resource four-fault ladder

**Status:** bounded, non-normative Haskell execution and conditional Rocq 9.2 model. Tracking [#1613](https://github.com/abiggerhammer/phil/issues/1613). Follows the [three-fault dual-head slice](formal-semantics-source-ping-adaptive-dual-head-resource-ladder-fsem02-v1.md); normative syntax, TCB and authority are unchanged.

## Admitted source and external control

The actual [accepted Grammar-v1 Ping source](../../test/fixtures/fsem02-protocol-progression-v1/accepted.phil) supplies typed Send/Receive U8 and End Done. The [minimally rejected stale Close](../../test/fixtures/fsem02-protocol-progression-v1/stale-close.phil) rejects with exactly `GrammarV1ComponentSendCloseCloseMismatch`. Source syntax does **not** grant role activation, nominal instance, partner/root selection, Close/disposal authority, scheduler choices or assurance.

After an externally selected Ping pair and an authorized nonempty terminal Close prefix, 9 first pairs × 4 prefixes × 4 legal remaining partner orders × 4 independent Client/Server resource-shape combinations yield **576 four-fault states**. Both free peers have malformed projected session heads. Both also have independently corrupted linear predecessors (wrong `TyUInt 8` type or wrong-session `TyEndpoint (End done)`). Injecting faults is never an admitted transition.

## Ordered rejection / repair contract

The actual `checkProcessCommunication` is required to produce **Client projected-head mismatch → Server projected-head mismatch → Client resource type/session error → Server resource type/session error**, at the precise process and endpoint. Each failed request has no accepted successor. Each repair changes **only one** independent observation, never an unrelated owner, committed Close prefix or active affine spectator loan. Reconstructing exactly the original full state requires all four repairs, then must replay the **same** externally authorized suffix.

The [five conditional finite-carrier Rocq lemmas](../../proof/Phil/Core/FSEM02PingAdaptiveDualHeadDualResourceLadder.v) cover general four-stage error priority (including two mixed shape combinations), concrete dual-wrong-type and dual-wrong-session instantiations, the absence of an admitted successor on each refused stage, and full-repair half-Close phase-map restoration. They compose existing `SessionStep.v`, `ConcurrencySemantics.v` and subsequent FSEM-02 finite model abstractions. They are **not** a proof of native Haskell Map/Set representation correspondence, general source elaboration fidelity, universal implementation refinement, progress, fairness, deadlock freedom, normative status or FSEM-02 completion.

The [focused strict-Haskell/Rocq preflight](../../.github/workflows/fsem02-adaptive-dual-head-dual-resource-ladder-preflight.yml) precedes the broad exact-head PR matrix; the required claim guard, fresh post-ready guard, protected expected-head squash merge and verified trusted claim release remain distinct gates.
