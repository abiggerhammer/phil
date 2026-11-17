# FSEM-02 — dual projected-head / independent resource fault ladder

**Status:** bounded, non-normative production Haskell conformance observations and conditional Rocq 9.2 model. Tracking [#1613](https://github.com/abiggerhammer/phil/issues/1613).
This follows the [cross-peer head/resource-shape refusal slice](formal-semantics-source-ping-adaptive-cross-peer-head-resource-shape-retry-fsem02-v1.md). No syntax, TCB or authority changes.

## Source and externally supplied inputs

The [accepted Grammar-v1 Ping source](../../test/fixtures/fsem02-protocol-progression-v1/accepted.phil) checks real typed Send/Receive U8 predecessors and End Done successors. The [minimally rejected stale-Close witness](../../test/fixtures/fsem02-protocol-progression-v1/stale-close.phil) must reject as **exactly** GrammarV1ComponentSendCloseCloseMismatch. These source witnesses do not select architecture instances, role activation, partner matching, selected root, terminal disposal authority or scheduling. All remain independently supplied.

After one of nine independently selected Ping pairs, four authorized nonempty Close prefixes and four legal suffix orders, the actual production Haskell checkProcessCommunication runs 144 committed configurations. Each receives four three-fault variants: BOTH remaining Client and Server projected source session heads are malformed, and a non-endpoint TyUInt 8 or wrong-session TyEndpoint (End Done) linear resource is placed on one of the free peers (576 distinct states). Injection is not a source transition.

## Precise refusals and replay

The refusal order is **Client projected head, Server projected head, then linear resource shape**. The first two calls must each fail with exact RendezvousProjectionSessionMismatch (including expected/observed session and process). Explicitly repairing projected metadata alone when the independently corrupted resource lives on that process must preserve that resource fault. The third call must fail as an exact ProtocolEndpointResourceTypeMismatch or ProtocolEndpointSessionMismatch, nested in RendezvousProtocolError at the owning peer. No rejected call has a successor, guessed authority or opaque repair.

Only separately restoring the third malformed resource may reconstruct the original entire committed pre-rendezvous map and replay the same externally authorized suffix. Each intermediate refusal must preserve earlier terminal Closes and the borrowed affine spectator's live loan state.

## Conditional model and verification boundary

The [five Rocq lemmas](../../proof/Phil/Core/FSEM02PingAdaptiveDualHeadResourceLadder.v) establish four ordered three-stage diagnostics on abstract finite nat identities and one conditional phase-map replay after full repair. They compose existing projected-head, resource-shape and half-Close lemmas. They do **not** prove the actual Haskell Context/Map representation matches the Rocq carrier, native source elaboration fidelity, general Haskell-to-Rocq refinement, global progress, fairness, deadlock freedom, or FSEM-02 normative completion.

The [focused preflight](../../.github/workflows/fsem02-adaptive-dual-head-resource-ladder-preflight.yml) builds production GHC 9.6.7 with -Werror, runs warning-free source fixtures and production regressions, and independently compiles admission-free Rocq 9.2 proofs before broad PR CI. Exact-head required checks, fresh post-ready FSEM guard, normal protected merge and trusted claim release remain distinct gates.
