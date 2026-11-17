# FSEM-02 — adaptive cross-peer head/resource-shape diagnostic precedence

**Status:** bounded, non-normative Haskell observations and conditional Rocq 9.2
model. [Issue #1613](https://github.com/abiggerhammer/phil/issues/1613)
remains open. This extends the [cross-peer missing-owner
slice](formal-semantics-source-ping-adaptive-cross-peer-head-owner-retry-fsem02-v1.md)
to *non-endpoint* and *wrong-session endpoint* linear resource shapes on
the opposite, still-free participant. No normative syntax or authority changes.

## Typed source, premises and experiment

The existing accepted [Grammar-v1 Ping
program](../../test/fixtures/fsem02-protocol-progression-v1/accepted.phil)
checks real `send U8` / `receive U8` through typed `End Done`
successors; the minimally rejected
[stale Close](../../test/fixtures/fsem02-protocol-progression-v1/stale-close.phil)
still requires the exact `GrammarV1ComponentSendCloseCloseMismatch` class.
The source does not select three architecture copies, processes, a root,
a partner bijection, disposal authority or a scheduler. These remain external
inputs, as in earlier slices.

Actual production `checkProcessCommunication` runs on one of nine externally
selected first Ping pairs, four already committed terminal Close prefixes,
and four admissible ordered suffix choices (144 configurations). After
each prefix, one remaining Client/Server pair is still unspent with
source-checked typed session predecessors and a separate active affine
loaned spectator.

For each configuration we inject **four distinct simultaneous faults**
(576 total): a malformed `End Done` projected head on one free peer, and
either `TyUInt 8` (not a protocol endpoint) or `TyEndpoint (End Done)`
(the wrong session head) in the *other* peer's linear predecessor resource.
Neither mutation is a source transition or authorized environmental action.

## Required observations

The real production rendezvous must first return
`RendezvousProjectionSessionMismatch` with the exact poisoned process,
expected typed Send/Receive and observed `End Done`. This rejects the
whole attempted transition without a successor map. Restoring only the
malformed head process then exposes one of the remote peer's exact errors:

- `RendezvousProtocolError (ProtocolEndpointResourceTypeMismatch ...)`
- `RendezvousProtocolError (ProtocolEndpointSessionMismatch ...)`

Both errors identify the correct remote ProcessKey, predecessor endpoint,
and type or expected/observed sessions. Finally, separately restoring that
peer's original resource reconstructs the **entire** committed prefix map;
the independent externally chosen suffix must replay to the identical
accepted successor. The tests additionally preserve the already committed
terminal Closes and the active affine spectator's loan state at every
rejection. No automatic repair, opaque classification or additional
authority is inferred.

## Conditional proof and verification boundary

[Five Rocq lemmas](../../proof/Phil/Core/FSEM02PingAdaptiveCrossPeerHeadResourceShapeRetry.v)
establish directional head-first diagnostics, remote type/session exposure
on head repair, and exact admitted half-Close phase-map replay when both
observations are restored. They reuse the existing finite
`fsem02AdaptiveHeadShapeGate` and `fsem02MixPhaseMap` models; the `nat`
process/session carriers are **not** a proof of Haskell `ProcessContext`,
`Map` or parser/elaborator representation fidelity.

The source-derived executable witness is in
[`Phase1FSEM02ProtocolProgressionMain.hs`](../../test/Phase1FSEM02ProtocolProgressionMain.hs).
The [focused preflight](../../.github/workflows/fsem02-adaptive-cross-peer-head-resource-shape-retry-preflight.yml)
requires warning-free GHC 9.6.7 production compilation and actual source
witnesses plus Rocq 9.2 admission-free compilation *before* a broad PR.
Required exact-head PR checks, fresh post-ready claim guard, protected merge
and trusted claim release remain independent gates. This slice does **not**
establish universally quantified Haskell–Rocq refinement, general language
progress, source-derived architecture/disposal authority, scheduler/liveness
or complete FSEM-02.
