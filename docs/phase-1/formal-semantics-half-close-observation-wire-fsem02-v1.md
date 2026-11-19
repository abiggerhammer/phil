# FSEM-02 half-Close OBS-V1 — stale intermediate retry and live-peer suffix

**NON-NORMATIVE / BOUNDED; FSEM-02 remains OPEN.** Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613).

## Scope and checked rule

This slice continues the exact complete Grammar-v1 accepted `Bytes[8]` Send/Receive/Close source and three minimally rejected source fixtures already checked by OBS-V1 and Close-order OBS-V1. Its explicit external premises are the protocol instance, message boundary certificate, activated client/server endpoint occurrences, roles, typed End Done heads, trusted terminal outcomes, disposition and architecture/root authority. Source spelling cannot grant these.

Given a successful restricted rendezvous and two distinct live terminal successors, the production `closeProcessEndpointState` executes either first Close. The repeated Close of that **same** retired successor must refuse with `EndpointClosureOccurrenceUnknown` and exact process/endpoint identity while the other endpoint remains live; the still-live peer Close then succeeds from the unchanged half-state and reaches exactly the already independently source-checked terminal state.

The native Haskell checker asserts both intermediate occurrence maps, payload and affine spectator preservation, the exact two refusal classes and identities, both successful remaining-peer suffixes, and equality of complete resulting `ProcessCommunicationState` (not merely final owner counts). Every source witness is checked before Core observations. Refusal is represented by `Left` with no successor state.

## Artifact / independent proof boundary

`test/Phase1FSEM02RestrictedSourceTransferMain.hs emit-rocq-half-close-observation` emits four tags in order: sender-half stale retry refused, receiver peer Close succeeds, receiver-half stale retry refused, sender peer Close succeeds. Strict GHC 9.6.7 CI compares emitted bytes to `FSEM02HalfCloseObservationData.v`; Rocq 9.2 compiles the exact finite datum, five finite facts and four conditional live-bit/owner-frame model theorems. No `Admitted`, `Axiom` or `Parameter` introduced.

This verifies those actual finite native source/Core observations and separate conditional model laws, **not** general Haskell Map/Set-to-Rocq state correspondence, universal Haskell-to-Rocq refinement, scheduler independence, terminal-disposal soundness, architectural/root selection, `satisfies C`, complete `SessionStep.v` / `ConcurrencySemantics.v` realization, or normative semantics. The existing Close-order OBS-V1 is retained.

Focused push workflow: `.github/workflows/fsem02-half-close-observation-preflight.yml`. This change still requires all exact-head required PR checks, fresh post-ready claim guard, normal expected-head protected squash merge and matching audited claim release.
