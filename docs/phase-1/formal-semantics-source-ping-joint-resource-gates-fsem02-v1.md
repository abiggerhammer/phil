# FSEM-02 — source Ping joint predecessor resource gates (non-normative)

Tracking [#1613](https://github.com/abiggerhammer/phil/issues/1613). This
bounded slice checks **nonterminal Send/Receive**, rather than repeating
terminal End/Close coverage. The independently parsed Grammar-v1 Ping
source supplies the actual Client Send and Server Receive predecessor and
successor binder identities. The checked binary family and projected dual
heads are verified; process network activation, protocol instance, role and
selected root remain separate explicit premises.

## Executable production tests

`test/Phase1FSEM02ProtocolProgressionMain.hs`,
`sourcePingJointPredecessorResourceGates`, executes the accepted full source
`test/fixtures/fsem02-protocol-progression-v1/accepted.phil` and separately
checks the minimally rejected
`test/fixtures/fsem02-protocol-progression-v1/stale-close.phil` with its exact
source binder rejection, not a generic parsing failure.

For each role independently, the actual production joint rendezvous checker
is given adversarial Core contexts whose endpoint metadata remains valid
but whose predecessor **linear resource** is (1) missing,
(2) the wrong `TyUInt 8`, or (3) an incorrect `TyEndpoint (End Done)`.
The tests require `RendezvousProtocolError` for the exact process, endpoint
and respective `ProtocolEndpointResourceMissing`,
`ProtocolEndpointResourceTypeMismatch`, or
`ProtocolEndpointSessionMismatch` error constructor. A simultaneous
Client-missing/Server-wrong-type input checks Client-first error precedence;
restoring only Client exposes the exact Server failure. No one-sided result
is produced. These are *deliberate external test faults*, not source-granted
resource edits or implicit rollback.

Only an explicit restoration of both originally checked resource contexts
admits the Send/Receive. Both exact old predecessor names disappear,
both continuation successors receive the independently projected End
session, the process key set is unchanged, and an unrelated borrowed
affine spectator and active loan survive. Deterministic replay of the
original healthy state yields the same complete native successor; replay
from the consumed state rejects the exact stale predecessor.

## Independently checked finite model

`proof/Phil/Core/FSEM02PingJointAtomicity.v` now contains
`fsem02PingJointResourceAdmission` and five conditional Rocq 9.2
theorems: either admission-gate refusal, either missing-linear-predecessor
refusal, and success requiring both gates while consuming both predecessors,
typing both successors and preserving affine maps and active loans.
The admitted gate booleans are **external observations**, not a proof
that Rocq's abstract `endpointType` equals a production
`TyEndpoint` or a derivation of the native error-constructor order.

The pre-PR focused strict GHC 9.6.7 and Rocq 9.2 gates are
`.github/workflows/fsem02-ping-joint-resource-gates-preflight.yml`.
Full current-head CI, the fresh post-ready claim guard and protected
merge are separate mandatory controls.

**Nonclaims:** no universal Surface/Haskell-to-Rocq refinement, scheduler,
network fairness, general architecture-root validity, disposition/disposal
authority, assurance or normative semantics. No syntax, TCB or branch rule
is changed. FSEM-02 remains open.
