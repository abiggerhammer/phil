# Phase 1 audit remediation: session message continuation binding

Stable finding: `PHIL-AUD-SESSION-CONTINUATION-BINDING-001`  
Audit event: `PHIL-AUDIT-20260921-SESSION-MESSAGE-CONTINUATION`  
Original frozen source: `a9f2c745686d8ae1b923e21045554f4864956e76`

## Finding

The public Surface checker checked the concrete message at `send`, `receive`,
`select`, and `offer`, but the successor endpoint retained the protocol's formal
message binder unchanged.  A continuation such as `Bytes[n]` could therefore be
interpreted using an unrelated ambient `n`, while a legitimate occurrence whose
source name differed from the formal binder could be rejected.

The defect was one missing semantic step: after a message occurrence has been
checked, the formal message binder must be instantiated with the logical term
for that checked occurrence before the continuation is exposed.

## Repair

`Phil.Core.Session.instantiateMessageStep` now performs the explicit occurrence
binding step while leaving `sendEndpoint`, `receiveEndpoint`, `selectEndpoint`,
and `offerEndpoint` themselves as descriptor/resource transitions.

The substitution is binder-aware across:

- subsequent send/receive message binders;
- select/offer payload binders;
- endpoint and product types;
- `Bytes` indices, proof propositions, refinements, and validated subjects;
- pending-receive continuations; and
- nested recursive session structure.

If a later binder would capture a free name in the concrete occurrence term, it
is alpha-renamed before substitution.  If a continuation genuinely depends on
the formal message but Surface has no logical term for the concrete occurrence,
checking fails closed rather than retaining the stale formal binder.

Surface supplies the occurrence term at the semantic point where it is known:

- `send`: from the checked source expression before any resource move;
- `receive` / `receive_exact`: from the payload binder of the enclosing `let`;
- `select`: from the checked branch payload expression; and
- `offer`: from the handler payload binder.

This does not introduce unrestricted copies of linear payloads.  Resource
consumption remains governed by the existing Core context transition; only the
successor endpoint's logical continuation type is instantiated.

## Permanent replay

`test/Phase1AuditSessionContinuationBindingMain.hs` preserves the 26-case audit
corpus:

- S01-S08: send occurrence binding and controls;
- R01-R06: receive occurrence binding and controls;
- B01-B04: select payload binding and controls;
- O01-O04: offer payload binding and controls; and
- C01-C04: lower-level endpoint helper/resource controls.

The regression cases require both directions of the repair: stale ambient names
must no longer make an invalid program pass, and legitimate aliasing of a formal
message binder to the concrete source binder must no longer make a valid program
fail.

The dedicated workflow also replays existing Surface, value, and refinement
conformance suites.

## Assurance boundary

This closes the public Surface session-message continuation-instantiation gap for
ordinary `send`, `receive`, `receive_exact`, `select`, and `offer` transitions.

It deliberately does **not** claim closure of recognition-backed
`receive_frame` / `commit_receive` continuation binding.  `PendingRecv` carries a
separate recognition/provenance boundary and remains an integration follow-up,
as recorded by the audit report.  This remediation also does not replace the
existing definedness/provenance obligations for logical terms, change the
linear-resource model, or make claims about native lowering beyond the existing
Phase 1 assurance boundary.
