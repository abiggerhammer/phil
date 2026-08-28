# Phase 1 protocol projection proof

This note records the Rocq certification target for `PHIL-PROT-PROJ-001`, covering the already implemented/tested PROT-003 and PROT-004 slices.

## Composition boundary

The proof deliberately reuses existing certified semantics rather than duplicating them:

- `PHIL-PROT-ID-001` supplies exact protocol-instance / role / local-session identity and action gating;
- `PHIL-SESSION-DUAL-001` supplies binary session duality and involution;
- `PHIL-GEN-INST-001` supplies accepted generic-instantiation authority.

The generic-instantiation witness is therefore opaque in `ProtocolProjection.v`: the theorem proves the protocol-specific consequences once ordinary generic requirements have already been accepted.

## Exact binary projection

A normalized `BinaryProtocolInstance` retains:

- the accepted generic-instantiation witness;
- exact `ProtocolInstanceRevision`;
- exact distinct primary and peer roles;
- the exact primary local session; and
- the peer session, required to be exactly `dualSession primary`.

`ProjectProtocolRole` admits only those two exact role/session pairs. The proof establishes that:

- exact instantiation preserves the imported generic witness and exact protocol revision;
- the primary role projects exactly the instantiated primary session;
- the peer role projects exactly its dependent dual;
- the two role sessions are dual in both directions;
- an undeclared role cannot project;
- role projection is session-unique for a well-formed binary instance;
- accepted projection evidence is tied to the exact protocol instance; and
- projection evidence from another instance rejects even when local session syntax happens to be equal.

## Session-polymorphic endpoints

The proof reuses the `ProtocolEndpointOccurrence` / `ProtocolEndpointContract` model certified by `PHIL-PROT-ID-001`.

A normalized `transferProtocolEndpoint` changes only the local occurrence name. It therefore preserves exact protocol instance, role, and local session without inspecting the session shape. In particular, `SessionVar S` remains exactly `SessionVar S` after transfer.

For communication authority, the proof distinguishes possession of an abstract session from exposure of a concrete communication head. `SessionVar S` has no `ConcreteCommunicationHead`, so the bare generic endpoint cannot perform a communication action merely because `S : Session`.

A later checked specialization is represented by `AcceptedSessionConstraint abstract concrete`. Communication after abstraction requires such an explicit accepted constraint plus a concrete communication head and the ordinary local-action premise. The exact protocol instance and role still must match; specialization cannot retarget endpoint identity.

This mirrors the executable PROT-003 behavior: `Phil.Core.Session.exposeSessionHead` rejects an unbound `SessionVar`, while `transferProtocolEndpoint` remains shape-parametric.

## Dedicated correspondence gate

`Phase 1 Protocol Projection Proofs` recompiles:

- `Syntax.v`;
- `Session.v`;
- the newly certified `ProtocolIdentity.v`; and
- `ProtocolProjection.v`

under Rocq 9.2.0, then reruns the unchanged executable pressure corpus:

- 6 PROT-003 generic-endpoint cases; and
- 9 PROT-004 family projection / duality cases.

The production modules are typechecked under `-Wall -Werror` but are not modified by this tranche.

## Residual correspondence boundary

Certification does **not** yet establish Haskell implementation equivalence. The following remain explicit later refinement boundaries:

- concrete `Text`, `Map`, and `Session` representation;
- `ProtocolSessionTemplate` substitution and `ProtocolMessageArgument` type/semantic-form correspondence;
- canonical derivation of `ProtocolInstanceRevision` from `GenericApplicationIdentity`;
- the concrete implementation of accepted session constraints / exposed session heads;
- resource-context movement/linearity correspondence beyond the normalized contract-preservation theorem; and
- Rocq extraction/toolchain and Haskell runtime correctness.

Those boundaries are not upgraded by the conformance corpus alone.
