# Phase 1 protocol family projection conformance

This note records the executable `PROT-004` rule for binary protocol-family instantiation, exact role projection, and duality.

The governing ADR-016 distinctions are:

```text
ProtocolFamily
    + exact static parameters
        -> ProtocolInstance
            -- project(role) --> LocalSession
```

and projection is an assurance-producing relation tied to the exact protocol instance and role.

## Reuse of generic instantiation

`Phil.Core.Protocol.Family` does not introduce a second parameter-discharge mechanism.

A `BinaryProtocolFamily` carries the same stable `DeclarationKey` + `InterfaceRevision` identity pair used by ordinary generic applications, plus its published `GenericRequirement`s. `instantiateBinaryProtocol` runs `checkGenericInstantiation` and derives a `GenericApplicationIdentity` from the exact semantic arguments.

The resulting `ProtocolInstanceRevision` is canonically derived from that generic application identity. Therefore changing an identity-bearing static argument changes the exact protocol instance even when the role-local session syntax is unchanged.

## Bounded parameterized session templates

The initial binary family representation permits message positions in a local session template to be either concrete Phil Core types or exact `GenericStaticParameterKey` references.

`ProtocolMessageArgument` therefore carries two already-checked views of one static actual:

- the exact `Ty` substituted into the session template; and
- the `SemanticForm` used by generic application identity.

PROT-004 treats their correspondence and boundary-message admissibility as inputs from the ordinary generic/boundary requirement layer. It does not declare arbitrary in-memory values communicable merely because they can be placed in a `ProtocolMessageArgument` fixture.

Identity-bearing generic arguments that do not occur in the local session template are allowed. This is intentional: protocol identity may depend on exact static requirements or indices even when two projections are definitionally equal.

## Exact projection and duality

A binary family declares two distinct role keys and one primary local session template.

Instantiation:

1. discharges the family requirements through `checkGenericInstantiation`;
2. derives the exact generic application identity;
3. substitutes the exact static message arguments into the primary local session;
4. derives the peer local session with `Phil.Core.Session.dualSession`; and
5. records both role-local sessions under one exact `ProtocolInstanceRevision`.

Because the peer is derived rather than independently supplied, an accepted binary instance cannot smuggle in a non-dual peer projection.

`projectProtocolRole` accepts only a role declared by that exact instance and returns `ProtocolProjectionEvidence(instance, role, session)`.

`verifyProtocolProjection` requires both:

- the exact same `ProtocolInstanceRevision`; and
- the exact session registered for that role.

A projection from another instance therefore rejects even when its local session is definitionally equal.

## Dedicated corpus

`test/Phase1ProtocolProjectionMain.hs` checks nine cases:

1. identity-bearing parameter changes produce distinct protocol instances despite equal local projections;
2. the primary role projects to the exact substituted local session;
3. the peer projection is the exact dependent dual;
4. an undeclared role rejects;
5. fabricated role-local session evidence rejects;
6. mixed-instance projection evidence rejects despite equal local session shape;
7. a missing message actual rejects;
8. family requirements cannot bypass ordinary generic instantiation; and
9. changing a message actual changes both the exact projected session and protocol-instance identity.

## Scope

This closes `PROT-004` only. `PROT-005` stale predecessor reuse and `PROT-006` guarded-transition evidence remain separate slices. The generalized projection/session-polymorphism Rocq proof remains a proof-side obligation in `PHIL-PROT-PROJ-001`.
