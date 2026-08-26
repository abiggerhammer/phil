# Phase 1 Systems protocol-state correspondence v1

Status: bounded executable conformance slice for `SYS-009`.

## Governing rule

A concrete transport path does not define Phil protocol state.

Systems lowering must retain an explicit correspondence between a target communication site and the exact source protocol facts that authorize it:

- exact protocol-instance identity;
- exact endpoint role;
- exact local-session state;
- exact live endpoint occurrence; and
- exact consuming transition and successor/terminal outcomes.

The target transport handle is only realization data. Equal socket, pointer, runtime-handle, queue, or device identity is never protocol-instance or endpoint identity.

## Endpoint occurrence model

`ProtocolEndpointState` records four independent semantic coordinates:

```text
EndpointOccurrenceKey
ProtocolInstanceRevision
ProtocolRoleKey
LocalSessionRevision
```

This is the bounded Systems-side form of ADR-016's `Endpoint[P,R,S]` distinction. The occurrence key matters independently of `P`, `R`, and `S`: a successful transition consumes one live occurrence and produces a distinct successor occurrence.

A successor may have a structurally or even textually equal local session revision when recursion requires it. That does not permit predecessor reuse. Likewise, equal local-session text under a different protocol instance or role is rejected.

This slice intentionally uses opaque stable revision keys. It does not claim to implement the full Phase-1 `ProtocolFamily -> ProtocolInstance -> LocalSession` construction/projection machinery; it provides the exact identities that Systems lowering must preserve once those upstream objects exist.

## Transition bindings

Each `ProtocolTransitionBinding` records:

- one exact predecessor endpoint occurrence;
- one semantic `ProtocolAction`;
- one exact Systems operation or terminator site;
- one exact Systems transport value;
- explicit successor or terminal outcomes; and
- one correspondence basis.

The verifier requires:

- every predecessor occurrence to exist;
- every successor occurrence to exist and differ from the predecessor;
- successor protocol instance and role to match the predecessor exactly;
- one semantic transition per exact target site;
- at most one consuming transition for one live endpoint occurrence;
- at most one producer transition for one successor occurrence; and
- an acyclic endpoint-successor graph.

The final condition rejects endpoint resurrection through a longer cycle even when every local edge looks individually plausible.

Fatal or otherwise terminal source outcomes are represented by `ProtocolTerminal`; they create no successor endpoint.

## Typed protocol sites

Where the logical Systems IR already exposes protocol structure, SYS-009 checks it structurally.

The bounded v1 checker recognizes:

- `OpCommitIngress` as an exact receive/recognition commit;
- `OpSessionSelect` as an exact protocol select;
- `TermSessionOffer` as an exact protocol offer;
- `TermReceiveExact` as an exact protocol receive boundary; and
- `TermSendExact` as an exact protocol send boundary.

Those sites require `CheckedProtocolCorrespondence`. The action, transport, and target outcome domain must agree with the actual Systems construct.

For example, an exact receive has the concrete target outcome domain `{success, failure}`. Omitting one arm is not a valid protocol correspondence.

## Frozen Phase-0 opaque bridge

The generic Phase-1 StageContract stack currently wraps the frozen Phase-0 `phase0SystemsArtifact`. Some of that artifact predates the later semantic `OpSessionSelect` / `TermSessionOffer` normalization and still represents protocol actions as `OpRuntimeCall`.

SYS-009 does not infer semantics from those call names.

A legacy runtime call may participate only through:

```text
CheckedLegacyOpaqueProtocolBridge evidence-id
```

The bridge must be explicit and nonempty, and the exact physical call must consume the declared transport exactly once. A typed protocol construct rejects this opaque bridge; conversely, an opaque runtime call rejects an ordinary typed correspondence basis.

This keeps migration honest without silently replacing the frozen SYS-001--008 witness foundation.

`RuntimeTransportCoincidence` is represented only as an explicit rejected basis so the invalid inference is mechanically testable.

## Upload witness pressure

The real upload witness follows one successful server lineage through the frozen Systems artifact:

```text
endpoint.0  receive/commit Hello
    -> endpoint.1

endpoint.1  select version          [legacy checked bridge]
    -> endpoint.2

endpoint.2  receive/commit Begin
    -> endpoint.3

endpoint.3  select proceed          [legacy checked bridge]
    -> endpoint.4

endpoint.4  receive payload/cancel  [legacy checked bridge]
    payload -> endpoint.5
    cancel  -> terminal

endpoint.5  exact payload receive
    success -> endpoint.6
    failure -> terminal EarlyEOF
```

All seven endpoint occurrences use the same physical Systems value:

```text
UploadServer:server.transport
```

That is deliberate. SYS-009 must accept physical transport reuse while refusing to collapse semantic endpoint occurrences into one reusable capability.

The current witness is a bounded success-lineage pressure case, not a claim that every branch of the entire upload protocol has already been reified into this new relation layer.

## Conformance corpus

The dedicated corpus requires:

- acceptance of the upload endpoint lineage;
- acceptance of one physical transport realizing many distinct endpoint occurrences;
- rejection when an equal local session is substituted from another protocol instance;
- rejection of successor role drift;
- rejection when a predecessor occurrence is returned as its own successor;
- rejection when a consumed endpoint drives a second transition;
- rejection of a multi-step cyclic endpoint lineage;
- rejection of transport-handle coincidence as protocol correspondence;
- explicit legacy opaque-bridge requirements;
- typed correspondence requirements for typed protocol constructs;
- exact receive-commit message-state matching;
- exact success/failure coverage for exact receive; and
- deterministic protocol-stage identity under map ordering.

## Deferred

This slice does not yet implement:

- complete protocol-family declaration/instantiation/projection checking from ADR-016;
- protocol duality proof production;
- complete upload branch coverage in the new Phase-1 relation layer;
- `SYS-010` exact boundary owner/length and send commit-point semantics;
- evidence transfer across protocol communication (`SYS-011`);
- erasure/strengthening and assumption laundering;
- multi-site assurance carriers;
- staging/copy cost relations; or
- next-stage ABI/deployment requirements.

Those later relations must preserve the exact endpoint occurrence and protocol identity established here rather than recovering them from target representation.
