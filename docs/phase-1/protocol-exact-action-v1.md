# Phase 1 exact protocol action conformance

This note records the executable `PROT-001` boundary for first-class protocol endpoints.

The governing rule is:

> A session action is legal only for the exact protocol instance, exact role, and current local session state that admit it.

ADR-016 distinguishes reusable protocol/session specification from possession of one live endpoint capability. Phase 0 already checks local session progression through `Phil.Core.Session`; Phase 1 must additionally retain enough provenance to prevent an endpoint from being exercised under the wrong protocol instance or role.

## Phase 1 Core bridge

`Phil.Core.Protocol` introduces a checked companion context around the existing Phase 0 resource/session machinery.

A live `ProtocolEndpointBinding` carries:

- the unique endpoint occurrence name used by the resource context;
- an exact `ProtocolInstanceRevision`;
- an exact `ProtocolRoleKey`; and
- the current role-local `Session`.

The ordinary `ResourceContext` simultaneously contains the linear `TyEndpoint` for that same session. Before communication, the protocol checker requires the metadata and resource state to agree exactly.

A `ProtocolActionRequest` names the exact protocol instance and role under which the operation is being checked. `checkProtocolAction` first rejects instance or role mismatch, then delegates the temporal/state-shape check to the existing session checker. Successful progression consumes the predecessor endpoint and, where applicable, installs a successor carrying the same protocol instance and role with the exact successor session returned by the session calculus.

This deliberately does not infer protocol identity from local session syntax, transport representation, or human names.

## Dedicated corpus

`test/Phase1ProtocolExactActionMain.hs` checks eight cases:

1. an exact send under the correct instance, role, and send state is accepted and preserves provenance on the successor;
2. the same local session action under a different protocol instance is rejected before transition;
3. the same action under a different role is rejected before transition;
4. a receive attempted at a send state is rejected by the current local session state;
5. protocol metadata and the live linear `TyEndpoint` state may not drift apart;
6. an exact labeled selection preserves instance/role provenance and installs the exact branch continuation;
7. a label absent from the current local state is rejected; and
8. exact terminal close consumes the live endpoint without fabricating a successor.

The CI gate runs this corpus with `-Wall -Werror` so the new Core module is compiled under the same warning discipline even though the initial slice is exercised as a dedicated conformance program.

## Scope

This closes `PROT-001` only.

It does not yet claim:

- that definitionally equal local sessions from distinct protocol instances cannot be substituted or joined (`PROT-002`);
- generic communication over an unconstrained session parameter (`PROT-003`);
- protocol-family projection/duality (`PROT-004`);
- the dedicated stale-predecessor corpus (`PROT-005`); or
- guarded-transition evidence rules (`PROT-006`).

Those cases build on the exact endpoint provenance introduced here. SYS-009 already covers the downstream requirement that lowering preserve protocol instance, role, and state through explicit correspondence rather than transport coincidence.
