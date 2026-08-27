# Phase 1 protocol identity separation conformance

This note records the executable `PROT-002` rule that local session shape is not protocol identity.

The governing rule from ADR-016 is:

> Local session equality does not imply protocol-instance identity.

A live endpoint is indexed by an exact protocol instance, role, and local session state. Two protocol instances may project to definitionally equal local `Session` syntax without becoming interchangeable.

## Endpoint contracts and occurrences

`Phil.Core.Protocol` distinguishes a live endpoint occurrence from its exact endpoint contract.

A `ProtocolEndpointBinding` carries:

- a branch/local occurrence name;
- exact `ProtocolInstanceRevision`;
- exact `ProtocolRoleKey`; and
- exact local `Session` state.

A `ProtocolEndpointContract` deliberately excludes the occurrence name and retains the other three identity-bearing components.

This permits branch-local endpoint occurrences with different names to inhabit the same post-join contract when their exact instance, role, and session all agree. It does **not** permit endpoints from distinct protocol instances to substitute or join merely because their local session syntax is equal.

## Checked relations

`checkProtocolEndpointSubstitution expected actual` accepts only when the exact endpoint contracts agree.

`checkProtocolEndpointJoin alternatives` accepts only when every branch-local endpoint occurrence has the same exact endpoint contract. The occurrence names may differ; protocol instance, role, and local state may not.

These checks complement `checkProtocolAction` from PROT-001. PROT-001 gates a communication action by exact instance, role, and current state. PROT-002 prevents earlier substitution or join reasoning from erasing those distinctions before an action is checked.

## Dedicated corpus

`test/Phase1ProtocolIdentitySeparationMain.hs` checks seven cases:

1. two distinct protocol instances may have definitionally equal local session syntax without equal endpoint contracts;
2. exact endpoint-contract substitution accepts across distinct occurrence names;
3. equal local session syntax does not permit cross-instance substitution;
4. equal local session syntax does not permit cross-instance join;
5. branch-local occurrences with the same exact contract do join;
6. equal local session syntax does not erase role identity; and
7. even with the same instance and role, substitution still requires the exact local session state.

## Scope

This closes `PROT-002` only. It does not implement protocol-family instantiation or projection evidence (`PROT-004`), unconstrained generic endpoint restrictions (`PROT-003`), stale endpoint rejection (`PROT-005`), or guarded-transition evidence (`PROT-006`). Target/runtime representation non-collapse remains covered separately by `PROT-007` / SYS-009.
