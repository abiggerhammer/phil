# Phase 1 protocol identity proof

## Status

Certified target for `PHIL-PROT-ID-001` over the implemented PROT-001, PROT-002, and PROT-007 semantic slice.

## Purpose

`Phil.Core.Protocol` already implements exact protocol-instance, role, and current-session gating, and the dedicated PROT-001/002 corpora establish the intended rejection pressure. SYS-009 separately demonstrates that target transport/runtime coincidence does not collapse protocol identity. The remaining ledger gap is a generalized proof authority connecting those executable rules to one representation-neutral semantic claim.

`proof/Phil/Core/ProtocolIdentity.v` supplies that claim.

## Normalized semantic model

The proof treats a live endpoint contract as exactly three semantic coordinates:

- `ProtocolInstanceRevision`;
- `ProtocolRoleKey`; and
- current local `Session`.

A live endpoint occurrence additionally has a local occurrence name. The occurrence name is deliberately excluded from contract identity, matching `ProtocolEndpointBinding` versus `ProtocolEndpointContract` in production.

`ContractMatches` requires equality of all three contract coordinates. Therefore:

- distinct occurrence names may inhabit the same exact contract;
- equal local session syntax never repairs a distinct protocol-instance identity;
- equal local session syntax never repairs a distinct role identity; and
- equal instance and role still do not permit substitution when local state differs.

`EndpointJoinCompatible` requires every continuing branch-local occurrence to be substitutable for the first exact contract, so a cross-instance occurrence cannot silently reconverge merely because its local session shape matches.

## Action gating

The proof deliberately does not duplicate the session calculus. `LocalActionAllowed` is an abstract premise supplied by the competent local-session layer; `PHIL-SESSION-STEP-001` remains responsible for the resource effect of an admitted transition.

`ProtocolActionAllowed` adds the protocol-specific gate around that premise. An action is admitted only when:

1. the requested protocol instance equals the live endpoint contract instance;
2. the requested role equals the live endpoint role; and
3. the current local session admits that exact action.

The proof establishes each requirement separately, proves wrong instance/role/current-state rejection, and proves the three exact premises sufficient for the normalized protocol action gate.

## Realization non-collapse

A normalized realized endpoint carries its semantic protocol contract plus independent transport and runtime-representation identities. `RuntimeCoincident` may hold even when semantic contracts differ.

The proof establishes that even simultaneous transport and runtime-representation coincidence cannot repair either a protocol-instance mismatch or a role mismatch. This is the semantic PROT-007 rule exercised concretely by SYS-009.

## Production correspondence pressure

The dedicated workflow leaves production unchanged and reruns the existing executable pressure:

- `test/Phase1ProtocolExactActionMain.hs` — 8 PROT-001 cases;
- `test/Phase1ProtocolIdentitySeparationMain.hs` — 7 PROT-002 cases; and
- `test/Phase1ProtocolStateCorrespondenceMain.hs` — 13 SYS-009 cases, including equal-session cross-instance rejection and transport-coincidence rejection.

The workflow also typechecks `Phil.Core.Protocol` and `Phil.Systems.ProtocolStateCorrespondence` under `-Wall -Werror`.

## Residual boundary

This certification is representation-neutral. It does not certify concrete `Text` equality/serialization for protocol-instance revisions, role keys, endpoint occurrence names, local-session representation, or Systems transport/runtime identifiers. `Map` representation, diagnostics, concrete source-to-endpoint provenance, and the Haskell implementation correspondence remain explicit boundaries until separately implementation-refined.

This theorem also does not claim protocol-family projection (`PHIL-PROT-PROJ-001`) or successor/stale/guarded progression (`PHIL-PROT-STEP-001`); those remain the next protocol proof obligations.
