# Phase 1 protocol stale-endpoint conformance

This note records the executable `PROT-005` rule that a successful protocol transition consumes the predecessor endpoint occurrence and leaves only its exact successor live.

The governing ADR-016 rule is:

> `Endpoint[P,R,S] -- legal action at S --> Endpoint[P,R,S']`
>
> The old endpoint cannot be used again.

## Existing mechanism

`Phil.Core.Protocol.checkProtocolAction` already delegates temporal progression to the Phase 0 `Phil.Core.Session` checker. A successful non-terminal action:

1. consumes the predecessor linear `TyEndpoint` resource;
2. removes the predecessor `ProtocolEndpointBinding` metadata;
3. creates exactly one successor linear endpoint under a distinct occurrence name;
4. preserves the exact protocol instance and role; and
5. records the declared successor `Session`.

A terminal close consumes the endpoint without fabricating a successor.

`Phil.Core.Session.continueWith` also rejects a transition whose successor reuses the predecessor occurrence name. This keeps predecessor and successor occurrences distinct even when their session shapes are structurally similar.

## Stale reuse

After a transition, a request naming the consumed predecessor is rejected before any new session action is considered because that endpoint occurrence is no longer present in the live protocol context.

The successor's session may have the same top-level communication constructor as the predecessor. That similarity does not revive or alias the consumed occurrence. Liveness follows the exact linear occurrence produced by the transition, not session-shape equality.

## Dedicated corpus

`test/Phase1ProtocolStaleEndpointMain.hs` checks seven cases:

1. a successful action removes predecessor protocol metadata;
2. it also removes the predecessor linear resource;
3. a later action on the stale predecessor rejects exactly;
4. the exact successor remains usable and preserves instance/role provenance;
5. a structurally similar successor state does not revive the predecessor;
6. a successor may not reuse the predecessor occurrence name; and
7. terminal close consumes the endpoint and a repeated stale close rejects.

## Scope

This closes `PROT-005` only. It introduces no new progression mechanism: it promotes the existing Core protocol/session linearity behavior into a dedicated Phase 1 conformance gate. `PROT-006` remains the separate guarded-transition evidence slice.
