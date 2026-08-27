# Phase 1 generic endpoint conformance

This note records the executable `PROT-003` rule for session-polymorphic endpoints.

ADR-016 permits generic code to quantify over an abstract local session state:

```text
S : Session
e : Endpoint[P,R,S]
```

Possessing such an endpoint does not reveal which communication transition, if any, is legal. Generic abstraction may preserve and transfer the endpoint, but it may not manufacture a communication action from the mere fact that `S` is a session.

## Abstract session representation

The existing Core `SessionVar` constructor represents an abstract session parameter directly. `SessionVar S` is intentionally not a communication head such as `Send`, `Receive`, `Select`, `Offer`, or `End`.

The Phase 0 session checker already treats an unexposed `SessionVar` as `UnboundSessionVariable`; PROT-003 reuses that fail-closed behavior rather than adding a generic channel escape hatch.

## Shape-parametric transfer

`Phil.Core.Protocol.Generic.transferProtocolEndpoint` moves one live endpoint occurrence from a predecessor name to a fresh successor name without inspecting the endpoint's session state.

The transfer:

- consumes the predecessor linear resource exactly once;
- removes predecessor protocol metadata;
- creates one successor linear resource;
- preserves exact protocol instance, role, and session contract; and
- works equally for concrete sessions and abstract `SessionVar` states.

This models the bounded Phase 1 operations ADR-016 permits for an unconstrained endpoint: move, return, ownership-preserving storage, or local delegation.

## Communication remains gated

All communication still goes through `Phil.Core.Protocol.checkProtocolAction` and the existing `Phil.Core.Session` checker.

For an endpoint whose current session is `SessionVar S`, send, receive, select, offer, and close all reject before any transition can occur because no concrete session head has been established.

A caller that later provides a stronger checked constraint exposing a concrete session form may use the ordinary protocol action checker; PROT-003 itself does not invent that constraint.

## Dedicated corpus

`test/Phase1ProtocolGenericEndpointMain.hs` checks six cases:

1. an abstract endpoint transfers without exposing session shape;
2. transfer consumes the predecessor occurrence and preserves the exact endpoint contract;
3. every communication action rejects on unconstrained `SessionVar S`;
4. transfer does not over-restrict an endpoint whose session is concrete;
5. transfer rejects a destination occurrence collision; and
6. transfer rejects an unknown predecessor occurrence.

## Scope

This closes `PROT-003` only. Protocol family instantiation/projection and duality remain `PROT-004`; stale predecessor reuse is `PROT-005`; guarded transition evidence is `PROT-006`.
