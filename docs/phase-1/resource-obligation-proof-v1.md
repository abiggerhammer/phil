# PHIL-RES-OBL-001 — obligation non-laundering proof

This proof certifies the semantic core of RES-011: control-flow reconvergence is not an obligation-disposition event.

## Composition boundary

`proof/Phil/Core/ProcessJoin.v` already certifies the decisive lower-layer property of `joinBranches`: successful normalization may replace the `ResourceContext` carried by a continuing path, but it preserves that path's opaque non-resource checker-state payload exactly.

The Phase 1 implementation stores `residualObligations` in that non-resource `CheckState` payload. `ResourceObligation.v` therefore models an observation

```
StatePayload -> ObligationId -> ObligationStatus
```

with five statuses:

- pending;
- discharged;
- runtime-bound;
- assumed through an already permitted boundary; and
- exported through an already permitted boundary.

The latter four are *recorded explicit dispositions*. Their semantic truth and competence remain owned by `PHIL-DISCH-BOUNDARY-001`, ADR-010, and the corresponding evidence/policy machinery. This theorem does not attempt to re-prove them.

## Certified claims

For every original continuing path of a successful process join:

1. the exact obligation status in its non-resource payload is unchanged by reconvergence;
2. a pending obligation therefore remains represented as pending on the normalized continuing path;
3. reconvergence cannot silently fabricate discharge, runtime binding, assumption, or export of a pending obligation; and
4. the same pending obligation survives a second reconvergence, covering the repeated/loop-like case exercised by RES-011.

This is stronger than a special case about one obligation map key: the join cannot alter *any* obligation-status observation over the preserved payload.

## Correspondence gate

The dedicated workflow reruns the unchanged `test/Phase1ObligationReconvergenceMain.hs` corpus under `-Wall -Werror`:

- branch-specific pending obligation survives first reconvergence;
- the carried obligation survives repeated reconvergence.

It also typechecks the unchanged test/implementation path and records exact Rocq source and `.vo` identities.

## Residual boundary

This is semantic certification, not implementation refinement. The following remain explicit trust/correspondence boundaries:

- the concrete Haskell `Map ObligationId Obligation` representation;
- correspondence between `residualObligations` and the normalized proof-side status observation;
- exact identity/serialization of concrete `ObligationId` values;
- correctness and semantic truth of explicit discharge/runtime/assumption/export events;
- diagnostics and ordering;
- GHC/runtime behavior and Haskell implementation equivalence; and
- Rocq kernel/toolchain correctness.

Reconvergence itself is certified only as a non-laundering operation: if no separate competent disposition occurred, a pending obligation remains pending and represented in the post-state.
