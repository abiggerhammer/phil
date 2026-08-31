# Phase 1 protocol projection implementation refinement

Obligation: `PHIL-PROT-PROJ-001`

This staging slice extracts the representation-neutral protocol-projection decisions already Certified by `proof/Phil/Core/ProtocolProjection.v`. It does not change production behavior.

## Extracted semantic surface

The extracted kernel owns only the protocol-specific choices that production can reflect from concrete facts:

- a protocol role projects only when the native role lookup says that role is declared;
- projection evidence is accepted only for the exact protocol-instance revision;
- projection evidence is accepted only for the exact selected local `Session`;
- accepted projection construction preserves exact instance, role, and local-session coordinates; and
- generic endpoint transfer preserves the exact same instance, role, and local-session contract while changing only the local occurrence name.

The decisions are deliberately atomic. Native `Map` lookup and Haskell equality remain responsible for producing the Boolean facts. This lets production keep the current detailed diagnostics for unknown roles, cross-instance evidence, and fabricated sessions without duplicating concrete representation in Rocq.

## What remains outside this kernel

The following remain native or predecessor boundaries:

- generic static-argument normalization and duplicate/missing-argument checks;
- `BoundaryMessageContract` admission;
- generic requirement discharge and application-identity derivation;
- protocol-template substitution;
- derivation of the peer session by `dualSession`;
- concrete `Text`, `Map`, `Set`, `Ty`, `SemanticForm`, and `Session` equality/traversal;
- resource-context consumption/insertion during endpoint transfer;
- predecessor/successor occurrence freshness and map integrity;
- the Session checker that rejects communication from a bare `SessionVar`;
- truth/competence of an accepted explicit session constraint;
- diagnostics, serialization, ABI/wire behavior, and GHC/Rocq/runtime correctness.

The Certified proof already composes `PHIL-PROT-ID-001`, `PHIL-SESSION-DUAL-001`, and `PHIL-GEN-INST-001`; this refinement does not reopen those boundaries.

## Staging verification

The Phase 1 Protocol Projection workflow is extended to:

1. recompile the Certified theorem and the implementation-correspondence theorem;
2. fresh-extract `ProtocolProjectionKernel.hs`;
3. strict-typecheck and execute direct controls for all extracted decisions/plans;
4. strict-typecheck the unchanged production projection/transfer paths; and
5. rerun the unchanged PROT-003 and PROT-004 pressure corpora.

Production `src/Phil/Core/Protocol/Family.hs` and `src/Phil/Core/Protocol/Generic.hs` remain unchanged in this staging PR. A green staging merge therefore leaves `PHIL-PROT-PROJ-001` at `Discharged / Certified`; promotion to `Implementation Refined` requires a separate exact-kernel production-binding closeout.
