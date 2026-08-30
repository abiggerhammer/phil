# PHIL-PROT-ID-001 implementation refinement staging

This staging slice adds a representation-neutral executable correspondence for the already-Certified protocol identity obligation without changing production.

## Certified semantic surface

`PHIL-PROT-ID-001` requires exact semantic separation of:

- protocol instance revision;
- protocol role;
- current local Session state; and
- current-local-state admission of a requested protocol action.

Occurrence names do not define endpoint contract identity. Equal transport identity or runtime representation does not repair an instance, role, or local-state mismatch.

## Extracted decision surface

`proof/Phil/Core/ProtocolIdentityImplementation.v` normalizes two production decisions:

1. endpoint contract correspondence, in exact precedence order:
   - protocol instance;
   - role;
   - local Session;
2. protocol action identity, in exact precedence order:
   - protocol instance;
   - role;
   - current-local-state action admission.

It also extracts exact three-coordinate contract construction through `planProtocolContract`.

The executable interface intentionally has no occurrence-name, transport-identity, or runtime-representation input.

## Native bridge boundary

This staging slice does not claim mechanical refinement of:

- concrete Haskell `Text`, `Name`, `Session`, `Map`, or equality implementations;
- endpoint-map lookup or map-key agreement;
- resource-context agreement;
- truth of current Session-action admission or Session-step execution;
- metadata advancement after an accepted Session step;
- transport/runtime identity or realization correctness;
- GHC, Rocq extraction, or runtime/toolchain correctness.

Those remain explicit native or predecessor boundaries.

## Staging verification

The Phase 1 Protocol Identity workflow recompiles the Certified theorem and implementation correspondence, fresh-extracts `ProtocolIdentityKernel.hs`, strict-typechecks and executes direct kernel controls, and reruns the unchanged PROT-001/PROT-002/SYS-009 pressure corpora.

Production `src/Phil/Core/Protocol.hs` remains unchanged. A green staging run therefore leaves `PHIL-PROT-ID-001` at `Discharged / Certified`; a separate exact-kernel production-binding closeout is required before promotion to `Implementation Refined`.
