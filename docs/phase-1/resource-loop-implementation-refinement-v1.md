# Resource Loop implementation refinement v1

`PHIL-RES-LOOP-001` is already Certified by `proof/Phil/Core/ResourceLoop.v`. Its machine-refinement surface deliberately composes the already machine-bound Resource Join predecessor rather than duplicating owner/subject conservation.

This staging slice extracts two representation-neutral decision surfaces.

## Loop projection admission

`decideLoopProjectionByFacts` accepts only when:

1. the concrete projection has the expected loop role (initial entry or backedge);
2. the already-Certified Resource Join projection relation accepts;
3. the projection uses exactly the declared loop-state slot domain; and
4. every declared loop-state slot uses exactly the declared requirement.

Its failure classes preserve that order: projection kind, Resource Join predecessor, telescope slot domain, telescope requirements.

## Explicit state transport

`decideStateTransportByFacts` implements exactly the Certified `CheckedStateTransport` disjunction:

- definitional equality admits transport without extra evidence; or
- a non-definitional change requires accepted explicit equality evidence.

This classifier does not claim that an explicit `VTransport` syntax node is required for definitionally equal types; production Core currently rejects redundant `VTransport` with `TransportNotRequired`. The Certified surface is the semantic admission relation: definitional equality needs no witness, while non-definitional equality requires explicit accepted evidence.

## Direct controls and unchanged corpus

The staging workflow fresh-extracts `ResourceLoopKernel.hs`, strict-typechecks it, and runs eight direct controls:

- loop projection: accept / wrong kind / Resource Join failure / slot-domain mismatch / requirement mismatch;
- state transport: definitional accept / explicit-evidence accept / missing-evidence reject.

It also reruns the unchanged four-case RES-009/010 correspondence corpus:

- `test/Phase1LoopStateProjectionMain.hs` — 2 cases;
- `test/Phase1PropositionalStateTransportMain.hs` — 2 cases.

## Explicit boundaries

Concrete `Map`/`Set` representation, CFG initial-entry/backedge recognition, source `LoopContract` elaboration, concrete Core `VTransport` representation, equality-evidence production/truth, Core-to-Systems owner/subject correspondence, exact diagnostics, Rocq/GHC correctness, and termination/totality remain explicit boundaries. `PHIL-RES-INVARIANT-001` continues to own logical invariant establishment.

A green staging merge leaves `PHIL-RES-LOOP-001` at `Discharged / Certified`; a separate exact-kernel production-binding closeout is required for `Implementation Refined`.
