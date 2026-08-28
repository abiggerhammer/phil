# Phase 1 resource loop proof v1

`PHIL-RES-LOOP-001` certifies the generalized loop-state and explicit propositional-transport semantics corresponding to the implemented/tested RES-009 and RES-010 slices.

## Composition boundary

This theorem reuses the already Certified `PHIL-RES-JOIN-001` relation `ResourceProjectionSuccess`. Loop initial entry and loop backedges therefore do **not** get a second ownership/subject-conservation rule: both are ordinary checked state projections into one declared `LoopStateTelescope`.

For every accepted loop projection the proof requires:

- `ResourceProjectionSuccess` for the exact incoming restricted-owner projection;
- the exact declared loop slot domain, with no omitted declared slot and no synthesized undeclared slot;
- the exact declared per-slot subject requirement; and
- fixed-subject justification through exact continuity or the already accepted succession relation supplied to `PHIL-RES-JOIN-001`.

The initial entry and every accepted backedge are proved to use that same telescope.

## Propositional transport

The proof separates definitional equality from explicit non-definitional transport.

`CheckedStateTransport source target` is admitted only when either:

1. `source = target` definitionally, or
2. explicit `AcceptedEqualityEvidence source target` is supplied.

The theorem proves that a non-definitional index change necessarily exposes the explicit equality-evidence premise, and that a non-definitional rewrite with no such evidence rejects.

This matches the RES-010 implementation pressure: `VTransport` consumes the source linear binding through Core's checked transport path before the resulting transported Systems value can satisfy the target state projection. The concrete `Ty`/`RefTerm`/proof-binding representation and the Core-to-Systems subject mapping remain correspondence boundaries rather than assumptions hidden inside this normalized proof.

## Invariants are separate

RES-013 is intentionally **not** part of this certification. A structurally valid loop entry/backedge does not establish an arbitrary logical invariant. `PHIL-RES-INVARIANT-001` separately owns the claim that every relevant predecessor/backedge establishes an explicitly declared nontrivial invariant with appropriate evidence.

The production `Phil.Systems.ControlStateInvariant` checker and `Phase1JoinLoopInvariantMain.hs` were inspected to preserve this boundary, but they are not counted as evidence for `PHIL-RES-LOOP-001`.

## Correspondence pressure

The dedicated workflow reruns the unchanged implementation corpus:

- RES-009: `test/Phase1LoopStateProjectionMain.hs` — 2 cases;
- RES-010: `test/Phase1PropositionalStateTransportMain.hs` — 2 cases.

It also typechecks the unchanged state-projection and Core value/transport implementation paths under `-Wall -Werror`.

## Residual boundary

This is semantic certification, not implementation refinement. The following remain explicit later correspondence/refinement boundaries:

- concrete `Map`/`Set` state-boundary representation;
- CFG initial-entry/backedge recognition and edge-label validation;
- source `LoopContract` elaboration into Systems state slots;
- concrete Core `VTransport` representation and its source-to-Systems owner/subject correspondence;
- truth/competence of equality evidence supplied to checked transport;
- exact diagnostics and Haskell implementation equivalence; and
- termination/totality. Phase 1 establishes partial correctness only.
