# PHIL-RES-JOIN-001 implementation refinement

This slice stages machine implementation refinement for the already-Certified
`PHIL-RES-JOIN-001` resource-join theorem.  It does not change production
Haskell behavior.

## Certified executable surface

`proof/Phil/Core/ResourceJoin.v` defines `ResourceProjectionSuccess` as exactly
three representation-neutral obligations:

1. every incoming linear owner is represented by exactly one post-state slot;
2. every post-state binding names an incoming owner; and
3. every bound owner satisfies the slot's semantic-subject requirement, either
   by exact continuity or by an already accepted explicit succession relation.

`proof/Phil/Core/ResourceJoinImplementation.v` exposes those three facts as one
small ordered decision:

- `ResourceProjectionAcceptedDecision`;
- `ResourceProjectionLinearCoverageDecision`;
- `ResourceProjectionInventedOwnerDecision`; or
- `ResourceProjectionSubjectAdmissionDecision`.

The implementation-correspondence theorem proves that, given Boolean reflection
for the three exact facts, kernel acceptance is equivalent to
`ResourceProjectionSuccess`.

## Deliberate composition boundaries

This kernel does **not** duplicate adjacent Certified or already-bound logic.
In particular:

- Core `ContextJoin` / `ProcessJoin` continuing-path conservation remains an
  explicit Certified predecessor supplied by `ResourceJoin.v`;
- concrete Systems CFG-edge and state-slot shape validation remains in
  `Phil.Systems.ControlStateProjection`;
- concrete key, `Map`, `Set`, value-role, mode, and diagnostic representation
  remains native Haskell correspondence;
- exact fixed-subject continuity is checked by the existing Systems subject
  index;
- explicit semantic succession (including the bounded protocol endpoint
  succession relation) remains the adjacent compositional predecessor checked
  by `Phil.Systems.ProtocolStateCorrespondence`, rather than being invented by
  `checkStateProjection`;
- the previously production-bound `SystemsControlPreservationKernel` continues
  to own the broader SYS-008 projection/capture decision surface.

A later production-binding closeout must therefore compose the exact extracted
RES-JOIN kernel at a point where the native projection facts and any required
accepted succession relation have both been established.  It must not weaken
that theorem to exact-subject equality only, nor fake a succession Boolean.

## Staging gate

The existing `Phase 1 Resource Join Proofs` workflow is extended to:

- recompile `ContextJoin.v`, `ProcessJoin.v`, and the Certified `ResourceJoin.v`;
- compile the implementation-correspondence theorem under Rocq 9.2.0;
- fresh-extract `ResourceJoinKernel.hs` with Rocq `bool` mapped directly to
  `Prelude.Bool`;
- strict-typecheck and execute four direct kernel controls; and
- rerun the unchanged correspondence corpus used by the original certification:
  Core Context, Process join, SYS-004 subject correspondence, SYS-008 control
  state projection, and SYS-009 protocol state correspondence.

The existing proof certificate is still emitted.  Production remains unchanged,
so `PHIL-RES-JOIN-001` stays `Discharged / Certified` until a later exact-kernel
production-binding closeout is fully green and merged.

Staging baseline: `ce0485573f4409122a8c7e8cb8d34a56de9f1185`.
