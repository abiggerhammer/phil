# PHIL-RES-JOIN-001 production binding

This closeout binds the already-Certified `PHIL-RES-JOIN-001` Resource Join projection relation to the exact Rocq-extracted `ResourceJoinKernel` staged by PR #567.

## Exact staged kernel

- staging PR: #567
- staging exact green head: `956291c18d8c0dedc7ef7bfb0df23efd36507ff4`
- staging merge: `bf619adcecfefca69eb9be9793eae7706b20f4b9`
- exact `ResourceJoinKernel.hs` SHA-256: `788a8cdf3d6ba199880b54a636002ca039c790980e43f6c44260774271d86af6`

`generated/ResourceJoinKernel.hs` and `src/ResourceJoinKernel.hs` preserve the exact staged extraction bytes.

## Production ownership

`Phil.Systems.ControlStateProjection.checkStateProjection` retains the existing concrete validation and typed diagnostics for CFG edges, slot domains, concrete values, modes, scoped loans, fixed subjects, duplicate restricted owners, and live-linear coverage.

After those native checks succeed, production independently projects the exact linear-owner slice and reflects three facts into the extracted kernel:

1. every incoming linear owner occurs in exactly one post-state binding;
2. every slot declared `Linear` is bound to an owner that is actually incoming as `Linear`; and
3. every bound linear owner satisfies its slot subject requirement under the concrete Stage-1 subject index.

The final production success path requires `ResourceProjectionAcceptedDecision`. Any impossible disagreement between the detailed native checks and the certified normalized classifier fails closed through the existing certified-kernel invariant path.

The current concrete state-projection layer implements fixed-subject admission by exact subject continuity. `ResourceJoin.v` also admits an explicit accepted succession relation; protocol endpoint succession remains the separately checked adjacent `ProtocolStateCorrespondence` layer rather than being invented inside state projection. This closeout therefore mechanically binds the concrete linear projection as a sound refinement of the Certified relation while retaining explicit succession as a named predecessor/cross-layer boundary.

## Preserved boundaries

The following remain explicit implementation or TCB boundaries:

- concrete `Text`, `Map`, `Set`, key, value, CFG, and role representations;
- construction of the source-subject index and source-to-Systems subject correspondence;
- concrete protocol succession construction and checking;
- affine and unrestricted state, which are outside the `ResourceProjectionSuccess` incoming-linear theorem surface;
- diagnostic payload construction and ordering;
- Rocq extraction/toolchain correctness and GHC/runtime correctness.

## Closeout gate

The dedicated production-binding workflow:

- recompiles the Certified Core join predecessors, `ResourceJoin.v`, and its implementation correspondence under Rocq 9.2.0;
- fresh-extracts `ResourceJoinKernel.hs`, requires SHA-256 `788a8cdf3d6ba199880b54a636002ca039c790980e43f6c44260774271d86af6`, and byte-compares both checked-in copies;
- builds the package and tests with warnings as errors, ensuring the production kernel is registered in `phil-core.cabal`;
- strict-typechecks the bound `ControlStateProjection` module;
- executes all four direct kernel controls through `src/`; and
- reruns the unchanged original RES-001–004 correspondence stack: Core Context (28 cases), Process join (12), SYS-004 subject correspondence (8), SYS-008 control-state projection (11), and SYS-009 protocol-state correspondence (13), 72 cases total.

A fully green exact head permits promotion of `PHIL-RES-JOIN-001` to `Discharged / Implementation Refined`.
