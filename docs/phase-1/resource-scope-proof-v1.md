# Phase 1 resource scope proof v1

This note records the Rocq certification target for `PHIL-RES-SCOPE-001`, covering the already implemented/tested RES-005 through RES-008 resource-scope conformance slices.

The proof composes Certified `PHIL-RES-JOIN-001` rather than re-proving exact continuing-owner conservation. The additional normalized claims are:

- a branch-local linear owner that is still live on a continuing predecessor cannot disappear from the post-state;
- an owner already disposed before reconvergence is outside the live-linear coverage premise;
- affine branch asymmetry must be represented by an explicit post-state carrier, including an explicit `AffineAbsent` value when the branch has no owner;
- omission of a declared affine slot is not interpreted as hidden maybe-possession;
- lexical scoped loans are closed before ordinary joins and loop backedges;
- terminal arms are outside the continuing-predecessor relation and therefore contribute no join projection.

## Composition boundary

`proof/Phil/Core/ResourceScope.v` imports `ResourceJoin.v`. Exact subject identity, linear owner coverage, no duplication, and succession evidence remain owned by `PHIL-RES-JOIN-001`. Surface lexical scope and process terminality are represented here only through the normalized scope/branch relations needed for this obligation; their concrete source/CFG correspondence remains explicit.

## Correspondence pressure

The dedicated workflow reruns the unchanged eight-case corpus:

- `test/Phase1BranchLocalLinearLeakMain.hs` — 2 RES-005 cases;
- `test/Phase1AffineBranchAsymmetryMain.hs` — 2 RES-006 cases;
- `test/Phase1ScopedLoanBoundaryMain.hs` — 2 RES-007 cases;
- `test/Phase1TerminalArmExclusionMain.hs` — 2 RES-008 cases.

It also rebuilds the existing Haskell certifier with `-Werror`; production behavior is unchanged.

## Residual boundary

This is semantic certification, not implementation refinement. Concrete `Map`/`Set` representation, CFG-edge recognition, `BorrowedSlice`/loan classification, source lexical-scope elaboration, terminal-block recognition, affine carrier representation, diagnostic ordering, and Haskell implementation equivalence remain later correspondence/refinement boundaries. Phase 1 certifies lexical loans only; future explicit lifetime relations may widen the admitted model.
