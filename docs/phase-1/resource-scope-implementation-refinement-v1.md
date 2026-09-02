# Resource Scope implementation refinement v1

`PHIL-RES-SCOPE-001` is already Certified by `proof/Phil/Core/ResourceScope.v` and composes the Certified Resource Join theorem rather than rebuilding exact continuing-owner/subject conservation.

This staging slice adds only the representation-neutral executable decisions corresponding to the additional scope theorem family:

- scoped-boundary admission: the Resource Join predecessor is accepted and every lexical loan is closed before the continuing edge;
- affine-state admission: every declared affine slot has an explicit post-state carrier, including explicit `AffineAbsent` rather than hidden maybe-possession; and
- branch-disposition admission: terminal arms contribute no continuing projection and continuing arms contribute exactly their declared projection.

Branch-local live-linear non-omission is not duplicated as a second classifier: it follows from the Resource Join predecessor exactly as `live_branch_local_linear_owner_cannot_disappear` does in the Certified proof. The production Resource Join predecessor is now machine-bound by #567/#568.

## Explicit correspondence boundaries

The extracted kernel receives normalized Boolean facts. Concrete `Map`/`Set` representation, CFG edge recognition, `BorrowedSlice` classification, source lexical-scope elaboration, terminal-block recognition, affine carrier representation, exact diagnostics, and Rocq/GHC correctness remain explicit boundaries until the later production-binding closeout.

The staging PR does not change production Haskell. It fresh-extracts `ResourceScopeKernel.hs`, runs eight direct controls covering every accepted/failure class, and reruns the unchanged RES-005 through RES-008 conformance corpus (two cases per matrix row).

A green staging merge leaves `PHIL-RES-SCOPE-001` at `Discharged / Certified`. Promotion to `Implementation Refined` requires a separate exact-kernel production-binding closeout.
