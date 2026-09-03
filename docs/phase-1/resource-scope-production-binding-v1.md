# Phase 1 Resource Scope Production Binding v1

`PHIL-RES-SCOPE-001` is already Certified by `proof/Phil/Core/ResourceScope.v`. PR #571 staged the executable correspondence surface and fresh-extracted `ResourceScopeKernel.hs` without changing production behavior.

The staged exact kernel is identified by SHA-256:

`4dfd2f2d22a4a84de67b3c60d4ec18bc64eeaf1491982cd79e214d761a3ea965`

This closeout checks that exact file into `generated/ResourceScopeKernel.hs` and mirrors it byte-for-byte at `src/ResourceScopeKernel.hs`.

## Production ownership

The existing `Phil.Systems.ControlStateProjection` checker keeps ownership of concrete CFG lookup, state-slot domains, restricted modes, value-role classification, detailed loan diagnostics, fixed-subject lookup, duplicate-owner diagnostics, and live-linear coverage. The previously bound `ResourceJoinKernel` remains the predecessor gate for exact continuing linear conservation.

After those native checks succeed, Resource Scope admission is independently reflected into the extracted kernel at the facts' actual ownership points:

- `decideScopedBoundaryByFacts` runs only after the concrete Resource Join gate has accepted. Its Resource Join predecessor fact is therefore supplied by an actual machine-bound predecessor, while lexical-loan closure is recomputed from every incoming/bound concrete Systems value and rejects any `BorrowedSlice` residue.
- `decideAffineProjectionByFact` independently checks that every concrete affine state slot has an explicit binding. Exact state-slot-domain checking remains the native representation layer; the extracted classifier owns the normalized no-hidden-maybe admission bit.
- `decideBranchDispositionByFacts` runs after every predecessor projection has passed concrete edge validation and the boundary has passed its native join/loop shape check. It independently confirms that every reported predecessor comes from a terminator with a continuing target and that the reported edge maps exactly to the declared boundary target. A terminal block therefore cannot be admitted as a continuing predecessor.

Branch-local live-linear non-omission is not duplicated in this kernel: the Certified Resource Scope proof derives it from `PHIL-RES-JOIN-001`, and production now does the same through the already-bound Resource Join kernel.

## Closeout gate

`Phase 1 Resource Scope Production Binding`:

1. recompiles the Certified Core join/scope chain and implementation correspondence under Rocq 9.2.0;
2. fresh-extracts `ResourceScopeKernel.hs`, requires the staged SHA-256 above, and byte-compares both checked-in copies;
3. builds the ordinary `phil-core` library with warnings as errors, including explicit `ResourceScopeKernel` module registration;
4. strict-typechecks the exact production kernel and `ControlStateProjection` binding;
5. executes all 8 direct extracted-kernel controls through `src/`; and
6. reruns the unchanged 8-case RES-005 through RES-008 correspondence corpus.

Concrete Map/Set representation, CFG/value lookup, source lexical-scope elaboration, the current `BorrowedSlice` representation, exact diagnostic ordering, and future non-lexical lifetime evidence remain explicit representation/correspondence boundaries. The closeout claims machine refinement of the current Phase 1 lexical-scope semantics, not a future lifetime-polymorphic borrow system.
