# PHIL-AUD-BORROW-LOCAL-001 remediation

## Audit identity

- Finding: `PHIL-AUD-BORROW-LOCAL-001`
- Audit event: `PHIL-AUDIT-20260921-BORROW-SCOPE`
- Original review snapshot: `255b84a68fa1cf4fce5db8bf72e52d58e6cb8dd3`
- Affected consumer: `Phil.Surface.Check.Engine.evalBorrow`

This document records the implementation remediation only. It does not change
the audit ledger's proof status, Phase-1 conformance status, or any Certified
claim.

## Root cause

The Surface borrow checker already had three important protections:

1. the owner remains under an active shared loan while the body is checked;
2. a directly returned borrowed view, including one nested in a runtime tuple,
   is rejected; and
3. the named view binding is removed before the shared loan ends.

The missing operation was **child-scope cleanup of every other binding created
inside the borrow body**. `evalBorrow` called `checkValueBlock` directly and
then removed only the explicit view spelling. A body-local alias such as
`escaped = view` could therefore remain in `stateBindings` and the Core
unrestricted zone after the loan ended.

That produced both sides of the same scope bug:

- an alias could remain readable after the owner was consumed; and
- a harmless child-local spelling could incorrectly block reuse outside the
  closed borrow.

## Repair

`evalBorrow` now checks the body with the existing
`checkScopedValueBlock environment incoming scoped body` path, using the
pre-borrow state as the incoming binding domain and the loaned state plus view
as the child state.

That existing scope-exit mechanism:

- computes all names added relative to the incoming domain;
- rejects any still-live child-local linear binding;
- removes unrestricted and affine child locals from both Surface metadata and
  the Core resource context; and
- preserves all pre-existing bindings.

The existing direct/aggregate returned-view check remains in `evalBorrow`.
The owner loan is still ended only after scoped cleanup succeeds. Initial owner
mode checks and Core active-loan consumption checks are unchanged.

This reuses the same semantic cleanup mechanism already used by decision/offer
child regions rather than creating a borrow-specific alias scanner.

## Permanent regression

`test/Phase1AuditBorrowScopeMain.hs` runs ordinary source through
`parseSurfaceFile` and `checkSurfaceComponent`, using the unchanged common
Phase-0 environment selected by
`phase0EnvironmentFor "examples/rejected/16-escape-shared-loan.phil"`.

The eight cases preserve the audit ledger's closure obligations:

1. safe local view use — accept;
2. directly returned view — `BorrowEscape`;
3. tuple containing returned view — `BorrowEscape`;
4. owner consumption during the active loan — `StructuralUse`;
5. original view spelling after scope exit — `StructuralUse`;
6. hidden let alias after owner consumption — `BorrowEscape` or
   `StructuralUse`;
7. hidden tuple alias after owner consumption — `BorrowEscape` or
   `StructuralUse`; and
8. reuse of a closed child-local spelling — accept.

The dedicated workflow strict-typechecks and executes this corpus under
GHC 9.6.7, then replays the frozen Surface conformance test suite so the repair
does not silently weaken the existing Phase-0 boundary.

## Remaining audit boundary

This slice does not assert that richer shape-changing carriers, nested borrows,
metadata/refinement-fact scope, or every Grammar-v1 dispatcher route are closed.
Those remain separate obligations in the live audit ledger.

At authoring, exact-head CI has not yet supplied execution evidence. A green
whole build alone is not treated as finding closeout; the dedicated eight-case
consumer replay is the relevant evidence.
