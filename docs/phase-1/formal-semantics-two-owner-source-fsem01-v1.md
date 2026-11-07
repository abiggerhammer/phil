# FSEM-01 — single-source two-linear-owner borrow conformance

> **Non-normative bounded source-checking slice**, following [#1653](https://github.com/abiggerhammer/phil/pull/1653) and tracking [#1613](https://github.com/abiggerhammer/phil/issues/1613). This does **not** discharge arbitrary source elaboration or Haskell-to-Rocq refinement.

## New evidence boundary

Prior FSEM-01 CONTEXT2-V1 evidence composed two `Core.Name` values that had
been resolved from *separately checked* one-owner source fragments. The earlier
Haskell `Core.Context` and Rocq frame lemmas correctly modeled two distinct
owners, but did not check one source function containing both.

The new bounded [source bridge](../../src/Phil/Surface/GrammarV1/TwoOwnerBorrowResourceSurface.hs)
accepts one actual parsed Grammar-v1 function of the form:

```phil
fn loan(owner : Bytes[8], spectator : Bytes[8]) -> (Bytes[8], Bytes[8]) satisfies C {
  borrow owner as view { view; unit; };
  return (owner, spectator);
}
```

It uses the production parser, checked intrinsic type/mode for **each**
parameter and **each** result element, and `grammarV1FunctionParameterScope`
to obtain two **distinct exact lexical binder keys and generated Core names**.
It resolves borrow, view, and both returned names within their actual scopes.
Any global fallback, foreign name, reversed return, extra parameter,
non-Bytes/incorrect mode/type, or unsupported syntax fails closed as
noncompetence or a precise scope/type error.

A restricted, source-span-preserving projection puts *both* checked linear
parameter bindings into the **actual production Surface checker**, not a
synthetically enlarged checkpoint. The checker then executes its existing
`startSharedLoan`, scoped-view cleanup, `endSharedLoan`, and sequential tuple
element consumption. `traceSurfaceBorrowComponent` captures full
`Core.ResourceContext` U/A/L/loan maps **from the real two-owner checker state**.

[Strict source tests](../../test/Phase1FSEM01TwoOwnerSourceMain.hs) require
both owners to be present before the borrow, the spectator to remain unaffected
during primary loan start/end, and both owners to be consumed at successful
return. They independently replay the Core operations and check actual
resulting snapshots. The rejected fixture differs from the accepted fixture
only by removing the final Unit expression inside the borrow body, thereby
returning a live borrowed view. It must reject specifically with
`BorrowEscape: shared view escapes its lexical scope`, without any fabricated
post-error consumption. The borrowed primary remains unconsumable; the
independent spectator can still be consumed without ending the primary loan.

Source fixtures:
[accepted](../../test/fixtures/fsem01-two-owner-source-v1/accepted.phil),
[BorrowEscape](../../test/fixtures/fsem01-two-owner-source-v1/escape.phil),
[reversed return](../../test/fixtures/fsem01-two-owner-source-v1/reversed-return.phil),
and [unadmitted third parameter](../../test/fixtures/fsem01-two-owner-source-v1/third-owner.phil).

## Explicit type/assurance boundary

Grammar-v1 parses tuple types, but the existing general
`grammarV1BoundType` does **not** yet elaborate them into `TyProduct`.
The Surface runtime uses an **opaque** `TyOpaque "Tuple[2]"` carrier for
tuple returns. This slice checks both source tuple element types and the
corresponding exact returned binder occurrences independently, and tests
the production tuple's two actual linear consumptions. It does **not** claim
that an arbitrary source tuple is correctly typed, provide global product
typing, or identify the opaque runtime marker with a fully elaborated
`TyProduct`. General tuple elaboration remains separate work.

Likewise `satisfies C` remains a source syntax placeholder in this
restricted checker: no checked C requirement is invented or discharged.

## Relation to Rocq and CI

The previously merged [two-owner Rocq frame
proofs](../../proof/Phil/Surface/SurfaceTwoOwnerContext.v)
establish extensional lookup preservation for a distinct spectator, not a
universal proof of the Haskell checker. This change adds **direct actual
single-source Haskell evidence** matching that bounded representation.
Source-to-Rocq refinement and proof of the exact tuple product typing
judgment remain open.

[Dedicated CI](../../.github/workflows/fsem01-two-owner-source.yml)
compiles the registered bounded production bridge warning-free, runs actual
accepted/rejected source witnesses and independent Core-operation replay,
and reruns the earlier one-owner OBS-V1 and composed CONTEXT2-V1 Haskell tests.
All existing proof and source artifacts remain unmodified. The dedicated
workflow is covered by the PR-only CI supersession policy.

## Further work

General multi-owner and elementwise product elaboration, arbitrary finite
Map/Set-to-Rocq simulation, branch joins, captures, loops, Unicode carrier
proof, source error preservation beyond the admitted fragment, and
`satisfies C` assurance discharge are **not proved here**. Any claim of
language-wide preservation or type soundness requires its own precise
theorem and independent evidence.
