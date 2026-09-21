# PHIL-SURFACE-BINDER-SCOPE-001 — borrow-view scope proof boundary

This slice continues SURF-009 certification with the bounded lexical rule for Grammar-v1 `borrow e as view { ... }`.

## Certified boundary

Production performs borrow lexical handling in this exact order:

1. resolve the owner expression in the parent scope;
2. enter a fresh child lexical frame;
3. allocate the view binder from the next declaration-wide ordinal;
4. check body-local lets inside that child frame;
5. leave the child frame, making the view and body-local binders unavailable; and
6. retain the advanced ordinal for later sibling scopes.

The normalized proof certifies that:

- an active owner resolves before the view exists;
- a future view binder cannot retroactively resolve the owner;
- the view binder gets the exact next declaration-rooted semantic identity;
- owner resolution is independent of future view/body binder creation;
- borrow exit never rolls the declaration-wide ordinal backward;
- borrow-local names disappear at child-scope exit;
- a later sibling borrow cannot reuse the earlier view's semantic identity; and
- alpha-renaming/source movement of the borrow view does not change semantic identity.

## Existing authority reused

- `SurfaceBinderScopeCore` / `PHIL-EXEC-BIND-001` own individual binder identity, duplicate rejection, active-shadowing rejection, and semantic-key injectivity.
- `SurfaceLetPatternScope` remains the body-local let/pattern authority.

This theorem adds only the borrow-specific owner-before-view and child-frame lifetime composition.

## Concrete correspondence

`Phil.Surface.GrammarV1.BorrowViewScope` is the production lexical authority.

The permanent `Phase1GrammarV1BorrowViewScopeMain.hs` corpus checks:

- owner resolution before view binding;
- body references to the exact generated view identity;
- child-scope removal of both the view and body-local lets;
- declaration-wide ordinal preservation after child exit;
- sibling borrow spelling reuse with fresh identities;
- active-shadowing rejection;
- future-view non-visibility; and
- alpha-stable borrow-view identity.

## Still open

Join/loop state binders, refinement binders, and protocol message/branch-payload binders remain separate SURF-009 slices.

Borrow ownership mode, loan validity, alias/resource safety, returned-value borrowing rules, parser representation, exact diagnostics, GHC/runtime correctness, and Rocq/toolchain correctness remain explicit separate authorities or TCB boundaries.
