# PHIL-SURFACE-BINDER-SCOPE-001 — callable outcome-state binder scope

The final binder-kind inventory exposed one production family that was not named in the earlier SURF-009 successor lists: `GrammarV1CallableOutcomeStateBinder`.

This slice certifies that missing family before aggregate closeout.

## Certified lexical boundary

Each explicit callable outcome `state(...)` clause is checked in its own child lexical frame.

- State slots are allocated in source order from the declaration-wide next ordinal.
- The child lexical frame disappears when that state clause closes.
- The advanced ordinal is retained across sibling state clauses and sibling outcome residues, so same-spelled sibling slots remain semantically distinct.
- Each sibling state scope starts its semantic `SurfaceState` from the callable parameter state; branch-local semantic bindings do not leak into siblings.
- Outcome proposition checking consumes the exact binder evidence from the selected branch-state scope.
- Repeated state clauses remain distinct and ambiguous for proposition routing rather than being silently merged.
- Whole-callable composition may begin after a closed result-refinement binder has already advanced the ordinal; this family never restarts a private identity stream.
- Alpha-renaming/source movement preserves semantic slot identities when state-clause shape is unchanged.

Duplicate slot rejection and active-shadowing behavior remain inherited from the common binder authority.

## Existing authorities reused

- `SurfaceBinderScopeCore` / `PHIL-EXEC-BIND-001` own exact declaration-root + ordinal identity, duplicate rejection, and sibling freshness.
- `SurfaceLetPatternScope` supplies the common ordered allocator used for bounded telescopes.
- Core proposition focusing remains authoritative for outcome proposition truth and sort/coercion behavior.

## Concrete correspondence

`Phil.Surface.GrammarV1.SemanticCallableOutcomeState` is the production lexical/state-composition authority.

The permanent `Phase1GrammarV1CallableOutcomeStateMain.hs` corpus checks:

- generated sibling-unique outcome-state identities;
- exact branch-state binder evidence in ensures/obligations;
- alpha-stable callable parameter/state identities and Core propositions;
- repeated state-clause ambiguity;
- explicit duplicate-state binder rejection;
- bounded primitive-state competence; and
- rejection of outcome-state shadowing of active callable generics.

## Inventory correction

The complete `GrammarV1BinderKind` inventory is:

- function parameters;
- callable parameters;
- callable outcome-state binders;
- claim parameters;
- component parameters;
- closure parameters;
- refinement binders;
- let/pattern binders;
- match/decide/offer arm binders;
- borrow-view binders;
- join-state binders;
- loop-state binders;
- protocol message binders; and
- protocol branch-payload binders.

Generic-static binders live in their separate `GenericStaticParameterKey` identity domain and are also covered by SURF-009.

After this slice lands, the aggregate closeout may accurately claim complete production binder-family coverage.
