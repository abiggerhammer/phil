# PHIL-SURFACE-BINDER-SCOPE-001 — loop-state scope proof boundary

This slice continues SURF-009 certification with Grammar-v1 loop-state binders.

## Certified lexical phases

Loop state has a visibility rule distinct from post-join state:

1. **all entry initializers** are checked in the parent/pre-loop scope while every loop-header name is still pending;
2. header slot **types** are checked left-to-right before each corresponding binder is introduced;
3. the invariant sees the **complete header telescope**;
4. the loop body runs in a nested child scope that sees the complete header; and
5. body/header scopes are discarded on loop exit while the declaration-wide fresh ordinal remains advanced.

The normalized proof certifies:

- existing parent references in initializers resolve exactly;
- self/future loop-header references from initializers reject;
- unknown nonlocal initializer names remain outside local-binder competence;
- later loop-state types may depend on earlier header binders;
- self/current/future header references in slot types reject;
- header allocation preserves source order and count;
- the header consumes exactly one fresh ordinal per slot;
- invariant and body visibility are exactly the completed header telescope;
- leaving the loop cannot roll back header/body allocation;
- loop-local names disappear after exit;
- explicit `continue` actual lists are preserved exactly, including the zero-actual case; and
- alpha-renaming/source movement preserves semantic loop-state identities when header shape is unchanged.

## Existing authorities reused

- `SurfaceBinderScopeCore` / `PHIL-EXEC-BIND-001` own individual binder identity/admission.
- `SurfaceLetPatternScope` owns body-local let/pattern ordering.
- `SurfaceJoinStateScope` supplies the immediately preceding post-control telescope proof family, but loop initializer visibility remains intentionally separate.

`PHIL-RES-LOOP-001` continues to own resource projection, backedge admission, state arity, and propositional transport. This slice does not duplicate those semantics.

## Concrete correspondence

`Phil.Surface.GrammarV1.LoopStateScope` is the production lexical authority.

The permanent `Phase1GrammarV1JoinLoopMain.hs` corpus checks:

- initializers against entry scope;
- header state flowing into explicit `continue` actuals;
- later header types depending on earlier header binders;
- initializer non-visibility of future header binders;
- type-level forward-reference rejection;
- active-shadowing and duplicate rejection;
- body-local let/break scope closure;
- zero-actual `continue` non-capture; and
- alpha-stable loop-state identity.

## Still open

Refinement binders and protocol message/branch-payload binders remain separate SURF-009 slices.

Concrete parser/reference traversal, `Text`/`Set`/`Map` representation, exact diagnostics, resource/backedge semantics, GHC/runtime correctness, and Rocq/toolchain correctness remain explicit boundaries.
