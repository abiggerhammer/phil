# PHIL-SURFACE-BINDER-SCOPE-001 — semantic refinement binder scope

This slice continues SURF-009 certification with the primitive-base semantic refinement path.

## Certified lexical boundary

For a source refinement such as `{v : U8 | P(v)}`, production:

1. enters one child lexical frame;
2. allocates a `GrammarV1RefinementBinder` through the ordinary declaration-root + ordinal binder authority;
3. resolves/rewrite predicate-local uses to that exact generated semantic identity;
4. inserts the semantic binding under the resolver-issued Core name, not source spelling;
5. checks/focuses the predicate; and
6. leaves the child frame while retaining the advanced declaration-wide ordinal.

The normalized proof certifies:

- accepted refinement binders use the exact next declaration-rooted semantic identity;
- active lexical shadowing and duplicate child binding reject through the existing binder authority;
- a same-spelled `SurfaceState` entry is not itself lexical shadowing authority;
- predicate-local use resolves to the exact generated binder;
- nonlocal predicate use is not invented as a refinement-local reference;
- the refinement binder disappears when the child frame closes;
- the outer ordinal advances exactly once;
- sibling refinements therefore receive fresh semantic identities; and
- alpha-renaming/source movement does not change semantic refinement identity.

## Existing authorities reused

- `SurfaceBinderScopeCore` / `PHIL-EXEC-BIND-001` own normalized binder identity, duplicate rejection, active-shadowing rejection, and sibling freshness.
- Core proposition focusing remains the authority for predicate truth/sort/coercion behavior.

This slice does not duplicate proposition semantics or the concrete generated Core-name serialization.

## Concrete correspondence

`Phil.Surface.GrammarV1.SemanticRefinementType` is the production refinement-binder authority. It inserts the binder into `SurfaceState` only under `grammarV1ResolvedBinderCoreName` and rewrites predicate references only where `LexicalReferenceScope` supplied exact local evidence.

The permanent `Phase1GrammarV1IntrinsicRefinementTypeElaborationMain.hs` corpus checks:

- generated Core identity rather than source spelling;
- exact predicate-reference evidence;
- alpha-stable binder/Core/type identity;
- sibling refinement ordinal advancement;
- lexical shadowing despite unrelated `SurfaceState` spelling behavior; and
- explicit preservation of Core focusing failures.

## Still open

Protocol message and branch-payload binders remain the final named SURF-009 binder family after this slice.

Concrete `Text`/`Map` representation, Core-name encoding, proposition traversal/rewrite correctness, focusing semantics, GHC/runtime correctness, and Rocq/toolchain correctness remain explicit boundaries.
