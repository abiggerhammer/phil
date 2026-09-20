# PHIL-SURFACE-BINDER-SCOPE-001 — case-arm scope proof boundary

This slice continues the SURF-009 binder-scope certification with the shared lexical rule used by Grammar-v1 `match`, `decide`, and `offer` arms.

## Certified boundary

The production order is exact:

1. resolve the case scrutinee in the parent scope;
2. enter a fresh child lexical frame for one arm;
3. allocate that arm's tuple/record binders in source order;
4. check arm-local lets inside the same child frame;
5. leave the child frame, making its names unavailable; and
6. retain the advanced declaration-wide ordinal for the next sibling arm.

The normalized proof certifies that:

- an active scrutinee resolves before arm binders exist;
- a future arm binder cannot retroactively make the scrutinee local;
- arm binder allocation is exactly the already-certified pattern allocation;
- leaving an arm does not retain its local names;
- the advanced ordinal is preserved across arm exit;
- every nonempty arm advances the start ordinal available to the next sibling;
- sibling spelling reuse therefore cannot reuse the prior arm's first semantic identity;
- alpha-renaming preserves arm semantic binder identities when arm binder shape is unchanged; and
- `match ... join state ...` remains explicitly outside this bounded case-arm theorem because join-state binders have their own SURF-009 authority.

## Existing authority reused

- `SurfaceBinderScopeCore` / `PHIL-EXEC-BIND-001` own individual binder admission, duplicate rejection, active-shadowing rejection, and semantic-key injectivity.
- `SurfaceLetPatternScope` owns recursive pattern source-order allocation and arm-local let ordering.

This slice only adds child-frame isolation and sibling ordinal threading.

## Concrete correspondence

`Phil.Surface.GrammarV1.CaseArmScope` is the shared production authority for `match`, `decide`, and `offer`.

The permanent `Phase1GrammarV1CaseArmScopeMain.hs` corpus checks:

- disjoint sibling arm scopes with fresh identities;
- exact tuple binder source order;
- record-field aliases and shorthand binders;
- arm-local let composition;
- the shared `decide` route;
- duplicate and active-shadowing rejection;
- scrutinee-before-arm visibility;
- explicit join-state non-competence; and
- alpha-stable semantic arm identities.

Parser syntax coverage for `offer` remains independently exercised by the existing offer corpus.

## Still open

Borrow-view binders, join/loop state binders, refinement binders, and protocol message/branch-payload binders remain separate SURF-009 slices.

Concrete `Text`/`Map` representation, parser traversal, exact diagnostic constructors, case-pattern/value compatibility, branch semantic typing, GHC/runtime correctness, and Rocq/toolchain correctness remain explicit boundaries.
