# PHIL-SURFACE-BINDER-SCOPE-001 — join-state scope proof boundary

This slice continues SURF-009 certification with explicit post-join state binders.

## Certified lexical boundary

Grammar-v1 join state is a post-predecessor telescope. Production checks it in this order:

1. predecessor match arms or if branches complete and their child-local names leave scope;
2. each join-slot type is checked against the scope that exists **before that slot is introduced**;
3. the slot binder is allocated from the next declaration-wide ordinal;
4. later slot types may therefore refer to earlier join slots;
5. self/current/future slot names remain pending and reject as forward references; and
6. the join invariant is checked only after the complete slot telescope exists.

The normalized Rocq proof certifies:

- predecessor branch locals do not enter post-join scope;
- earlier post-join slots resolve exactly;
- current/future post-join slot references reject;
- unrelated nonlocal names remain outside local-binder competence rather than being guessed;
- join-slot binder allocation preserves source order and count;
- each slot gets the exact declaration-rooted next identity;
- the final ordinal advances by exactly the telescope length;
- invariant scope begins at that completed-telescope point; and
- alpha-renaming/source movement preserves semantic join-slot identities when telescope shape is unchanged.

## Existing authorities reused

- `SurfaceBinderScopeCore` / `PHIL-EXEC-BIND-001` own individual binder admission and exact semantic identity.
- `SurfaceCaseArmScope` owns match/decide/offer predecessor arm scope.
- `SurfaceLetPatternScope` owns branch-local let/pattern scope.

Resource projection and ownership conservation remain `PHIL-RES-JOIN-001`; invariant truth remains `PHIL-RES-INVARIANT-001`. This slice does not duplicate either semantic theorem.

## Concrete correspondence

`Phil.Surface.GrammarV1.JoinStateScope` is the production lexical authority for explicit join state on `match` and `if`.

The existing `Phase1GrammarV1JoinLoopMain.hs` corpus pressures:

- post-arm fresh join identities;
- active-shadowing rejection;
- later slot types depending on earlier join slots;
- forward-reference rejection;
- disjoint if-branch predecessor locals;
- omitted-else non-invention;
- join-name non-visibility inside predecessor arms; and
- alpha-stable join-state identity.

The same corpus also contains loop-state cases; those remain successor evidence rather than claims of this slice.

## Still open

Loop-state binders, refinement binders, and protocol message/branch-payload binders remain separate SURF-009 slices.

Concrete `Text`/`Set`/`Map` representation, parser traversal, exact diagnostics, type checking, proposition truth, resource projection, GHC/runtime correctness, and Rocq/toolchain correctness remain explicit boundaries.
