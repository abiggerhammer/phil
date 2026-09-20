# PHIL-SURFACE-BINDER-SCOPE-001 — let/pattern scope proof boundary

This slice continues Surface binder-scope certification after the term-binder and generic-static binder cores.

## Certified boundary

Production separates two operations that must remain ordered:

1. resolve a `let` initializer in the scope that exists **before** the let; then
2. allocate every binder introduced by the pattern in exact source preorder.

The normalized Rocq model certifies that:

- an empty pattern allocates no binder identities;
- each source binder site consumes exactly one declaration-wide fresh ordinal;
- allocation preserves binder count and source preorder;
- alpha-renaming/source movement of a pattern does not alter generated semantic identities when the binder shape is unchanged;
- the initializer result is independent of binders that will be introduced by the same let;
- therefore a future let binder cannot make a previously unresolved initializer local;
- an already-active initializer binder is preserved exactly; and
- the post-let ordinal advances monotonically by the number of pattern binders.

## Existing authority reused

All individual binder admission rules remain owned by the previously certified term-binder core and `PHIL-EXEC-BIND-001`: duplicates and active shadowing fail through that authority. This slice adds only recursive pattern ordering and the initializer-before-binding composition rule.

## Concrete correspondence

The production path is:

- `PatternBinderScope.grammarV1BindPattern`, which traverses identifier, tuple, and record patterns in source preorder and treats a bare record field as its shorthand binder;
- `LetPatternScope`, which resolves the initializer first and then applies the pattern binder traversal; and
- `ParameterBodyScope`, which confirms subsequent bounded local occurrences resolve to the exact generated binder/Core identity.

The permanent `Phase1GrammarV1LetPatternScopeMain.hs` corpus covers recursive tuple/record preorder, self-reference non-visibility, duplicate recursive-pattern rejection, active parameter-name collision, closure/outer-scope composition, and alpha-stable tuple-pattern identity.

## Still open

Match/decide/offer arm binders, borrow-view binders, join/loop state binders, refinement binders, and protocol message/branch binders remain separate SURF-009 slices.

Concrete parser-tree traversal, `Text`/`Map` representation, exact diagnostic constructors, pattern/value shape checking, Core type/resource semantics, GHC/runtime correctness, and Rocq/toolchain correctness remain explicit boundaries.
