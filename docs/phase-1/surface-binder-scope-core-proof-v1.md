# PHIL-SURFACE-BINDER-SCOPE-001 — term-binder scope core proof boundary

This slice begins the mechanized Surface binder-scope obligation without duplicating the already-Certified execution binder semantics.

## Predecessor authority

`PHIL-EXEC-BIND-001` already proves the normalized binder algebra used by SURF-009:

- binder identity is exact declaration root plus lexical ordinal;
- display spelling and source position are nonsemantic;
- duplicate binders reject;
- active lexical shadowing rejects; and
- closed sibling scopes may reuse a spelling only with a fresh ordinal.

The new Surface theorem imports that authority directly.

## Surface boundary certified by this slice

`proof/Phil/Surface/SurfaceBinderScopeCore.v` records the term-binder route used by Grammar-v1:

- source spelling/span do not alter the semantic binder key;
- accepted binders retain the exact declaration root and ordinal from `PHIL-EXEC-BIND-001`;
- duplicate-current-frame and active-outer-frame cases reject;
- leaving a lexical scope does not roll back the declaration-wide ordinal;
- reopening a sibling scope therefore gives a distinct semantic occurrence;
- equal local ordinals under distinct declaration roots remain distinct; and
- local reference classification is fail-closed:
  - an active local resolves to its exact binder;
  - a pending local rejects as a forward reference; and
  - an unresolved nonlocal name remains outside the bounded local-binder route rather than being guessed to be local.

## Concrete correspondence

The production authority is split across:

- `Phil.Surface.GrammarV1.BinderScope` — declaration-rooted `GrammarV1BinderKey`, monotonic ordinal allocation, lexical frames, duplicate/shadowing rejection, scope exit, and exact lookup;
- `ParameterBodyScope` — exact parameter occurrences in bounded function/closure bodies;
- `LexicalReferenceScope` — local-vs-forward-vs-nonlocal reference classification; and
- `SemanticFunctionHeader` — generated Core names are used in Surface/Core semantic state and dependent result types.

The permanent `Phase1GrammarV1BinderScopeMain.hs` corpus pressures alpha/source-span stability, duplicate rejection, active shadowing, sibling freshness, declaration-root separation, exact body resolution, unknown-name non-competence, and generated-name use in semantic function headers.

## Still open under PHIL-SURFACE-BINDER-SCOPE-001

This is the first bounded certification slice, not the final aggregate. Separate successor slices still need to compose:

- generic-static binder identity/resolution;
- let/pattern binders;
- match-arm and borrow-view binders;
- join/loop state binders;
- refinement binders; and
- protocol message/branch-payload binders.

Those surfaces already have executable coverage in several cases, but this PR does not silently claim them.

Concrete `Text`/`Map` representation, the injective `$phil.local:` Core-name serialization, source spans, parser traversal, exact Haskell diagnostics, GHC/runtime correctness, and Rocq/toolchain correctness remain explicit correspondence/TCB boundaries.
