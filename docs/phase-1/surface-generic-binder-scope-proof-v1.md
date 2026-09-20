# PHIL-SURFACE-BINDER-SCOPE-001 — generic-static binder scope proof boundary

This slice continues the Surface binder-scope certification after the term-binder core by closing the declaration-header generic-static binder identity and lookup boundary.

## Boundary owned here

`Phil.Surface.GrammarV1.GenericBinderScope` gives each generic parameter a semantic `GenericStaticParameterKey` derived from:

- the exact enclosing `DeclarationKey`; and
- a monotonic ordinal in the generic-parameter telescope.

Source spelling and source span are retained only for diagnostics. The proof models that authority directly and establishes:

- alpha-renaming/source movement does not change generic binder identity;
- the generated key preserves the exact declaration root and ordinal;
- different telescope positions are distinct;
- equal ordinals under different declaration roots remain distinct;
- duplicate generic parameter spellings reject;
- lookup returns the exact already-bound semantic parameter;
- absent generic names reject rather than being guessed; and
- term-local binder identity and generic-static binder identity inhabit distinct semantic namespaces.

## Imported semantic authorities

This slice does **not** reinterpret generic kinds or generic values.

- `PHIL-SURFACE-ELAB-001` remains the Surface semantic-routing authority.
- `PHIL-GEN-KIND-001` remains the exact static-actual kind-selection authority.
- `PHIL-EFFECT-POLY-001` remains the bounded Effects-instantiation authority.

Those theorem families explicitly leave concrete `GenericStaticParameterKey` construction and source name resolution as correspondence boundaries; this slice closes that Surface-specific gap.

## Concrete correspondence

The permanent `Phase1GrammarV1GenericBinderScopeMain.hs` corpus checks:

- alpha/source-span-stable function generic keys;
- all nine Grammar-v1 generic kinds routed to their exact existing Core kinds;
- duplicate generic-binder rejection;
- declaration-root separation;
- exact lookup and missing-name rejection;
- resolver-issued identity flowing into callable Effects use; and
- preservation of that exact key through the already-Certified effect-polymorphism path.

The last two cases are composition evidence only; this proof does not duplicate effect semantics.

## Remaining PHIL-SURFACE-BINDER-SCOPE-001 work

Still separate are:

- let/pattern, match-arm, and borrow-view term binders;
- join/loop state binders;
- refinement binders; and
- protocol message/branch-payload binders.

Concrete `Text`/`Map` representation, `$phil.static:` serialization, source spans, exact Haskell diagnostics, generic-kind bridge implementation, GHC/runtime correctness, and Rocq/toolchain correctness remain explicit correspondence/TCB boundaries.
