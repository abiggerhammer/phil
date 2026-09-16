# Effect polymorphism implementation refinement v1

`PHIL-EFFECT-POLY-001` is Certified by `proof/Phil/Core/EffectPolymorphism.v`. This implementation-refinement layer isolates the executable admission surface for bounded `Effects` instantiation.

## Extracted semantic seam

`proof/Phil/Core/EffectPolymorphismImplementation.v` exposes one ordered decision over four reflected facts:

1. exact generic parameter identity;
2. `Effects` kind recognition;
3. successful canonical finite-set decoding; and
4. actual effect set is a subset of the declared upper bound.

The semantic proof establishes that accepted instantiations preserve exact parameter identity and the original upper bound, admit equal or narrower sets, reject widening, and preserve complete subject-aware semantic effect identities.

## Native boundary

The following remain native representation/runtime facts:

- `GenericStaticParameterKey` equality;
- `GenericEffectsKind` recognition;
- `SemanticForm` representation and canonical finite-set decoding;
- `Data.Set` representation, difference, and emptiness;
- excess-set and diagnostic payload construction;
- CALL-EFFECT callable latency/invocation behavior; and
- Rocq extraction, GHC, and runtime correctness.

The extracted kernel owns only the final ordered admission decision after those primitive facts are reflected as booleans.

## Production-binding rule

The row may move to `Implementation Refined` only when CI fresh-extracts the decision kernel, proves byte identity with the checked-in production copy, verifies its fixed digest, exercises direct decision controls, strict-typechecks the production `Phil.Core.EffectPolymorphism` route and Grammar-v1 bridge, and reruns the unchanged EFF-003/004 corpus.
