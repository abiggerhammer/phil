# Effect subject implementation refinement v1

`PHIL-EFFECT-SUBJECT-001` is Certified by `proof/Phil/Core/EffectSubject.v`. This implementation-refinement layer isolates the bounded executable decision surface used by the Haskell EFF-001/002 implementation.

## Extracted semantic seams

`proof/Phil/Core/EffectSubjectImplementation.v` exposes two ordered decisions.

1. **Correspondence integrity** — source subject key nonempty, target subject key nonempty, then relation revision nonempty.
2. **Subject retarget admission** — subject index in range first; exact source/target identity then accepts without correspondence; a changed subject requires correspondence; supplied correspondence must name the exact current source and exact requested target.

The Rocq proof relates the accepting branches back to the Certified semantic retarget relation. Representation coincidence is deliberately absent from the decision inputs, so no runtime handle, pointer, source spelling, target symbol, address, or other representation fact can authorize retargeting.

## Native boundary

The following remain native representation/runtime facts:

- `Text` representation, equality, and nonemptiness;
- list indexing and replacement over concrete Haskell subject lists;
- construction and canonical serialization of `SemanticEffect`;
- truth and competence of an externally accepted equality/succession/correspondence relation;
- concrete error payload reconstruction; and
- Rocq extraction, GHC, and runtime correctness.

The extracted kernel owns only the final semantic branch order after those primitive facts are reflected as booleans.

## Production-binding rule

The row may move to `Implementation Refined` only when CI fresh-extracts the decision kernel, proves byte identity with the checked-in production copy, verifies the fixed kernel digest, exercises direct decision controls, strict-typechecks the production `Phil.Core.Effect` route, and reruns the unchanged EFF-001/002 corpus.
