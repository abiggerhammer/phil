# PHIL-EFFECT-POLY-001 production binding v1

This closeout binds the Certified EFF-003/004 bounded effect-set instantiation decision to the exact Rocq-extracted Haskell kernel.

## Exact extracted kernel

Production checks in:

- `src/EffectPolymorphismKernel.hs`

The required SHA-256 is:

`6e73c70c6fb3455f63f72dcf3a88f11d48d6b6b8c98f038a7a9275cb83cc5db8`

CI fresh-extracts `EffectPolymorphismKernel.hs` from `proof/Phil/Core/EffectPolymorphismImplementationExtraction.v`, compares it byte-for-byte with the checked-in production copy, and rejects any digest drift.

## Production-bound decision

`src/Phil/Core/EffectPolymorphism.hs` retains concrete representation work and supplies four primitive facts to the extracted kernel:

1. actual generic parameter key equals the exact declared key;
2. actual kind is exactly `Effects`;
3. the actual `SemanticForm` decodes as the canonical finite effect-set representation; and
4. the decoded actual set has no member outside the declared upper bound.

The kernel owns that ordering. A key mismatch rejects before kind inspection; kind mismatch rejects before semantic-form decoding is authoritative; malformed effect-set representation rejects before the subset result matters; and only an exact-or-narrower canonical set is admitted.

Production retains `SemanticForm` decoding, `Data.Set` operations, excess-set construction, and public diagnostic reconstruction. The accepted result preserves the original declared upper bound and the exact decoded actual set.

## Preserved boundaries

This binding does **not** claim to verify:

- Haskell `GenericStaticParameterKey`, `GenericStaticKind`, `SemanticForm`, or `Data.Set` representations;
- correctness of concrete finite-set decoding or set operations;
- source-to-Core generic/effect resolution;
- CALL-EFFECT callable latency, storage, return, or invocation semantics beyond imported Certified predecessors;
- diagnostics beyond their checked decision routing;
- Rocq extraction, GHC, or runtime correctness.

## Closeout criterion

`PHIL-EFFECT-POLY-001` may move to `Discharged / Implementation Refined` only when one exact-head CI run verifies all of the following together:

- the Certified and implementation Rocq proofs compile;
- fresh extraction is byte-identical to `src/EffectPolymorphismKernel.hs`;
- the exact kernel hash above matches;
- direct extracted-kernel controls pass;
- the bound `src/Phil/Core/EffectPolymorphism.hs` route and Grammar-v1 bridge strict-typecheck with `-Wall -Werror`; and
- the unchanged EFF-003/004 generic-binder/effect-polymorphism corpus remains green.
