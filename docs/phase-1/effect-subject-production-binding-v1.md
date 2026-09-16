# PHIL-EFFECT-SUBJECT-001 production binding v1

This closeout binds the Certified EFF-001/002 semantic effect-subject decision surface to the exact Rocq-extracted Haskell kernel.

## Exact extracted kernel

Production checks in:

- `src/EffectSubjectKernel.hs`

The required SHA-256 is:

`91b982a6891d04a3915d7cb8293c3c39ae3da0789c49f0ced4235a3d4c8f154e`

CI fresh-extracts `EffectSubjectKernel.hs` from `proof/Phil/Core/EffectSubjectImplementationExtraction.v`, compares it byte-for-byte with the checked-in production copy, and rejects any digest drift.

## Production-bound decisions

`src/Phil/Core/Effect.hs` retains concrete representation work and supplies primitive facts to two extracted decisions.

### 1. Correspondence integrity

The extracted kernel owns this order:

1. source semantic-subject key nonempty;
2. target semantic-subject key nonempty; and
3. accepted relation revision nonempty.

Production retains concrete `Text` representation/nonemptiness and the opaque `SemanticEffectSubjectCorrespondence` constructor. Truth and competence of the named relation remain an outer authority boundary.

### 2. Exact subject retarget admission

The extracted kernel owns this order:

1. requested subject index is in range;
2. exact same subject accepts without correspondence;
3. a changed subject requires correspondence;
4. supplied correspondence must name the exact current source; and
5. supplied correspondence must name the exact requested target.

Only the exact correspondence branch permits rebuilding the semantic effect identity with the replacement subject. Runtime/representation coincidence has no input to the kernel.

Production retains concrete list indexing/replacement, `SemanticEffectSubjectKey` equality, canonical effect serialization, and public diagnostic payload reconstruction.

## Preserved boundaries

This binding does **not** claim to verify:

- `Text`, list, `Maybe`, or `SemanticEffect` representation correctness;
- correctness of canonical `SemanticForm` serialization;
- source-to-Core subject resolution;
- truth, adequacy, or competence of an accepted equality/succession/correspondence relation;
- pointer, SSA, object, storage, boundary, or Systems subject correspondence beyond imported Certified predecessors;
- Haskell/GHC/runtime correctness; or
- diagnostics beyond their checked decision routing.

The implementation-refinement claim is only that the semantic EFF-001/002 admission order is production-bound to the exact extracted kernel while concrete representation and predecessor facts remain explicit trusted boundaries.

## Closeout criterion

`PHIL-EFFECT-SUBJECT-001` may move to `Implementation Refined` only when one exact-head CI run verifies all of the following together:

- the Certified and implementation Rocq proofs compile;
- fresh extraction is byte-identical to `src/EffectSubjectKernel.hs`;
- the exact kernel hash above matches;
- direct extracted-kernel controls pass;
- the bound `src/Phil/Core/Effect.hs` strict-typechecks with `-Wall -Werror`; and
- the unchanged EFF-001/002 callable-effect corpus remains green.
