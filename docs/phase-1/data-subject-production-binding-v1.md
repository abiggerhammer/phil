# Phase 1 data subject production binding v1

This closeout binds the already-Certified `PHIL-DATA-SUBJECT-001` DATA-012 checker to the exact representation-neutral decision kernel staged in #463.

## Exact extracted kernel

Production checks in:

- `src/DataSubjectKernel.hs`

The required SHA-256 is:

`b4b03eaab273225b39e50f080ff01fbafd82644b03aebd44f2589742161f424a`

The closeout workflow fresh-extracts `DataSubjectKernel.hs` from `proof/Phil/Core/DataSubjectImplementationExtraction.v`, compares it byte-for-byte with the checked-in production copy, and rejects any hash drift.

## Production-bound decisions

`src/Phil/Core/DataSubjectTransport.hs` retains concrete representation work and supplies primitive facts to three extracted decisions.

### 1. Common update prerequisites

The extracted kernel owns this order:

1. predecessor consumed;
2. replacement constructed;
3. predecessor identity is stable;
4. replacement identity is stable;
5. stable subject kinds match;
6. the evidence template mentions its subject binder;
7. evidence is bound to the exact predecessor subject;
8. the evidence subject identity is stable; and
9. the evidence subject kind matches the predecessor kind.

Production retains native `RefTerm` stable-id decoding, equality, proposition-mention detection, and public diagnostic reconstruction. The final two Certified facts are redundant once exact evidence-subject equality with an already-stable predecessor has passed, but production reflects them explicitly and fails closed if that representation invariant were ever violated.

### 2. Same/changed subject transport mode

The extracted kernel owns the exact presence rule:

- same subject + no transport: proceed;
- same subject + transport: reject as spurious;
- changed subject + no transport: require transport;
- changed subject + transport: proceed to exact transport validation.

Concrete `Maybe DataSubjectTransport`, `RefTerm` equality, result-evidence reconstruction, and diagnostic payloads remain native.

### 3. Exact transport validation

For a changed subject with explicit transport, the extracted kernel owns this order:

1. accepted transport disposition;
2. nonempty relation revision;
3. exact evidence reference;
4. exact predecessor identity;
5. exact replacement identity;
6. exact normalized source proposition; and
7. exact normalized target proposition.

Production retains concrete `Text`, `RefTerm`, and `Proposition` representation/equality, proposition normalization/substitution, and exact public diagnostics. The disposition rejection reason is also retained natively and is returned unchanged.

## Preserved boundaries

This production binding does **not** claim to verify:

- `RefTerm`, `Proposition`, `Text`, `Name`, or `Maybe` representation correctness;
- source-to-Core stable-subject elaboration;
- correctness of stable-id kind decoding;
- proposition substitution or normalization;
- truth or competence of accepted copy/succession relations;
- pointer, SSA, object, boundary, or Systems subject correspondence;
- Haskell/GHC/runtime correctness;
- diagnostics beyond their checked decision routing; or
- any resource-elimination or boundary-discharge obligation owned by predecessor rows.

The implementation-refinement claim is only that the final semantic decision order for the Certified DATA-012 subject-update/transport contract is production-bound to the exact extracted kernel, while those concrete representation and predecessor facts remain explicit trusted boundaries.

## Closeout criterion

`PHIL-DATA-SUBJECT-001` may move from `Discharged / Certified` to `Discharged / Implementation Refined` only when an exact-head CI run verifies all of the following together:

- the Certified and implementation Rocq proofs compile;
- fresh extraction is byte-identical to `src/DataSubjectKernel.hs`;
- the exact kernel hash above matches;
- direct extracted-kernel controls pass;
- the bound `DataSubjectTransport.hs` strict-typechecks with `-Wall -Werror`; and
- the unchanged DATA-012 19-case correspondence corpus remains green.
