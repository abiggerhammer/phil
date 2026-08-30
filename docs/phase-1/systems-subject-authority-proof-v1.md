# Phase 1 Systems subject/provider/authority proof v1

Status: Rocq semantic certification tranche for `PHIL-SYS-SUBJECT-AUTH-001` over the already implemented and tested SYS-004–006 cumulative Systems/StageContract chain.

## Certified semantic boundary

`proof/Phil/Core/SystemsSubjectAuthority.v` models the semantic gates owned by the existing cumulative verifier stack:

1. **SYS-004 subject correspondence**
   - a Systems value may carry a source semantic subject only through an explicit checked subject relation;
   - runtime representation/pointer/storage coincidence is not semantic subject identity;
   - every represented Systems value must exist;
   - one Systems value may not be assigned to multiple distinct stable source subjects; and
   - the subject relation retains an explicit validity scope.

2. **SYS-005 provider-call correspondence**
   - the SYS-004 subject stage must already verify;
   - a provider call is justified by an exact selected admitted provider occurrence, required interface, semantic operation, and implementation entry;
   - the represented call-site/link domains are exact; and
   - a matching runtime symbol/signature alone never establishes semantic provider correspondence.

3. **SYS-006 authority/effect correspondence**
   - the SYS-005 provider-call stage must already verify;
   - qualified provider surfaces and represented uses have exact domains;
   - public authority cannot escape the selected client-visible surface and cannot disappear from the operation assignment;
   - internal authority must already be qualified with the exact disposition used by the Systems operation;
   - a source-observable effect cannot be widened by target realization; and
   - an internal realization-only effect outside the source effect bound requires an explicit realization refinement.

The aggregate theorem requires all three layers simultaneously. Therefore successful bounded SYS-004–006 correspondence preserves semantic subject identity, exact selected-provider identity, and public/internal authority/effect non-widening across the cumulative Systems stage.

## Existing production correspondence

This PR does not change production Haskell or tests. Its correspondence target is the existing cumulative chain:

- `src/Phil/Systems/SubjectCorrespondence.hs`
- `src/Phil/Systems/ProviderCallCorrespondence.hs`
- `src/Phil/Systems/AuthorityEffectCorrespondence.hs`

The dedicated workflow also reruns the unchanged focused conformance corpus:

- `test/Phase1SubjectCorrespondenceMain.hs` — 8 SYS-004 cases
- `test/Phase1ProviderCallCorrespondenceMain.hs` — 13 SYS-005 cases
- `test/Phase1AuthorityEffectCorrespondenceMain.hs` — 10 SYS-006 cases

Total: **31 unchanged cases**.

## Certified predecessors

The normalized theorem composes with the already Certified semantic predecessors named by the ledger:

- `PHIL-PROV-QUAL-001`
- `PHIL-AUTH-ATTEN-001`
- `PHIL-DATA-SUBJECT-001`
- ADR-010, ADR-014, and ADR-015 remain governing design boundaries.

No predecessor theorem is widened by this tranche.

## Residual boundary

This is semantic certification, not implementation refinement. The following remain explicit assumptions or correspondence boundaries:

- Rocq kernel/toolchain correctness;
- concrete Haskell Text/key/revision equality and construction;
- `Map`/`Set`/list enumeration, canonicalization, and extensional semantics;
- concrete source-subject to Systems-value enumeration;
- truth and competence of selected provider qualification/admission artifacts;
- concrete callable/provider/authority surface construction;
- exact diagnostic reconstruction and rejection precedence;
- Haskell implementation equivalence to the normalized Rocq model;
- concrete target/runtime/backend behavior; and
- truth of external assumptions or realization evidence.

Physical pointer, storage, ABI, or runtime-symbol coincidence remains intentionally insufficient to establish semantic identity.

Base: `51808e8095fb80d7fd12c9db1938e3ee5e3a1ca3`.
