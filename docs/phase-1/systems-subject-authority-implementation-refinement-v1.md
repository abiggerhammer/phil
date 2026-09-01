# Systems Subject Authority Implementation Refinement v1

`PHIL-SYS-SUBJECT-AUTH-001` is already Certified. This tranche stages only its representation-neutral executable decision surface; production behavior is unchanged.

## Extracted semantic decisions

`SystemsSubjectAuthorityImplementation.v` reflects the cumulative SYS-004--006 theorem family into five ordered decision kernels.

### SYS-004 subject correspondence

`decideSubjectStageByFacts` admits only checked semantic subject correspondence and requires a nonempty Systems-value set, existence of every referenced Systems value, exclusive value-to-subject binding, and exact validity scope. Runtime representation coincidence is a distinct rejecting constructor.

### SYS-005 provider call correspondence

`decideProviderCallStageByFacts` composes successful subject-stage verification with exact provider-call binding, selected admission, interface, operation, implementation entry, and call-site domain. Runtime-symbol-only inference is a distinct rejection.

### SYS-006 effect and authority use

`decideEffectUseByFacts` is the direct executable form of Certified `effect_use_admitted`: an effect already in the source bound is admitted; source-observable widening rejects; an internal realization-only effect outside the source bound requires explicit realization refinement.

`decideAuthorityExerciseByFacts` is the direct executable form of Certified `authority_exercise_admitted`: public authority must be declared; internal authority must be independently qualified and carry the exact disposition.

`decideAuthorityEffectStageByFacts` composes successful provider-stage verification with exact surface/use domains, public authority nonescape/completeness, qualified internal assignments, and admission of all concrete effect and authority uses.

The Rocq correspondence theorems build normalized Certified fact records from the reflected Boolean facts. Predecessor-stage acceptance is an explicit compositional premise rather than being hidden inside a representation choice.

## Representation boundary

The staged kernel deliberately begins after concrete representation work. These remain explicit Haskell/correspondence boundaries:

- StageContract revision construction and canonical serialization;
- concrete `Text`, key, revision, `Map`, `Set`, and list equality/enumeration;
- function/value existence lookup and global reverse-binding construction;
- provider selection, qualification/admission, semantic-surface, effect-bound, and authority-assignment construction;
- exact diagnostic payload construction and traversal order;
- truth/completeness of provider, authority, target, runtime, assumption, and realization evidence; and
- Rocq extraction/toolchain and Haskell runtime correctness.

Production `SubjectCorrespondence.hs`, `ProviderCallCorrespondence.hs`, and `AuthorityEffectCorrespondence.hs` are unchanged in this staging PR. A separate closeout must check in the exact extracted kernel and bind the native traversal decisions before the ledger can move from `Discharged / Certified` to `Discharged / Implementation Refined`.

## Staging verification

The existing `Phase 1 Systems Subject Authority Proofs` workflow is extended to:

- compile the Certified proof plus implementation-correspondence proof;
- fresh-extract `SystemsSubjectAuthorityKernel.hs`;
- strict-typecheck and execute 32 direct decision controls;
- strict-typecheck the unchanged SYS-004--006 production chain and tests;
- rerun the unchanged cumulative 31-case corpus; and
- record proof, extraction, production, test, harness, and staging-document identities.
