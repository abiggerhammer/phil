# Phase 1 generic identity implementation refinement

`PHIL-GEN-ID-IMPL-001` closes the mechanical correspondence between the Certified GEN-009/GEN-010 identity model and production `Phil.Core.Generic`.

The refinement is split into two executable seams.

## Semantic-argument domain

#292 proved that the reusable extracted equality-parametric `keyListNoDupb` checker accepts exactly the Certified `argumentDomainValid` predicate. #296 bound `deriveGenericApplicationIdentity` to that checker while preserving the first-duplicate diagnostic and failing closed on checker/normalizer disagreement.

## Application and discharge-lineage equality

#298 proved and extracted `GenericIdentityEqualityKernel.hs`. The kernel does not serialize Phil identities. It accepts only native equality facts:

- application declaration key equality;
- exact interface revision equality;
- canonical semantic-argument map equality;
- semantic application equality within discharge lineage;
- definition revision equality; and
- accepted disposition-map equality as discharge-evidence identity.

The production binding replaces the derived `Eq` instances for `GenericApplicationIdentity` and `GenericDischargeLineage` with calls to the extracted decisions. Native Haskell equality computes the primitive representation facts; Rocq owns their logical conjunction and the semantic-application/discharge-lineage separation.

`Ord` remains structurally derived. The closeout harness checks that the kernel-backed equality agrees with `Ord == EQ` on representative equal identities as well as independently exercising every equality component.

## Explicit trust boundaries

The following remain primitive representation/runtime foundations rather than being serialized through the normalized Rocq model:

- `DeclarationKey`, `InterfaceRevision`, and `DefinitionRevision` equality;
- `GenericStaticParameterKey`, `SemanticForm`, and `GenericRequirementDisposition` equality;
- canonical `Data.Map.Strict` extensional equality and ordering;
- `SemanticForm` serialization and collision assumptions; and
- architecture occurrence / `InstanceKey` derivation, which remains a separate generativity obligation.

The final workflow fresh-extracts the equality kernel and compares it byte-for-byte with `src/GenericIdentityEqualityKernel.hs`, typechecks the bound production path under `-Wall -Werror`, reruns the unchanged seven-case GEN-009/010 corpus, and runs the direct equality-component harness. Only that exact-head green run is sufficient to mark `PHIL-GEN-ID-IMPL-001` Discharged / Implementation Refined.
