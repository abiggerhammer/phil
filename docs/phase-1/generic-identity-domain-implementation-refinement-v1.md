# Generic identity argument-domain implementation refinement v1

This tranche begins `PHIL-GEN-ID-IMPL-001`, the Implementation Refined migration for the already Discharged / Certified `PHIL-GEN-ID-001` / GEN-009 and GEN-010 semantics.

It is deliberately a proof/correspondence staging slice. Production behavior is unchanged.

## Reused executable kernel

The certified generic identity model defines semantic-argument domain validity as duplicate-freedom of argument keys:

`argumentDomainValid arguments := NoDup (map fst arguments)`.

The generic instantiation refinement already produced and checked in an equality-parametric executable no-duplicate key checker, `GenericInstantiationDomainKernel.keyListNoDupb`, whose Rocq source theorem states that it returns `true` exactly for `NoDup` lists whenever the supplied equality predicate reflects actual equality.

Rather than generate a second copy of the same algorithm, this tranche proves that the existing executable checker specializes exactly to `GenericIdentity.argumentDomainValid`.

The specialization uses `Nat.eqb` in the normalized proof model. The eventual production bridge will use derived Haskell `(==)` on concrete `GenericStaticParameterKey` values; correctness of that concrete equality remains an explicit primitive representation/runtime foundation.

## What this tranche establishes

`proof/Phil/Core/GenericIdentityDomainImplementation.v` proves:

- executable argument-domain acceptance iff Certified `argumentDomainValid`;
- duplicate semantic-argument keys reject; and
- two distinct-key argument orders are both accepted by the domain checker, preserving the precondition needed for the Certified order-nonsemantic identity theorem.

## Production binding still required

A later binding slice must route `deriveGenericApplicationIdentity` duplicate-domain acceptance through the checked-in `GenericInstantiationDomainKernel.keyListNoDupb`, while preserving the current first-duplicate diagnostic and failing closed on any kernel/concrete disagreement.

The remaining identity correspondence boundary is intentionally explicit: `GenericApplicationIdentity` uses concrete `DeclarationKey`, `InterfaceRevision`, and canonical `Map GenericStaticParameterKey SemanticForm`; ordinary derived Haskell equality and `Map` extensional equality/canonicalization are the representation foundation corresponding to the Certified `sameApplication` relation. `deriveGenericDischargeLineage` is a direct constructor preserving the application identity while adding definition revision and discharge evidence. Architecture occurrence generativity remains the responsibility of the already separate architecture/instance layer.

A green staging run earns Mechanized evidence for this bounded argument-domain correspondence only. It does not yet make `PHIL-GEN-ID-IMPL-001` Implementation Refined.
