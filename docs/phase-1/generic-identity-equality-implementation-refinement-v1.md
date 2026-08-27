# Phase 1 Generic Identity Equality Implementation Refinement v1

This tranche continues `PHIL-GEN-ID-IMPL-001` after the semantic-argument domain checker was proved and production-bound in #292/#296.

## Scope

The remaining Certified GEN-ID identity semantics are intentionally represented as native equality facts rather than serialized Rocq identities.

`proof/Phil/Core/GenericIdentityEqualityImplementation.v` defines an executable three-fact decision for ordinary generic application identity:

1. declaration key equality;
2. exact public interface revision equality; and
3. extensional semantic-argument equality.

It proves that the executable decision accepts exactly `GenericIdentity.sameApplication` whenever those facts reflect the corresponding Certified propositions.

The same file defines a separate three-fact discharge-lineage decision:

1. semantic application equality;
2. definition revision equality; and
3. accepted discharge-evidence identity equality.

It proves that this decision accepts exactly the extensional discharge-lineage relation and separately proves that changing either definition revision or discharge evidence rejects lineage equality.

## Representation boundary

Production uses richer representations than the normalized Rocq model:

- `DeclarationKey` and `InterfaceRevision` are concrete Haskell identities;
- semantic arguments are canonical `Map GenericStaticParameterKey SemanticForm` values;
- discharge evidence is represented by the complete accepted disposition map rather than one normalized `nat`;
- architecture occurrence identity remains a separate `InstanceKey` / architecture-layer concern.

The extracted kernel therefore consumes only booleans supplied by those native equality relations. No lossy serialization into proof-model `nat` values is introduced.

Derived/native equality correctness for keys, revisions, `SemanticForm`, canonical `Map` equality, and the interpretation of the full disposition map as discharge-evidence identity remain explicit representation/runtime foundations.

## Staging criterion

This PR does not change production behavior. A green staging run establishes a Mechanized equality tranche only.

The later production-binding closeout will check in the exact extracted kernel, route `Eq GenericApplicationIdentity` and `Eq GenericDischargeLineage` through it using native equality facts, preserve `Ord` consistency, rerun the unchanged GEN-009/010 corpus, and only then upgrade `PHIL-GEN-ID-IMPL-001` to `Discharged / Implementation Refined`.
