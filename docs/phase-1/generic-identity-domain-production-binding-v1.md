# Generic identity domain production binding v1

This slice binds the already-mechanized `PHIL-GEN-ID-IMPL-001` semantic-argument domain rule into production without changing the broader GEN-ID identity model.

## Bound rule

Certified `PHIL-GEN-ID-001` defines a valid semantic-argument domain as `NoDup (map fst arguments)`. PR #292 proved that the reusable equality-parametric extracted checker `GenericInstantiationDomainKernel.keyListNoDupb`, specialized with exact equality, accepts exactly those domains.

`Phil.Core.Generic.deriveGenericApplicationIdentity` now delegates duplicate-domain acceptance to that extracted checker over the concrete `GenericStaticParameterKey` sequence. Handwritten Haskell remains responsible only for reconstructing the existing first-duplicate diagnostic and materializing the canonical `Map` representation.

If the extracted decision and concrete normalization disagree, production fails closed with `GenericApplicationIdentityKernelBridgeMismatch`.

## Preserved behavior

- duplicate semantic-argument keys still reject with the first duplicate key;
- argument traversal order remains nonsemantic after canonical `Map` normalization;
- declaration key and exact interface revision remain fields of ordinary application identity;
- discharge evidence and definition revision remain downstream lineage rather than ordinary application identity;
- architecture occurrence generativity remains in the architecture/instance layer.

## Remaining refinement boundary

This binding closes only the executable argument-domain seam. The full `PHIL-GEN-ID-IMPL-001` closeout still requires explicit mechanical correspondence between production canonical `Map` equality and Certified `argumentsEquivalent` / `sameApplication`, plus the separate discharge-lineage correspondence. Derived Haskell `Eq`/`Ord`, `Map` canonicalization, `SemanticForm` equality/serialization, and architecture `InstanceKey` derivation remain primitive representation/runtime foundations unless separately refined.
