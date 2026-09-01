# Provider Lineage Target Production Binding v1

This closeout binds the already-staged `PHIL-PROV-LINEAGE-TARGET-001` decision surface to the exact Rocq-extracted Haskell kernel.

## Exact kernel

`src/ProviderQualificationLineageTargetKernel.hs` is checked in byte-for-byte from staging run `33482739677` (#6). Its SHA-256 is:

`829e98d3b1653b0f4ca1a3fd64f570206df0a05e5500467d82f13a75a4d0f030`

CI fresh-extracts the kernel from `ProviderQualificationLineageTargetImplementationExtraction.v`, checks that digest, and requires byte identity with the checked-in production kernel.

## PROV-013 binding

`checkProviderCrossTargetSemanticReuse` reflects the concrete Haskell facts into `decideTargetReuseByFacts` and maps its ordered failure constructors back to the existing `ProviderCrossTargetReuseError` API. The two Certified semantic-claim gates intentionally map to the pre-existing combined `TargetReuseRequiresSemanticImplementationClaim` diagnostic. Claim/interface/implementation mismatches, missing target-specific translation evidence, and equal target profiles retain their prior payloads.

Canonical `SemanticForm` serialization and target-evidence revision construction remain native representation bridges; the semantic admission decision is kernel-owned.

## PROV-014 binding

`checkProviderAdmissionApplicability` reflects the accepted-admission bit and nineteen exact equality facts into `decideAdmissionApplicabilityByFacts`. Every kernel failure constructor maps to the same existing diagnostic class and expected/actual payload as the former ordered `requireEqual` chain.

Exported symbols remain deliberately absent from the semantic decision, matching the Certified theorem: symbol rename alone is nonsemantic.

## Residual boundary

This closeout does not mechanize canonical serialization/hashing, concrete `Text`/`Set` representation equality, or truth/completeness of translation, artifact/profile/ABI, target-assumption, and realization evidence. Those remain the explicit correspondence/evidence boundaries already recorded by the Certified obligation.
