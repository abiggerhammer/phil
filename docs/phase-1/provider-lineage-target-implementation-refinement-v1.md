# Provider Lineage Target Implementation Refinement v1

`PHIL-PROV-LINEAGE-TARGET-001` is already Certified. This tranche stages only its bounded executable decision surface; production behavior is unchanged.

## Extracted semantic decisions

`ProviderQualificationLineageTargetImplementation.v` reflects the Certified PROV-013/014 theorem family into two ordered decision kernels.

### PROV-013 cross-target reuse

`decideTargetReuseByFacts` checks, in production order:

1. semantic qualification layer;
2. semantic implementation subject;
3. prior target evidence claim revision;
4. prior required interface;
5. prior semantic implementation;
6. prior translation evidence;
7. new target evidence claim revision;
8. new required interface;
9. new semantic implementation;
10. new translation evidence; and
11. distinct target profiles.

`reflected_target_reuse_decision_exact` proves acceptance exactly equivalent to Certified `CrossTargetSemanticReuse`.

### PROV-014 concrete admission applicability

`decideAdmissionApplicabilityByFacts` checks the accepted admission plus the nineteen exact applicability/selection equalities required by Certified `AdmissionApplicable`, in the same order as the production checker.

`reflected_admission_applicability_decision_exact` proves acceptance exactly equivalent to Certified `AdmissionApplicable`.

Exported symbol metadata is deliberately absent from the decision surface, matching the Certified theorem and the existing implementation contract that symbol names are nonsemantic metadata.

## Representation boundary

The staged kernel consumes already-reflected Booleans. The following remain explicit Haskell/correspondence boundaries:

- canonical `SemanticForm` serialization and content-addressed revision construction;
- concrete `Text`, `Set`, and revision-wrapper equality;
- truth/completeness of translation-validation, target-assumption, realization, artifact/profile, and ABI evidence;
- construction of exact diagnostic payloads; and
- extraction/Rocq/toolchain correctness.

Production `ProviderQualificationTargetReuse.hs` and `ProviderQualificationApplicability.hs` are unchanged in this staging PR. A separate closeout must check in the exact extracted kernel and bind those production decisions before the ledger can move from `Discharged / Certified` to `Discharged / Implementation Refined`.

## Staging verification

The existing `Phase 1 Provider Lineage Target Proofs` workflow is extended to:

- compile the Certified target proof and implementation-reflection proof;
- fresh-extract `ProviderQualificationLineageTargetKernel.hs`;
- strict-typecheck the extracted kernel;
- execute 33 direct controls covering every success/failure gate;
- strict-typecheck the unchanged PROV-013/014 production modules;
- rerun the unchanged correspondence tests and existing proof certification; and
- record proof, extraction, production, test, harness, and staging-document identities.
