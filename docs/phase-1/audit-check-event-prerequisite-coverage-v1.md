# Phase 1 audit: check-event prerequisite coverage

Status: focused defensive proof-correspondence tranche following the 23 September 2026 support-producer review. This continues the existing `D-CERT-SUPPORT-01` / prerequisite-completeness work; it does not create a new canonical finding.

## Audit observation

The independent support-producer replay established a route where a checked root is discharged by definition while a runtime-bound prerequisite remains part of the original check event. The handoff retains both nodes, but there is no parent decision certificate whose `PrerequisiteFact` traversal could name that child.

That does **not** refute `CertificateSupportPreserved`. The existing theorem is intentionally conditional on a prerequisite already being named by a certificate. A certificate-free disposition can therefore satisfy the theorem vacuously while still leaving a mandatory event prerequisite outside the modeled support domain.

## Proof slice

`proof/Phil/Assurance/CheckEventPrerequisiteCoverage.v` makes that missing domain premise explicit without changing `PrerequisiteSupport.v`.

The model separates:

- the complete mandatory prerequisite domain of one emitted check event;
- the existing certificate-prerequisite relation;
- an explicit operation/prerequisite relation for requirements that do not arise from a decision certificate; and
- the final support relation consumed downstream.

The central theorem proves that every mandatory event prerequisite reaches final support when:

1. certificate-named prerequisites satisfy the existing `CertificateSupportPreserved` contract;
2. explicit operation prerequisites also preserve support; and
3. every mandatory event prerequisite is accounted for by one of those two routes.

A negative witness models the certificate-free observation: certificate support is preserved vacuously, yet event-level support is incomplete because neither route accounts for the mandatory child. A positive witness shows the same certificate-free shape succeeding when an explicit operation/prerequisite relation carries the child into final support.

## Native correspondence boundary

This is a bounded proof model, not extraction of Haskell and not an implementation repair. The audit handoff identifies the concrete correspondence work that remains:

- derive the mandatory event-prerequisite domain from the actual checked result rather than reconstructing it from normalized pending-map entries;
- preserve stable IDs, original requirement/type, logical subject or occurrence, origin, scope and required point;
- route certificate-free prerequisites through a documented operation-use/prerequisite or complete scoped-inventory path;
- preserve selected runtime/export policy without treating declaration of a runtime check as execution; and
- require the actual final consumer to use the resulting support relation.

The production adapter and disposition routing remain visible premises. This PR does not claim that current Haskell already establishes `EventPrerequisiteAccountedFor` or `OperationSupportPreserved`.

## Boundaries

Proof/docs/workflow only. No production Haskell, resource ownership, residual interpretation, numeric adapters, native lowering, LLVM, packaging or Phase 1 trusted-computing-base boundary changes.

This slice deliberately does not close the separate direct named-evidence authority connection or the full `ValueResult`-to-resolved-forest binding problem from the same audit handoff. Those remain successor work or implementation-lane work as appropriate.
