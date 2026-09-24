# Phase 1 audit remediation: exact same-event subject endpoints

This implementation-side remediation continues `D-RES-SUPPORT-01` / `D-RES-TREE-01` after the actual evidence-use inventory and residual-free producer-origin boundary.

## Boundary

The accepted Phase-1 chain now starts from the authentic returned `ValueResult` and its complete ordered `valueResultEvidence` inventory. Every `RefVar` occurrence in every actual subject-bearing evidence use must obtain a competent semantic endpoint before `closeOriginalCheckEventBundle` can enter the immutable final manifest consumer.

The endpoint authority for this scoped route comes only from durable logical subject support captured with actual `EvidenceResidual` records and validated against the exact retained obligation record plus origin, scope, and required point. A later or ambient `ResourceContext` binding is never consulted for endpoint authority.

This gives the supported Phase-1 path an event-qualified subject key:

`validated producer event + exact durable logical subject name/type`.

The event qualification contains the validated `ResidualSpec` and the ordered residual IDs actually returned by the checker. It is deliberately scoped to this original event and final-closure call; it is not presented as a global execution nonce or a generalized Phase-2 subject registry.

## Transport restriction

This boundary supports only unchanged subject identity inside one exact original event. Source and target endpoints are therefore equal. The implementation does **not** infer a rebase from equal source spelling, equal types, proposition text, or a later replacement binding.

If Phase 1 would require a distinct target subject, this route fails to provide that transport rather than manufacturing it. A future generalized path may admit an explicit checked rebase, but that is not added here.

## Final consumer integration

Endpoint reflection is not an optional reporting helper. `closeOriginalCheckEventBundle` first derives the exact original-event handoff, then requires complete endpoint coverage for the same actual evidence inventory, and only then invokes `closeVerificationBundleWithHandoff`.

A subject-bearing actual use with no exact producer-bound logical support therefore fails closed. Missing endpoint metadata is never interpreted as evidence that the use was closed. Genuinely closed uses remain classified by the existing structural `actualEvidenceUseInventory` rule and acquire no fabricated subject identity.

## Ownership and evidence authority

Durable logical subject support remains separate from resource ownership and proof authority. A consumed Affine/Linear owner stays consumed. The endpoint adapter reads retained logical support but does not alter `ResourceContext`, loans, or unrestricted evidence authority. Likewise, certificate and direct named-evidence authority continue through their existing exact fail-closed paths.

## Permanent controls

`test/Phase1AuditEvidenceSubjectEndpointsMain.hs` covers:

- ordered endpoint coverage for every subject of a two-subject actual residual;
- producer-event qualification using the exact actual residual inventory and validated metadata;
- a consumed Linear subject retaining a logical endpoint while its owner remains absent;
- a later same-spelled ambient replacement being unable to retarget the old endpoint;
- a subject occurrence absent from exact producer support failing closed; and
- incorrect event metadata failing before endpoint authority is granted.

The dedicated workflow also reruns the existing original-event final-closure regression unchanged, including the valid `(5-3)==(5-3)` control and final manifest support-edge checks.

## Non-claims

This is a bounded implementation correspondence repair, not a global subject-ID framework, a cross-event rebase mechanism, a source-pre-normalization occurrence proof, or a whole-release certification. Numeric source/environment/result-subject adapters remain a separate implementation slice. Rocq proof/refinement work is unchanged, and LLVM remains inside the Phase-1 trusted computing base.
