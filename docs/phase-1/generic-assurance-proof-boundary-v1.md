# PHIL-ASSURE-GENERIC-001 proof boundary

This certification owns the reusable conditional-assurance relation for generic bodies.

## Certified here

- One reusable body-assurance artifact is bound to the exact generic declaration, interface revision, definition revision, public requirement set, public requirement revisions, and body evidence artifact identity.
- An ordinary application may reuse that body only when its exact declaration/interface/definition coordinates match.
- The current public requirements and their revisions must match the body contract exactly.
- The application's requirement-discharge lineage must already be an accepted `PHIL-GEN-INST-001` instantiation with exact disposition-domain coverage.
- Every public requirement therefore has one explicit admitted disposition, and no unexposed requirement receives one.
- Under the strict generic-instantiation policy, body reuse cannot introduce `AssumptionDependent` or `Exported` dispositions.
- Distinct ordinary application identities may share the exact same body assurance while retaining distinct exact discharge lineages.
- Replacing one application's discharge lineage cannot rekey the shared body artifact or its sibling applications.
- Backend/monomorphization/realization identity is not part of source generic-body assurance identity.

## Imported predecessor competence

This proof does not re-prove:

- structural/public generic requirement inference (`PHIL-GEN-REQ-001`);
- exact generic instantiation/disposition validity (`PHIL-GEN-INST-001`);
- proposition/evidence truth or provider-refinement soundness;
- validity-scope applicability (`PHIL-ASSURE-SCOPE-001` / `PHIL-ASSURE-VALIDITY-001`);
- evidence-use authority (`PHIL-ASSURE-USE-001`); or
- policy authority for explicitly permitted assumptions/exports.

The reuse layer consumes those accepted predecessor facts; it cannot manufacture them.

## Production / representation boundary

Concrete `Text`, `Digest`, `Map`, `Set`, canonical requirement rendering, SHA-256/digest collision assumptions, artifact identity validation, and concrete `GenericDischargeLineage` representation remain Haskell/representation foundations. The implementation-correspondence proof models the production rejection order over native equality/domain facts, but this PR does not extract or production-bind a kernel.

Any later extracted-kernel production binding belongs to the separate implementation-refinement lane.
