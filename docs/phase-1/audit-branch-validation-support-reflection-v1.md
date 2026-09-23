# Phase 1 audit: validation-decision support reflection

Status: focused defensive proof-correspondence tranche for `P-BRANCH-SUPPORT-REFLECTION-01`, following the merged implementation repair in #1350.

## Question

The branch-evidence proof model already requires every logical subject carried across scope exit to survive or be explicitly rebased. That theorem is only useful if the native producer reports every subject that a later elimination can expose.

Before #1350, `DecisionShape` contributed no support. A `ValidationDecision claim context subject` could therefore cross branch exit even though its accepted arm later materialized `TyValidated claim context subject`.

The implementation repair now makes the relevant native relationship explicit:

- `decisionSubjects (ValidationDecision _ context subject)` reports `context` and `subject`;
- the accepted branch of `bindDecisionPattern` materializes `TyValidated claim context subject`; and
- `freeTypeSubjects (TyValidated _ context subject)` reports the same two logical subjects.

This slice proves the normalized correspondence for that route and connects it to `Phil.Surface.BranchEvidenceSupport`.

## Proof slice

`proof/Phil/Surface/BranchValidationSupportReflection.v` distinguishes:

- the repaired native support produced for a validation decision;
- the support later exposed by materialized validated evidence; and
- the old empty `DecisionShape` support that characterized the defect.

It proves that:

1. repaired validation-decision support reflects every subject later exposed by `TyValidated`;
2. the previous empty support is not reflection-complete, even though an empty support list is vacuously exportable by the generic scope model;
3. when both context and subject survive scope exit, the repaired support exports normally;
4. when the validated subject does not survive, the repaired support cannot export; and
5. allocating a fresh subject with the same source spelling cannot authorize the removed logical subject.

The last two facts reuse the existing `ExportSupport` / `ExportSubject` relation rather than inventing a second scope rule.

## Native correspondence boundary

The proof file is a bounded correspondence model, not extraction of Haskell. Its native mapping is the exact field relationship now present in `src/Phil/Surface/Check/Engine.hs` after #1350:

- producer: `decisionSubjects` for `ValidationDecision`;
- consumer/elimination: accepted `bindDecisionPattern` arm;
- materialized support walk: `freeTypeSubjects` for `TyValidated`;
- scope gate: the existing `pruneScopedPath` support check.

The proof does not claim that all `DecisionKind` constructors are covered. Digest, recognition, provider and callable decision support remain successor correspondence work under `P-BRANCH-SUPPORT-REFLECTION-01`.

## Boundaries

This change is proof/docs/workflow-only. It does not modify Surface checking, resource ownership, residual-obligation interpretation, numeric adapters, LLVM, native lowering, or any Phase 1 trusted-computing-base boundary.

In particular it does **not** close `D-RES-SUPPORT-01`, `D-NUM-ENV-ADMISSION-01`, or `D-NUM-RESULT-SUBJECT-01`, and it does not restore consumed owners merely to preserve logical interpretation.
