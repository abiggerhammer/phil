# PHIL-AUD residual-free event origin — final-closure supported boundary

Lane: impl-audit

## Finding

The actual-use inventory repair preserves every evidence use returned by the checker, including checked closed facts and carried binding evidence. For a residualizing check, the returned `EvidenceResidual` record and retained obligation state also preserve the `ResidualSpec` metadata needed to validate the original event. A residual-free `ValueResult` does not retain that historical event identity.

That distinction matters at the final accepting operation. Before this repair, `resolveOriginalCheckEvent` could legitimately be used as a fresh diagnostic re-resolution of a residual-free result under caller-supplied event metadata, but `closeOriginalCheckEventBundle` could then treat the same caller-supplied metadata as if it established the historical producer event. Two different `ResidualSpec` values can label the same residual-free result, so presence of a spec at final closure is not producer provenance.

## Repair

`closeOriginalCheckEventBundle` now enforces an explicit Phase 1 supported boundary: the bounded original-event final-closure route requires at least one `EvidenceResidual` emitted by the actual checker. The existing resolver then validates that emitted obligation's origin, scope, required point and identity against the supplied `ResidualSpec` before any manifest closure is attempted.

If the returned result is residual-free, final closure rejects with `OriginalCheckEventClosureProducerAssociationRequired` before examining caller-supplied bundle, policy, ledger or selection data. This does not claim that residual-free checks are invalid. It says only that this final-closure adapter lacks a durable historical producer association for them. A future producer-bound event object can widen the supported boundary without weakening this rule.

Low-level `resolveOriginalCheckEvent` remains available for fresh checking and diagnostic replay. Therefore valid closed checks such as `(5-3)==(5-3)` and valid carried facts remain valid and statically resolvable; they simply cannot acquire historical final-use identity from a later arbitrary `ResidualSpec`.

## Regression

`Phase1AuditResidualFreeEventOriginMain.hs` checks that:

1. a genuine residual-free closed check remains valid and statically resolvable;
2. its original caller-supplied spec cannot by itself authorize final closure;
3. a different caller-supplied spec cannot relabel the same returned result into another accepted historical event;
4. genuine carried binding evidence remains valid and statically resolvable; and
5. carried residual-free evidence likewise cannot acquire final event origin from caller metadata alone.

The dedicated workflow also reruns `Phase1AuditOriginalEventForestMain.hs`, whose positive final-closure case contains a genuine emitted residual prerequisite. That preserves the already-landed original-event forest/final-consumer behavior and confirms this restriction is not a blanket rejection of products, refinements, modes, or residualizing events.

## Boundaries

This repair changes no resource ownership or loan state, restores no affine/linear owner, changes no product definitional equality, and does not require refinement predicates to be true at formation. It does not modify Rocq proofs. It is a scoped native Phase 1 provenance restriction corresponding to the audit handoff's requirement that residual-free producer origin not be inferred from caller-supplied event-shaped metadata.
