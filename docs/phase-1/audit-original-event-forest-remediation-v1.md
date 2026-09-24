# PHIL-AUD original check-event forest remediation

This Haskell slice continues the open original-event/forest correspondence from `PHIL-AUDIT-20260923-CHECK-EVENT-SCOPE-CALLERS` and `PHIL-AUDIT-20260924-CONSUMER-ENDPOINT-COVERAGE`. It does not change the Phase 1 trusted computing base and does not modify Rocq.

## Problem

The Core value checker returns more information than the normalized pending-obligation map alone. A residualizing `ValueResult` retains the checked refinement type, the concrete subject term when one exists, the exact evidence-use inventory, the returned `CheckState`, the emitted obligations, and their durable logical-subject support.

Resolving each entry of `residualObligations` independently throws some of that event structure away. In particular, `(a-b)==(a-b)` can close definitionally while the subtraction definedness prerequisite remains residual. The map then contains the child but no parent record from which the final assurance relation can recover that the child was required to admit the original check event.

## Repair boundary

`Phil.Assurance.resolveOriginalCheckEvent` rebases the actual returned `ValueResult` onto the existing resolver without treating the pending map as the source of truth.

The adapter:

- derives the original instantiated proposition from the returned refined type and concrete subject term;
- validates every returned `EvidenceResidual` against the exact emitted obligation record and the `ResidualSpec` occurrence metadata;
- derives the temporary logical typing view only from the exact durable support captured for those returned residuals, without restoring ownership or mutating the returned resource state;
- resolves the original unnormalized event root through the existing resolver, so definitionally simplified parents regain their real prerequisite forest;
- requires every residual use to occur in that resolved forest;
- requires the forest's still-pending nodes to equal the returned residual-use inventory, so dropping a returned use cannot silently shrink the event; and
- checks each residual proposition against the resolved canonical proposition for the same exact obligation ID.

`handoffOriginalCheckEvent` then feeds that exact resolver tree into the existing immutable checker-to-ledger handoff. Certificate `EvidenceFact` identity remains explicit and fail-closed, and direct named evidence still uses the existing exact event/name authority attachment before final manifest closure.

This is an exact rebase of the real checker result, not a second hand-written obligation fixture. The caller-supplied `ResidualSpec` is checked against the emitted records and the resolved occurrence; a mismatched root occurrence or scope fails closed.

## Preserved behavior

The repair does not reject products, alter product definitional equality, require a refinement predicate to be inhabited at type formation, merge logical binders with ambient resource/proof names, or restore a consumed affine/linear owner. Ordinary valid arithmetic such as `(5-3)==(5-3)` remains statically valid. Existing runtime/export policy and stronger later static discharge remain available because the original event is resolved through the normal discharge policy rather than by freezing old disposition tags.

## Permanent replay

`Phase1AuditOriginalEventForestMain.hs` covers:

1. a definitionally discharged subtraction equality whose runtime prerequisite remains a parent-to-child handoff dependency;
2. a case where both root and child were returned as residuals but are rebased into one original event forest;
3. rejection of a mismatched occurrence/root ID;
4. rejection of mismatched scope metadata;
5. rejection when a returned residual use is removed while its pending node remains; and
6. preservation of fully static literal subtraction equality.

## Remaining correspondence

This slice supplies the previously missing `ValueResult`-to-resolved-forest transport. The live audit's separate final-accepting-entry question remains a distinct integration boundary: the concrete local/conditional/export accepting route must consume this event-derived handoff rather than fall back to an independently reconstructed pending-map subset. Existing `closeVerificationBundleWithHandoff` support/final-scope checks remain the downstream consumer to connect at that boundary.
