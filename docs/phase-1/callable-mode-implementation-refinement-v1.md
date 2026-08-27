# Phase 1 callable mode implementation refinement v1

This note stages the executable implementation correspondence for `PHIL-CALL-MODE-001` without changing production behavior.

## Certified surface

`proof/Phil/Core/CallableMode.v` already certifies three connected structural rules:

1. unrestricted captures may copy or move, while affine/linear captures must move;
2. the same restricted semantic occurrence may not be captured twice; and
3. closure structural mode is the least upper bound of captured modes under `Unrestricted < Affine < Linear`.

It also identifies moved restricted occurrences so the surrounding ownership checker can consume the predecessor occurrence.

## Executable seam

`CallableModeImplementation.v` exposes a representation-conscious kernel surface:

- `decideCallableCaptureTransfer mode transfer` owns transfer acceptance;
- `captureMovedRestrictedByMode mode transfer` owns restricted-move classification;
- `decideCallableDuplicateCapture sameOccurrence firstMode secondMode` owns duplicate-restricted rejection from a native occurrence-equality fact; and
- `closureStructuralModeFromModes modes` owns the closure-mode fold.

The duplicate checker deliberately accepts only `sameOccurrence : bool`. Concrete `CaptureOccurrenceKey` is `Text` in Haskell and remains a native identity representation; it is not serialized into the normalized Rocq model.

`Mode` and `CaptureTransfer` are finite semantic enums, so a later production binding may bridge them by total constructor mapping and fail closed if a representation round trip ever disagrees.

## Proved correspondence

The staging proof shows:

- extracted transfer acceptance iff the Certified `captureTransferAllowed` predicate is true;
- extracted moved-restricted classification equals Certified `captureMovedRestricted`;
- duplicate acceptance, when supplied `Nat.eqb` as the equality fact, iff Certified `duplicateCaptureAllowed` is true; and
- folding only the capture modes yields exactly Certified `closureStructuralMode` for the original captures.

## Production boundary

This PR leaves `src/Phil/Core/Callable.hs` unchanged. Its existing `Map` normalization, first-error diagnostics, `Set` materialization, and structural fold remain the production implementation under test.

A later binding tranche should check in the exact extracted `CallableModeKernel.hs`, route the semantic decisions through it, preserve current duplicate/transfer diagnostics, retain handwritten `Map` normalization, and fail closed on bridge disagreement.

Source capture discovery, callable effect inference, callable lifecycle transitions, scoped-loan escape, authority/evidence semantics, syntax, closure conversion, and target environment layout remain separate obligations.
