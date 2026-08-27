# Phase 1 callable mode implementation refinement v1

This note records the executable implementation correspondence for `PHIL-CALL-MODE-001`.

## Certified surface

`proof/Phil/Core/CallableMode.v` certifies three connected structural rules:

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

`Mode` and `CaptureTransfer` are finite semantic enums and cross the production bridge by total constructor mapping.

## Proved correspondence

The correspondence proof shows:

- extracted transfer acceptance iff the Certified `captureTransferAllowed` predicate is true;
- extracted moved-restricted classification equals Certified `captureMovedRestricted`;
- duplicate acceptance, when supplied `Nat.eqb` as the equality fact, iff Certified `duplicateCaptureAllowed` is true; and
- folding only the capture modes yields exactly Certified `closureStructuralMode` for the original captures.

## Production binding

`src/CallableModeKernel.hs` is the exact extracted kernel. `src/Phil/Core/Callable.hs` now uses it as the semantic authority for all four CALL-MODE decisions.

The handwritten production layer retains only representation and diagnostic responsibilities:

- `Map` lookup/normalization supplies native `CaptureOccurrenceKey` equality and preserves first-error ordering;
- total bridges map `Phil.Core.Syntax.Mode` and `CaptureTransfer` to the finite extracted enums;
- the extracted moved-restricted predicate selects predecessor occurrences for the canonical `Set` summary; and
- the extracted mode-list fold determines `closureMinimumStructuralMode`.

A `Map.lookup` result whose stored occurrence does not equal the lookup key is treated as `CallableModeKernelBridgeMismatch`, although canonical `Data.Map.Strict` behavior makes that branch unreachable under the ordinary runtime foundation.

The dedicated implementation-refinement workflow fresh-extracts `CallableModeKernel.hs`, requires byte-identical equality with the checked-in kernel, typechecks the bound production path under `-Wall -Werror`, reruns the CALL-001–005 correspondence corpus, and records production correspondence hashes.

## Remaining trust boundary

Rocq extraction/toolchain correctness, GHC/runtime behavior, native `CaptureOccurrenceKey` equality, `Data.Map.Strict` lookup/canonicalization, `Data.Set` materialization, and the total enum bridge implementation remain primitive representation/runtime foundations.

Source capture discovery, callable effect inference, callable lifecycle transitions, scoped-loan escape, authority/evidence semantics, syntax, closure conversion, and target environment layout remain separate obligations.
