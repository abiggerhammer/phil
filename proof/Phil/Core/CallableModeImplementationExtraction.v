From Corelib Require Extraction.

From Phil.Core Require Import CallableModeImplementation.

Extraction Language Haskell.
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "CallableModeKernel"
  decideCallableCaptureTransfer
  captureMovedRestrictedByMode
  decideCallableDuplicateCapture
  closureStructuralModeFromModes.
