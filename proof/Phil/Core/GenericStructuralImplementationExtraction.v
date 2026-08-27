From Corelib Require Extraction.
From Phil.Core Require Import
  GenericStructural
  GenericStructuralImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive list => "[]" [ "[]" "(:)" ].

Extraction "GenericStructuralKernel"
  addStructuralUse
  inferGenericStructuralRequirements
  modeAllowsStructuralPermission
  modeSatisfiesRequirements
  decideGenericStructuralActual.
