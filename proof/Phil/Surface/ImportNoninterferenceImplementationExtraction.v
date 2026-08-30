From Corelib Require Extraction.
From Phil.Surface Require Import ImportNoninterferenceImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "ArchitectureImportKernel"
  decideImportResolutionByFacts
  planImportedBinding.
