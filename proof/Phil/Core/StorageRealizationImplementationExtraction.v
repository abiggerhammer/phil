From Corelib Require Extraction.
From Phil.Core Require Import StorageRealizationImplementation.

Extraction Language Haskell.
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "StorageRealizationKernel"
  decideStorageRealizationValidByFacts.
