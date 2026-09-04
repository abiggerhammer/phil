From Stdlib Require Extraction.

From Phil.Core Require Import StorageRealizationImplementation.

Extraction Language Haskell.

Extraction "StorageRealizationKernel.hs"
  decideStorageRealizationValidByFacts.
