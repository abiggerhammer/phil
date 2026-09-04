From Corelib Require Extraction.
From Phil.Core Require Import StorageCostAttributionImplementation.

Extraction Language Haskell.
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "StorageCostAttributionKernel.hs"
  decideStorageCostSubjectExactByFacts
  decideStorageCostPhysicalDomainExactByFacts
  decideAttributableStorageCostByFacts
  decideStorageCostLineageValidByFacts
  decideStorageRuntimeCostBindingByFacts
  decideCertifiedStorageCostAttributionByFacts.
