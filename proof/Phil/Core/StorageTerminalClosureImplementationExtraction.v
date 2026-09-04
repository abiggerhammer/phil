From Corelib Require Extraction.
From Phil.Core Require Import StorageTerminalClosureImplementation.

Extraction Language Haskell.
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "StorageTerminalClosureKernel.hs"
  decideSemanticStorageLiveByFacts
  decideSemanticStorageReleasedByFacts
  decideSemanticStorageTerminalDispositionByFacts
  decideSemanticStorageClosureByFacts
  decidePhysicalStorageReclaimedByFacts
  decidePhysicalStorageLeakedByFacts
  decidePhysicalStorageRetainedByProfileByFacts
  decidePhysicalStorageReclamationByFacts
  decideCertifiedMemoryProcessClosureByFacts
  decideCertifiedMemoryRootClosureByFacts.
