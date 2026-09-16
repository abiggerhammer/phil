From Corelib Require Extraction.
From Phil.Core Require Import ProviderRelativePathImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "ProviderRelativePathKernel"
  decideFileSystemOccurrenceByFacts
  decideProviderRelativeSegmentAt
  decideProviderRelativeSegmentsFrom
  decideProviderRelativePathByFacts.
