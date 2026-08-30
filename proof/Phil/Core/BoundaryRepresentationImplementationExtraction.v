From Corelib Require Extraction.
From Phil.Core Require Import BoundaryRepresentationImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "BoundaryRepresentationKernel"
  decideBoundaryMappingByFacts
  planBoundaryCorrespondence
  decideBoundaryUse.
