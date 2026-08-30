From Corelib Require Extraction.
From Phil.Core Require Import BoundaryEncodingImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "BoundaryEncodingKernel"
  decideQualifiedEncodingByFacts
  planGeneratedEncoding
  decideEncodingCanonicality
  decideBoundarySerializationByFacts.
