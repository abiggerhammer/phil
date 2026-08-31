From Corelib Require Extraction.
From Phil.Core Require Import DataIdentityImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "DataIdentityKernel"
  decideDataIdentityByFact
  decideDataOperationByFact
  decideDataOperationAfterIdentityByFacts.
