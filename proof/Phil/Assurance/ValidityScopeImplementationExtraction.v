From Corelib Require Extraction.
From Phil.Assurance Require Import ValidityScopeImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive list => "[]" [ "[]" "(:)" ].

Extraction "AssuranceValidityScopeKernel"
  validityScopeFactsb
  decideValidityScope.
