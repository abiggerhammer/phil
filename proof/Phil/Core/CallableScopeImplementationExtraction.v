From Corelib Require Extraction.
From Phil.Core Require Import CallableScopeImplementation.

Extraction Language Haskell.
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "CallableScopeKernel"
  decideScopeCaptureByFacts
  decideRecursiveClosureGraphFacts.
