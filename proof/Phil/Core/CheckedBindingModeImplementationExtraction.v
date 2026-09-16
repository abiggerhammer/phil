From Stdlib Require Import Extraction.

From Phil.Core Require Import CheckedBindingModeImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].

Extraction "CheckedBindingModeKernel.hs"
  decideCheckedBindingModeByFacts.
