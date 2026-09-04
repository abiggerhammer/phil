From Stdlib Require Import Extraction.

From Phil.Surface Require Import GrammarRevisionImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].

Extraction "GrammarRevisionKernel.hs"
  decideGrammarRevisionBindingByFacts.
