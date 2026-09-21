From Stdlib Require Import Extraction.

From Phil.Core Require Import UTF8Implementation.

Extraction Language Haskell.

Extract Inductive bool =>
  "Prelude.Bool" ["Prelude.True" "Prelude.False"].

Extraction "UTF8ImplementationKernel"
  decideReadUTF8ByFacts
  decideWriteUTF8ByFacts
  decideWriteLineByFacts.
