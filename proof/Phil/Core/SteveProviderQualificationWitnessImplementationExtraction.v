From Stdlib Require Import Extraction.

From Phil.Core Require Import SteveProviderQualificationWitnessImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].

Extraction "SteveProviderQualificationWitnessKernel.hs"
  decideSteveProviderQualificationWitnessByFacts.
