From Stdlib Require Import Extraction.

From Phil.Core Require Import SystemsRealizationEffectsImplementation.

Extraction Language Haskell.
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "SystemsRealizationEffectsKernel"
  decideTargetStrengtheningByFacts
  decideStagingEffectByFacts
  decideNextStageExportByFacts
  decideSystemsRealizationEffectsByFacts.
