From Corelib Require Extraction.
From Phil.Core Require Import SystemsStageClosureImplementation.

Extraction Language Haskell.
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "SystemsStageClosureKernel"
  SourceClosureDecision
  TargetClosureDecision
  StageIdentityDecision
  SystemsStageClosureDecision
  decideSourceClosureByFacts
  decideTargetClosureByFacts
  decideStageIdentityByFacts
  decideSystemsStageClosureByFacts.
