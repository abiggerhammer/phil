From Corelib Require Extraction.

From Phil.Core Require Import ArchitectureInstantiation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "ArchitectureInstantiationKernel"
  decideChildSlotByFacts
  decideArchitectureRequirementByFacts
  decideRootRequirementByFacts
  decideArchitectureReferenceByFacts.
