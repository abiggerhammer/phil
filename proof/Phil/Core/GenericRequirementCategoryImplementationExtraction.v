From Corelib Require Extraction.
From Phil.Core Require Import
  GenericRequirementCategory
  GenericRequirementCategoryImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "GenericRequirementCategoryKernel"
  GenericRequirementCategory
  GenericRequirementCompetence
  competenceForRequirementCategory
  RequirementHandoffDecision
  decideRequirementHandoffByFacts
  RequirementInterfaceDomainDecision
  decideRequirementInterfaceDomainByFacts.
