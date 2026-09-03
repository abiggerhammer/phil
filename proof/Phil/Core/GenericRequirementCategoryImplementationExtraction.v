From Corelib Require Extraction.
From Phil.Core Require Import
  GenericRequirementCategory
  GenericRequirementCategoryImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "GenericRequirementCategoryKernel"
  Phil.Core.GenericRequirementCategory.GenericRequirementCategory
  Phil.Core.GenericRequirementCategory.GenericRequirementCompetence
  Phil.Core.GenericRequirementCategory.competenceForRequirementCategory
  Phil.Core.GenericRequirementCategoryImplementation.RequirementHandoffDecision
  Phil.Core.GenericRequirementCategoryImplementation.decideRequirementHandoffByFacts
  Phil.Core.GenericRequirementCategoryImplementation.RequirementInterfaceDomainDecision
  Phil.Core.GenericRequirementCategoryImplementation.decideRequirementInterfaceDomainByFacts.
