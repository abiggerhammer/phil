From Corelib Require Extraction.
From Phil.Core Require Import
  GenericRequirements
  GenericRequirementsImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "GenericRequirementsKernel"
  requirementsCover
  decideGenericRequirementsCoverage.
