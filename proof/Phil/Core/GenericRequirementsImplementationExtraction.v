From Corelib Require Extraction.
From Phil.Core Require Import GenericRequirementsImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "GenericRequirementsKernel"
  requirementsCover
  decideGenericRequirementsCoverage.
