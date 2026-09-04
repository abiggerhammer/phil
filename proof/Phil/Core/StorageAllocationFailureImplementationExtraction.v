From Corelib Require Extraction.
From Phil.Core Require Import StorageAllocationFailureImplementation.

Extraction Language Haskell.
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "StorageAllocationFailureKernel.hs"
  decideStorageFailureRealizationByFacts
  decideStorageFailureCannotFailByFacts
  decideStorageFailureMapsToSourceByFacts
  decideStorageFailureProvedUnreachableByFacts
  decideStorageFailureAssumptionByFacts
  decideStorageFailureDeploymentRequirementByFacts
  decideStorageFailureUnaccountedByFacts.
