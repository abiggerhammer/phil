From Corelib Require Extraction.
From Phil.Assurance Require Import DeploymentQualificationImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "DeploymentQualificationKernel"
  decideDeploymentQualificationByFacts
  decideDeploymentQualificationAvailableByFacts.
