From Corelib Require Extraction.
From Phil.Assurance Require Import DeploymentAuthorityImplementation.

Extraction Language Haskell.
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "DeploymentAuthorityKernel"
  decideDeploymentAuthorityPolicyAdmissibleByFacts
  decideDeploymentAuthorityGrantMatchesByFacts
  decideDeploymentAuthorityIssuedByFacts
  decideDeploymentAuthorityUsableByFacts.
