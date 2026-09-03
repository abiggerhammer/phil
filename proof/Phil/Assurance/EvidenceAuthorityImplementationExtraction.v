From Corelib Require Extraction.
From Phil.Assurance Require Import EvidenceUse EvidenceAuthorityImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "AssuranceEvidenceAuthorityKernel"
  GateResult
  decideArtifactAuthorityByFacts
  decideRuntimeAuthorityByFacts.
