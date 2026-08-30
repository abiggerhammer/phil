From Corelib Require Extraction.
From Phil.Core Require Import ProviderEvidenceQualificationImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "ProviderEvidenceQualificationKernel"
  decideProviderEvidenceCompetenceByFacts
  decideDirectEvidenceSubjectMappingByFacts
  decideCheckedEvidenceSubjectMappingByFacts
  decideRuntimeCoincidenceSubjectMapping.
