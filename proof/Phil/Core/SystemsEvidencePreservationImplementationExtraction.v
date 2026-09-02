From Corelib Require Extraction.
From Phil.Core Require Import SystemsEvidencePreservationImplementation.

Extraction Language Haskell.

Extraction "SystemsEvidencePreservationKernel"
  EvidenceErasureDecision
  decideEvidenceErasureByFacts
  AssumptionDependencyDecision
  decideAssumptionDependencyByFacts
  SystemsEvidenceDecision
  decideSystemsEvidenceByFacts.
