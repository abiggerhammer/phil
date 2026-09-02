From Corelib Require Extraction.
From Phil.Core Require Import SystemsRevisionCanonicalizationImplementation.

Extraction Language Haskell.

Extraction "SystemsRevisionCanonicalizationKernel"
  SystemsRevisionNamespace
  planSystemsArtifactRevision
  planPhase1StageContractRevision.
