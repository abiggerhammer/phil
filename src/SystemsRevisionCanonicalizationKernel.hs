{-# OPTIONS_GHC -Wno-unused-imports #-}
module SystemsRevisionCanonicalizationKernel where

import qualified Prelude

data SystemsRevisionNamespace =
   SystemsArtifactRevisionNamespace
 | Phase1StageContractRevisionNamespace

data SystemsArtifactRevisionPlan source program stageContract lowering =
   MkSystemsArtifactRevisionPlan SystemsRevisionNamespace source program 
 stageContract lowering

planSystemsArtifactRevision :: a1 -> a2 -> a3 -> a4 ->
                               SystemsArtifactRevisionPlan a1 a2 a3 a4
planSystemsArtifactRevision source program stageContract lowering =
  MkSystemsArtifactRevisionPlan SystemsArtifactRevisionNamespace source
    program stageContract lowering

data Phase1StageContractRevisionPlan instance0 realization systems profile facts dispositions mechanisms justifications =
   MkPhase1StageContractRevisionPlan SystemsRevisionNamespace instance0 
 realization systems profile facts dispositions mechanisms justifications

planPhase1StageContractRevision :: a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 ->
                                   a8 -> Phase1StageContractRevisionPlan 
                                   a1 a2 a3 a4 a5 a6 a7 a8
planPhase1StageContractRevision instanceValue realization systems profile facts dispositions mechanisms justifications =
  MkPhase1StageContractRevisionPlan Phase1StageContractRevisionNamespace
    instanceValue realization systems profile facts dispositions mechanisms
    justifications
