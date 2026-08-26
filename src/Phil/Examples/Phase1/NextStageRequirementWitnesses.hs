{-# LANGUAGE OverloadedStrings #-}

module Phil.Examples.Phase1.NextStageRequirementWitnesses
  ( uploadNextStageRequirementStage
  , steveNextStageRequirementStage
  , uploadFrameReceiveRequirementBasis
  , steveHostAbiRequirementBasis
  ) where

import Phil.Examples.Phase1.CostAttributionWitnesses
  ( steveCostAttributionStage
  , uploadCostAttributionStage
  )
import Phil.Examples.Phase1.SystemsWitnesses
  ( steveHostAbiDecisionId
  , steveHostAbiTargetPrecondition
  )
import Phil.Systems.NextStageRequirement
import Phil.Systems.RuntimePrimitiveReuse
  ( RuntimePrimitiveProfileRef (..)
  )
import Phil.Systems.TargetStrengthening
  ( TargetPreconditionRef (..)
  )

uploadNextStageRequirementStage
  :: Either String NextStageRequirementStageBundle
uploadNextStageRequirementStage =
  uploadCostAttributionStage >>= completeNextStageRequirementStageBundle

steveNextStageRequirementStage
  :: Either String NextStageRequirementStageBundle
steveNextStageRequirementStage =
  steveCostAttributionStage >>= completeNextStageRequirementStageBundle

uploadFrameReceiveRequirementBasis :: NextStageRequirementBasis
uploadFrameReceiveRequirementBasis =
  NextStageRuntimePrimitiveBasis
    (RuntimePrimitiveProfileRef "upload.runtime.frame_receive")

steveHostAbiRequirementBasis :: NextStageRequirementBasis
steveHostAbiRequirementBasis =
  NextStageTargetPreconditionBasis TargetPreconditionRef
    { targetPreconditionDecision = steveHostAbiDecisionId
    , targetPreconditionRequirement = steveHostAbiTargetPrecondition
    }
