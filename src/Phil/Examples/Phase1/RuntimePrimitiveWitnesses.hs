{-# LANGUAGE OverloadedStrings #-}

module Phil.Examples.Phase1.RuntimePrimitiveWitnesses
  ( uploadRuntimePrimitiveStage
  , steveRuntimePrimitiveStage
  , uploadFrameReceivePrimitiveProfile
  , completeRuntimePrimitiveStage
  ) where

import Phil.Examples.Phase1.RuntimeClaimWitnesses
  ( steveRuntimeClaimStage
  , uploadRuntimeClaimStage
  )
import Phil.Systems.RuntimeClaimBinding
  ( RuntimeClaimStageBundle
  )
import Phil.Systems.RuntimePrimitiveReuse

uploadFrameReceivePrimitiveProfile :: RuntimePrimitiveProfileRef
uploadFrameReceivePrimitiveProfile =
  RuntimePrimitiveProfileRef "upload.runtime.frame_receive"

uploadRuntimePrimitiveStage :: Either String RuntimePrimitiveStageBundle
uploadRuntimePrimitiveStage =
  completeRuntimePrimitiveStage <$> uploadRuntimeClaimStage

steveRuntimePrimitiveStage :: Either String RuntimePrimitiveStageBundle
steveRuntimePrimitiveStage =
  completeRuntimePrimitiveStage <$> steveRuntimeClaimStage

completeRuntimePrimitiveStage
  :: RuntimeClaimStageBundle
  -> RuntimePrimitiveStageBundle
completeRuntimePrimitiveStage = completeRuntimePrimitiveStageBundle
