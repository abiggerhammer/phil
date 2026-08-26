{-# LANGUAGE OverloadedStrings #-}

module Phil.Examples.Phase1.CostAttributionWitnesses
  ( uploadCostAttributionStage
  , steveCostAttributionStage
  , uploadRuntimeCostBases
  , uploadFrameReceiveChargeIdentity
  , completeCostAttributionStage
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Phil.Examples.Phase1.StagingEffectWitnesses
  ( steveStagingEffectStage
  , uploadStagingEffectStage
  )
import Phil.Systems.CostAttribution
import Phil.Systems.IR
  ( DecisionId (..)
  )
import Phil.Systems.RuntimePrimitiveReuse
  ( RuntimePrimitiveProfileRef (..)
  )
import Phil.Systems.StagingEffect
  ( StagingEffectStageBundle
  )

uploadFrameReceiveChargeIdentity :: CostChargeIdentity
uploadFrameReceiveChargeIdentity =
  CostChargeIdentity "cost.runtime.frame_receive.v1"

uploadRuntimeCostBases
  :: Map RuntimePrimitiveProfileRef RuntimeCostBasis
uploadRuntimeCostBases = Map.fromList
  [ basis "upload.runtime.frame_receive"
      "lower.ingress.frame_storage"
      uploadFrameReceiveChargeIdentity
  , basis "upload.runtime.hello_policy"
      "lower.check.hello_policy"
      (CostChargeIdentity "cost.runtime.hello_policy.v1")
  , basis "upload.runtime.branch_refinement"
      "lower.check.version_refinement"
      (CostChargeIdentity "cost.runtime.branch_refinement.v1")
  , basis "upload.runtime.begin_policy"
      "lower.check.begin_policy"
      (CostChargeIdentity "cost.runtime.begin_policy.v1")
  , basis "upload.runtime.receive_exact"
      "lower.check.receive_exact"
      (CostChargeIdentity "cost.runtime.receive_exact.v1")
  , basis "upload.runtime.send_exact"
      "lower.runtime.send_exact"
      (CostChargeIdentity "cost.runtime.send_exact.v1")
  , basis "upload.runtime.digest"
      "lower.runtime.digest"
      (CostChargeIdentity "cost.runtime.digest.v1")
  , basis "upload.runtime.store"
      "lower.runtime.store"
      (CostChargeIdentity "cost.runtime.store.v1")
  ]
  where
    basis profile decision charge =
      let profileRef = RuntimePrimitiveProfileRef profile
      in (profileRef, RuntimeCostBasis
          { runtimeCostBasisProfile = profileRef
          , runtimeCostBasisDecision = DecisionId decision
          , runtimeCostBasisCharge = charge
          })

uploadCostAttributionStage
  :: Either String CostAttributionStageBundle
uploadCostAttributionStage = do
  base <- uploadStagingEffectStage
  completeCostAttributionStage base uploadRuntimeCostBases

steveCostAttributionStage
  :: Either String CostAttributionStageBundle
steveCostAttributionStage = do
  base <- steveStagingEffectStage
  completeCostAttributionStage base Map.empty

completeCostAttributionStage
  :: StagingEffectStageBundle
  -> Map RuntimePrimitiveProfileRef RuntimeCostBasis
  -> Either String CostAttributionStageBundle
completeCostAttributionStage = completeCostAttributionStageBundle
