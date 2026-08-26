{-# LANGUAGE OverloadedStrings #-}

module Phil.Examples.Phase1.StagingEffectWitnesses
  ( uploadStagingEffectStage
  , steveStagingEffectStage
  , uploadDigestStagingRequirementKey
  , uploadDigestStagingTargetSubject
  , uploadReceivePrimitiveProfile
  , completeStagingEffectStage
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.Authority
  ( AuthorityOperationKey (..)
  , AuthoritySubjectKey (..)
  )
import Phil.Core.AuthorityConfinement
  ( AuthorityUse (..)
  )
import Phil.Core.Callable
  ( SemanticEffect (..)
  )
import Phil.Examples.Phase1.RuntimePrimitiveWitnesses
  ( steveRuntimePrimitiveStage
  , uploadRuntimePrimitiveStage
  )
import Phil.Systems.IR
  ( CostClass (..)
  , CostShape (..)
  , emptyCostShape
  )
import Phil.Systems.RuntimeClaimBinding
  ( RuntimeSiteKey
  )
import Phil.Systems.RuntimePrimitiveReuse
  ( RuntimePrimitiveProfileRef (..)
  , RuntimePrimitiveStageBundle (..)
  , RuntimePrimitiveSubjectRef (..)
  )
import Phil.Systems.StagingEffect

uploadDigestStagingRequirementKey :: StagingRequirementKey
uploadDigestStagingRequirementKey =
  StagingRequirementKey "staging.upload.digest-input.v1"

uploadDigestStagingTargetSubject :: StagingTargetSubject
uploadDigestStagingTargetSubject =
  StagingTargetSubject "target.upload.payload.digest-staging"

uploadReceivePrimitiveProfile :: RuntimePrimitiveProfileRef
uploadReceivePrimitiveProfile =
  RuntimePrimitiveProfileRef "upload.runtime.receive_exact"

uploadStagingEffectStage :: Either String StagingEffectStageBundle
uploadStagingEffectStage = do
  base <- uploadRuntimePrimitiveStage
  sourceSite <- uniqueSiteByProfile uploadReceivePrimitiveProfile base
  let sourceSubject = RuntimePrimitiveExplicitSubject "upload.payload"
      requirement = StagingRequirement
        { stagingRequirementKey = uploadDigestStagingRequirementKey
        , stagingRequirementSourceSite = sourceSite
        , stagingRequirementSourceProfile = uploadReceivePrimitiveProfile
        , stagingRequirementSourceSubject = sourceSubject
        , stagingRequirementTargetSubject = uploadDigestStagingTargetSubject
        }
      transfer = StagingSubjectTransfer
        { stagingTransferSource = sourceSubject
        , stagingTransferTarget = uploadDigestStagingTargetSubject
        , stagingTransferRevision =
            StagingTransferRevision "transfer.target.byte-copy-equality.v1"
        }
      authority = Set.fromList
        [ AuthorityUse
            (AuthoritySubjectKey "target.staging-buffer")
            (AuthorityOperationKey "allocate")
        , AuthorityUse
            (AuthoritySubjectKey "target.staging-buffer")
            (AuthorityOperationKey "write")
        ]
      cost = StagingCostAccount
        { stagingCostIdentity =
            StagingCostIdentity "cost.target.upload.digest-staging.v1"
        , stagingCostClass = TargetRequired
        , stagingCostShape = emptyCostShape
            { costAllocationCount = Just "1 staging buffer"
            , costPeakLiveMemory = Just "payload length"
            , costBytesCopied = Just "payload length"
            , costFrequency = Just "per payload before digest"
            }
        }
      event = StagingEvent
        { stagingEventKey = uploadDigestStagingRequirementKey
        , stagingEventRequirement = uploadDigestStagingRequirementKey
        , stagingEventEffect =
            Just (SemanticEffect "target.staging.copy-bytes")
        , stagingEventAuthority = Just authority
        , stagingEventFailure =
            Just (StagingMayFail (Set.singleton "allocation-failure"))
        , stagingEventSubjectTransfer = Just transfer
        , stagingEventCost = Just cost
        }
  pure (completeStagingEffectStage
    base
    (Map.singleton uploadDigestStagingRequirementKey requirement)
    (Map.singleton uploadDigestStagingRequirementKey event))

steveStagingEffectStage :: Either String StagingEffectStageBundle
steveStagingEffectStage = do
  base <- steveRuntimePrimitiveStage
  pure (completeStagingEffectStage base Map.empty Map.empty)

completeStagingEffectStage
  :: RuntimePrimitiveStageBundle
  -> Map.Map StagingRequirementKey StagingRequirement
  -> Map.Map StagingRequirementKey StagingEvent
  -> StagingEffectStageBundle
completeStagingEffectStage = makeStagingEffectStageBundle

uniqueSiteByProfile
  :: RuntimePrimitiveProfileRef
  -> RuntimePrimitiveStageBundle
  -> Either String RuntimeSiteKey
uniqueSiteByProfile profile bundle =
  case Map.lookup profile (runtimePrimitiveStageReverse bundle) of
    Nothing -> Left ("runtime primitive profile missing: " <> show profile)
    Just sites -> case Set.toAscList sites of
      [site] -> Right site
      [] -> Left ("runtime primitive profile has no sites: " <> show profile)
      many -> Left ("runtime primitive profile is not unique: "
        <> show profile <> " -> " <> show many)
