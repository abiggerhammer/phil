{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.StagingEffect
  ( StagingEffectStageRevision (..)
  , StagingRequirementKey (..)
  , StagingTargetSubject (..)
  , StagingTransferRevision (..)
  , StagingCostIdentity (..)
  , StagingFailureSurface (..)
  , StagingRequirement (..)
  , StagingSubjectTransfer (..)
  , StagingCostAccount (..)
  , StagingEvent (..)
  , StagingEffectStageBundle (..)
  , StagingEffectVerificationError (..)
  , deriveStagingEffectStageRevision
  , makeStagingEffectStageBundle
  , verifyStagingEffectStageBundle
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
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
import Phil.Core.Static
  ( SemanticForm (..)
  , canonicalSemanticForm
  )
import Phil.Systems.IR
  ( BlockId (..)
  , CostClass (..)
  , CostShape (..)
  )
import Phil.Systems.Phase1Stage
  ( SourceFactKey (..)
  )
import Phil.Systems.RuntimeClaimBinding
  ( RuntimeSiteKey (..)
  , RuntimeSiteSlot (..)
  )
import Phil.Systems.RuntimePrimitiveReuse
  ( RuntimePrimitiveProfileRef (..)
  , RuntimePrimitiveSiteBinding (..)
  , RuntimePrimitiveStageBundle (..)
  , RuntimePrimitiveStageRevision (..)
  , RuntimePrimitiveSubjectRef (..)
  , RuntimePrimitiveVerificationError
  , verifyRuntimePrimitiveStageBundle
  )

newtype StagingEffectStageRevision = StagingEffectStageRevision
  { unStagingEffectStageRevision :: Text
  }
  deriving (Eq, Ord, Show)

newtype StagingRequirementKey = StagingRequirementKey
  { unStagingRequirementKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype StagingTargetSubject = StagingTargetSubject
  { unStagingTargetSubject :: Text
  }
  deriving (Eq, Ord, Show)

newtype StagingTransferRevision = StagingTransferRevision
  { unStagingTransferRevision :: Text
  }
  deriving (Eq, Ord, Show)

newtype StagingCostIdentity = StagingCostIdentity
  { unStagingCostIdentity :: Text
  }
  deriving (Eq, Ord, Show)

data StagingFailureSurface
  = StagingInfallible
  | StagingMayFail (Set Text)
  deriving (Eq, Ord, Show)

data StagingRequirement = StagingRequirement
  { stagingRequirementKey :: StagingRequirementKey
  , stagingRequirementSourceSite :: RuntimeSiteKey
  , stagingRequirementSourceProfile :: RuntimePrimitiveProfileRef
  , stagingRequirementSourceSubject :: RuntimePrimitiveSubjectRef
  , stagingRequirementTargetSubject :: StagingTargetSubject
  }
  deriving (Eq, Ord, Show)

data StagingSubjectTransfer = StagingSubjectTransfer
  { stagingTransferSource :: RuntimePrimitiveSubjectRef
  , stagingTransferTarget :: StagingTargetSubject
  , stagingTransferRevision :: StagingTransferRevision
  }
  deriving (Eq, Ord, Show)

data StagingCostAccount = StagingCostAccount
  { stagingCostIdentity :: StagingCostIdentity
  , stagingCostClass :: CostClass
  , stagingCostShape :: CostShape
  }
  deriving (Eq, Ord, Show)

data StagingEvent = StagingEvent
  { stagingEventKey :: StagingRequirementKey
  , stagingEventRequirement :: StagingRequirementKey
  , stagingEventEffect :: Maybe SemanticEffect
  , stagingEventAuthority :: Maybe (Set AuthorityUse)
  , stagingEventFailure :: Maybe StagingFailureSurface
  , stagingEventSubjectTransfer :: Maybe StagingSubjectTransfer
  , stagingEventCost :: Maybe StagingCostAccount
  }
  deriving (Eq, Ord, Show)

data StagingEffectStageBundle = StagingEffectStageBundle
  { stagingEffectStageBase :: RuntimePrimitiveStageBundle
  , stagingEffectStageRevision :: StagingEffectStageRevision
  , stagingEffectStageRequirements
      :: Map StagingRequirementKey StagingRequirement
  , stagingEffectStageEvents
      :: Map StagingRequirementKey StagingEvent
  }
  deriving (Eq, Show)

data StagingEffectVerificationError
  = StagingEffectBaseError RuntimePrimitiveVerificationError
  | StagingEffectStageRevisionMismatch
      StagingEffectStageRevision StagingEffectStageRevision
  | StagingRequirementMapKeyMismatch
      StagingRequirementKey StagingRequirementKey
  | StagingRequirementUnknownSite
      StagingRequirementKey RuntimeSiteKey
  | StagingRequirementProfileMismatch
      StagingRequirementKey
      RuntimePrimitiveProfileRef
      RuntimePrimitiveProfileRef
  | StagingRequirementSourceSubjectMissing
      StagingRequirementKey RuntimePrimitiveSubjectRef
  | StagingRequirementEmptyTargetSubject StagingRequirementKey
  | StagingRequirementSelfTransfer
      StagingRequirementKey Text
  | StagingEventDomainMismatch
      (Set StagingRequirementKey)
      (Set StagingRequirementKey)
  | StagingEventMapKeyMismatch
      StagingRequirementKey StagingRequirementKey
  | StagingEventRequirementMismatch
      StagingRequirementKey
      StagingRequirementKey
      StagingRequirementKey
  | StagingEventMissingEffect StagingRequirementKey
  | StagingEventEmptyEffect StagingRequirementKey
  | StagingEventMissingAuthority StagingRequirementKey
  | StagingEventInvalidAuthority
      StagingRequirementKey AuthorityUse
  | StagingEventMissingFailureSurface StagingRequirementKey
  | StagingEventEmptyFailureSet StagingRequirementKey
  | StagingEventEmptyFailureName StagingRequirementKey
  | StagingEventMissingSubjectTransfer StagingRequirementKey
  | StagingEventTransferSourceMismatch
      StagingRequirementKey
      RuntimePrimitiveSubjectRef
      RuntimePrimitiveSubjectRef
  | StagingEventTransferTargetMismatch
      StagingRequirementKey
      StagingTargetSubject
      StagingTargetSubject
  | StagingEventEmptyTransferRevision StagingRequirementKey
  | StagingEventMissingCost StagingRequirementKey
  | StagingEventEmptyCostIdentity StagingRequirementKey
  | StagingEventCostClassMismatch
      StagingRequirementKey CostClass CostClass
  | StagingEventMissingBytesCopied StagingRequirementKey
  | StagingEventMissingFrequency StagingRequirementKey
  | StagingEventCostIdentityReused
      StagingCostIdentity (Set StagingRequirementKey)
  deriving (Eq, Show)

deriveStagingEffectStageRevision
  :: StagingEffectStageBundle
  -> StagingEffectStageRevision
deriveStagingEffectStageRevision bundle = StagingEffectStageRevision
  ("phil.phase1.stage.staging-effect.canonical.v1:"
    <> canonicalSemanticForm (SemanticRecord (Map.fromList
      [ ("base_stage", SemanticAtom
          (unRuntimePrimitiveStageRevision
            (runtimePrimitiveStageRevision (stagingEffectStageBase bundle))))
      , ("requirements", SemanticRecord (Map.fromList
          [ (unStagingRequirementKey key, semanticRequirement requirement)
          | (key, requirement) <- Map.toAscList
              (stagingEffectStageRequirements bundle)
          ]))
      , ("events", SemanticRecord (Map.fromList
          [ (unStagingRequirementKey key, semanticEvent event)
          | (key, event) <- Map.toAscList (stagingEffectStageEvents bundle)
          ]))
      ])))

makeStagingEffectStageBundle
  :: RuntimePrimitiveStageBundle
  -> Map StagingRequirementKey StagingRequirement
  -> Map StagingRequirementKey StagingEvent
  -> StagingEffectStageBundle
makeStagingEffectStageBundle base requirements events = provisional
  { stagingEffectStageRevision =
      deriveStagingEffectStageRevision provisional
  }
  where
    provisional = StagingEffectStageBundle
      { stagingEffectStageBase = base
      , stagingEffectStageRevision = StagingEffectStageRevision "pending"
      , stagingEffectStageRequirements = requirements
      , stagingEffectStageEvents = events
      }

verifyStagingEffectStageBundle
  :: StagingEffectStageBundle
  -> Either StagingEffectVerificationError ()
verifyStagingEffectStageBundle bundle = do
  mapLeft StagingEffectBaseError $
    verifyRuntimePrimitiveStageBundle (stagingEffectStageBase bundle)
  requireEqual StagingEffectStageRevisionMismatch
    (deriveStagingEffectStageRevision bundle)
    (stagingEffectStageRevision bundle)

  mapM_ (checkRequirement (stagingEffectStageBase bundle))
    (Map.toAscList (stagingEffectStageRequirements bundle))

  let expectedEvents = Map.keysSet (stagingEffectStageRequirements bundle)
      actualEvents = Map.keysSet (stagingEffectStageEvents bundle)
  requireEqual StagingEventDomainMismatch expectedEvents actualEvents

  mapM_ (checkEvent bundle) (Map.toAscList (stagingEffectStageEvents bundle))
  checkCostIdentitySeparation (stagingEffectStageEvents bundle)

checkRequirement
  :: RuntimePrimitiveStageBundle
  -> (StagingRequirementKey, StagingRequirement)
  -> Either StagingEffectVerificationError ()
checkRequirement base (key, requirement) = do
  requireEqual StagingRequirementMapKeyMismatch
    key (stagingRequirementKey requirement)
  siteBinding <- maybe
    (Left (StagingRequirementUnknownSite key
      (stagingRequirementSourceSite requirement)))
    Right
    (Map.lookup
      (stagingRequirementSourceSite requirement)
      (runtimePrimitiveStageSites base))
  requireEqual (StagingRequirementProfileMismatch key)
    (runtimePrimitiveSiteProfile siteBinding)
    (stagingRequirementSourceProfile requirement)
  if Set.member
      (stagingRequirementSourceSubject requirement)
      (runtimePrimitiveSiteSubjects siteBinding)
    then Right ()
    else Left (StagingRequirementSourceSubjectMissing
      key (stagingRequirementSourceSubject requirement))
  let target = unStagingTargetSubject
        (stagingRequirementTargetSubject requirement)
  if Text.null target
    then Left (StagingRequirementEmptyTargetSubject key)
    else Right ()
  case stagingRequirementSourceSubject requirement of
    RuntimePrimitiveExplicitSubject source
      | source == target -> Left (StagingRequirementSelfTransfer key source)
    _ -> Right ()

checkEvent
  :: StagingEffectStageBundle
  -> (StagingRequirementKey, StagingEvent)
  -> Either StagingEffectVerificationError ()
checkEvent bundle (key, event) = do
  requireEqual StagingEventMapKeyMismatch key (stagingEventKey event)
  requireEqual (StagingEventRequirementMismatch key)
    key (stagingEventRequirement event)
  requirement <- maybe
    (Left (StagingEventDomainMismatch
      (Map.keysSet (stagingEffectStageRequirements bundle))
      (Map.keysSet (stagingEffectStageEvents bundle))))
    Right
    (Map.lookup key (stagingEffectStageRequirements bundle))

  case stagingEventEffect event of
    Nothing -> Left (StagingEventMissingEffect key)
    Just (SemanticEffect effect)
      | Text.null effect -> Left (StagingEventEmptyEffect key)
      | otherwise -> Right ()

  case stagingEventAuthority event of
    Nothing -> Left (StagingEventMissingAuthority key)
    Just authority -> mapM_ (checkAuthority key) (Set.toAscList authority)

  case stagingEventFailure event of
    Nothing -> Left (StagingEventMissingFailureSurface key)
    Just StagingInfallible -> Right ()
    Just (StagingMayFail failures)
      | Set.null failures -> Left (StagingEventEmptyFailureSet key)
      | any Text.null (Set.toAscList failures) ->
          Left (StagingEventEmptyFailureName key)
      | otherwise -> Right ()

  transfer <- maybe
    (Left (StagingEventMissingSubjectTransfer key))
    Right
    (stagingEventSubjectTransfer event)
  requireEqual (StagingEventTransferSourceMismatch key)
    (stagingRequirementSourceSubject requirement)
    (stagingTransferSource transfer)
  requireEqual (StagingEventTransferTargetMismatch key)
    (stagingRequirementTargetSubject requirement)
    (stagingTransferTarget transfer)
  case stagingTransferRevision transfer of
    StagingTransferRevision revision
      | Text.null revision ->
          Left (StagingEventEmptyTransferRevision key)
      | otherwise -> Right ()

  cost <- maybe
    (Left (StagingEventMissingCost key))
    Right
    (stagingEventCost event)
  case stagingCostIdentity cost of
    StagingCostIdentity identity
      | Text.null identity -> Left (StagingEventEmptyCostIdentity key)
      | otherwise -> Right ()
  requireEqual (StagingEventCostClassMismatch key)
    TargetRequired (stagingCostClass cost)
  checkCostField
    (StagingEventMissingBytesCopied key)
    (costBytesCopied (stagingCostShape cost))
  checkCostField
    (StagingEventMissingFrequency key)
    (costFrequency (stagingCostShape cost))

checkAuthority
  :: StagingRequirementKey
  -> AuthorityUse
  -> Either StagingEffectVerificationError ()
checkAuthority key use
  | Text.null subject || Text.null operation =
      Left (StagingEventInvalidAuthority key use)
  | otherwise = Right ()
  where
    AuthoritySubjectKey subject = authorityUseSubject use
    AuthorityOperationKey operation = authorityUseOperation use

checkCostField
  :: StagingEffectVerificationError
  -> Maybe Text
  -> Either StagingEffectVerificationError ()
checkCostField err value = case value of
  Nothing -> Left err
  Just text
    | Text.null text -> Left err
    | otherwise -> Right ()

checkCostIdentitySeparation
  :: Map StagingRequirementKey StagingEvent
  -> Either StagingEffectVerificationError ()
checkCostIdentitySeparation events =
  mapM_ checkGroup (Map.toAscList groups)
  where
    groups = Map.fromListWith Set.union
      [ (stagingCostIdentity cost, Set.singleton key)
      | (key, event) <- Map.toAscList events
      , Just cost <- [stagingEventCost event]
      ]
    checkGroup (identity, keys)
      | Set.size keys <= 1 = Right ()
      | otherwise = Left (StagingEventCostIdentityReused identity keys)

semanticRequirement :: StagingRequirement -> SemanticForm
semanticRequirement requirement = SemanticRecord (Map.fromList
  [ ("key", SemanticAtom
      (unStagingRequirementKey (stagingRequirementKey requirement)))
  , ("source_site", semanticSiteKey (stagingRequirementSourceSite requirement))
  , ("source_profile", SemanticAtom
      (unRuntimePrimitiveProfileRef
        (stagingRequirementSourceProfile requirement)))
  , ("source_subject", semanticSubject
      (stagingRequirementSourceSubject requirement))
  , ("target_subject", SemanticAtom
      (unStagingTargetSubject (stagingRequirementTargetSubject requirement)))
  ])

semanticEvent :: StagingEvent -> SemanticForm
semanticEvent event = SemanticRecord (Map.fromList
  [ ("key", SemanticAtom
      (unStagingRequirementKey (stagingEventKey event)))
  , ("requirement", SemanticAtom
      (unStagingRequirementKey (stagingEventRequirement event)))
  , ("effect", semanticMaybeEffect (stagingEventEffect event))
  , ("authority", semanticMaybeAuthority (stagingEventAuthority event))
  , ("failure", semanticMaybeFailure (stagingEventFailure event))
  , ("transfer", semanticMaybeTransfer (stagingEventSubjectTransfer event))
  , ("cost", semanticMaybeCost (stagingEventCost event))
  ])

semanticMaybeEffect :: Maybe SemanticEffect -> SemanticForm
semanticMaybeEffect value = case value of
  Nothing -> SemanticAtom "missing"
  Just (SemanticEffect effect) -> SemanticAtom effect

semanticMaybeAuthority :: Maybe (Set AuthorityUse) -> SemanticForm
semanticMaybeAuthority value = case value of
  Nothing -> SemanticAtom "missing"
  Just authority -> SemanticUnordered (Set.map semanticAuthority authority)

semanticAuthority :: AuthorityUse -> SemanticForm
semanticAuthority use = SemanticRecord (Map.fromList
  [ ("subject", SemanticAtom subject)
  , ("operation", SemanticAtom operation)
  ])
  where
    AuthoritySubjectKey subject = authorityUseSubject use
    AuthorityOperationKey operation = authorityUseOperation use

semanticMaybeFailure :: Maybe StagingFailureSurface -> SemanticForm
semanticMaybeFailure value = case value of
  Nothing -> SemanticAtom "missing"
  Just StagingInfallible -> SemanticAtom "infallible"
  Just (StagingMayFail failures) ->
    SemanticUnordered (Set.map SemanticAtom failures)

semanticMaybeTransfer :: Maybe StagingSubjectTransfer -> SemanticForm
semanticMaybeTransfer value = case value of
  Nothing -> SemanticAtom "missing"
  Just transfer -> SemanticRecord (Map.fromList
    [ ("source", semanticSubject (stagingTransferSource transfer))
    , ("target", SemanticAtom
        (unStagingTargetSubject (stagingTransferTarget transfer)))
    , ("revision", SemanticAtom
        (unStagingTransferRevision (stagingTransferRevision transfer)))
    ])

semanticMaybeCost :: Maybe StagingCostAccount -> SemanticForm
semanticMaybeCost value = case value of
  Nothing -> SemanticAtom "missing"
  Just cost -> SemanticRecord (Map.fromList
    [ ("identity", SemanticAtom
        (unStagingCostIdentity (stagingCostIdentity cost)))
    , ("class", SemanticAtom (renderCostClass (stagingCostClass cost)))
    , ("shape", semanticCostShape (stagingCostShape cost))
    ])

semanticCostShape :: CostShape -> SemanticForm
semanticCostShape shape = SemanticRecord (Map.fromList
  [ ("compile_time", semanticMaybeText (costCompileTime shape))
  , ("code_size", semanticMaybeText (costCodeSize shape))
  , ("allocation_count", semanticMaybeText (costAllocationCount shape))
  , ("peak_live_memory", semanticMaybeText (costPeakLiveMemory shape))
  , ("bytes_copied", semanticMaybeText (costBytesCopied shape))
  , ("dynamic_check_count", semanticMaybeText (costDynamicCheckCount shape))
  , ("branch_or_dispatch", semanticMaybeText (costBranchOrDispatch shape))
  , ("hash_or_crypto_work", semanticMaybeText (costHashOrCryptoWork shape))
  , ("synchronization", semanticMaybeText (costSynchronization shape))
  , ("frequency", semanticMaybeText (costFrequency shape))
  ])

semanticMaybeText :: Maybe Text -> SemanticForm
semanticMaybeText value = maybe (SemanticAtom "none") SemanticAtom value

semanticSubject :: RuntimePrimitiveSubjectRef -> SemanticForm
semanticSubject subject = case subject of
  RuntimePrimitiveExplicitSubject value -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "explicit")
    , ("value", SemanticAtom value)
    ])
  RuntimePrimitiveSourceFactSubject fact -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "source-fact")
    , ("value", SemanticAtom (unSourceFactKey fact))
    ])

semanticSiteKey :: RuntimeSiteKey -> SemanticForm
semanticSiteKey key = SemanticRecord (Map.fromList
  [ ("function", SemanticAtom (runtimeSiteFunction key))
  , ("block", SemanticAtom (unBlockId (runtimeSiteBlock key)))
  , ("slot", SemanticAtom (renderSiteSlot (runtimeSiteSlot key)))
  ])

renderSiteSlot :: RuntimeSiteSlot -> Text
renderSiteSlot slot = case slot of
  RuntimeOperationSite index -> "op." <> Text.pack (show index)
  RuntimeTerminatorSite -> "term"

renderCostClass :: CostClass -> Text
renderCostClass costClass = case costClass of
  SemanticRequired -> "semantic-required"
  RuntimeAssuranceRequired -> "runtime-assurance-required"
  TargetRequired -> "target-required"
  DefensiveProfile -> "defensive-profile"
  ConservativeLowering -> "conservative-lowering"

requireEqual :: Eq a => (a -> a -> e) -> a -> a -> Either e ()
requireEqual mkError expected actual
  | expected == actual = Right ()
  | otherwise = Left (mkError expected actual)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
