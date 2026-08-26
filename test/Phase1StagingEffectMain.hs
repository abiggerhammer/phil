{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

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
import Phil.Examples.Phase1.StagingEffectWitnesses
import Phil.Systems.IR
  ( BlockId (..)
  , CostClass (..)
  , CostShape (..)
  )
import Phil.Systems.RuntimeClaimBinding
  ( RuntimeSiteKey (..)
  , RuntimeSiteSlot (..)
  )
import Phil.Systems.RuntimePrimitiveReuse
  ( RuntimePrimitiveProfileRef (..)
  , RuntimePrimitiveSubjectRef (..)
  , verifyRuntimePrimitiveStageBundle
  )
import Phil.Systems.StagingEffect
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SYS-017 SYS-016 upload predecessor remains valid"
        uploadPrimitiveRegression
    , test "SYS-017 SYS-016 Steve predecessor remains valid"
        stevePrimitiveRegression
    , test "SYS-017 upload target staging event is accepted"
        uploadStagingAccepted
    , test "SYS-017 Steve empty staging relation is accepted"
        steveStagingAccepted
    , test "SYS-017 upload staging event carries every required consequence"
        uploadStagingConsequencesPresent
    , test "SYS-017 selected staging requirement cannot omit its event"
        eventOmissionRejected
    , test "SYS-017 staging requirement map key is exact"
        requirementMapKeyRejected
    , test "SYS-017 staging requirement must name an exact predecessor site"
        unknownSiteRejected
    , test "SYS-017 staging requirement must retain exact primitive profile"
        profileDriftRejected
    , test "SYS-017 staging source subject must exist at exact site"
        sourceSubjectDriftRejected
    , test "SYS-017 staging target subject cannot be empty"
        emptyTargetSubjectRejected
    , test "SYS-017 staging event must bind its exact requirement"
        eventRequirementDriftRejected
    , test "SYS-017 staging realization effect cannot be omitted"
        missingEffectRejected
    , test "SYS-017 staging realization effect cannot be empty"
        emptyEffectRejected
    , test "SYS-017 staging authority account cannot be omitted"
        missingAuthorityRejected
    , test "SYS-017 malformed staging authority is rejected"
        malformedAuthorityRejected
    , test "SYS-017 staging failure surface cannot be omitted"
        missingFailureRejected
    , test "SYS-017 may-fail staging needs an explicit failure set"
        emptyFailureSetRejected
    , test "SYS-017 explicit infallibility is distinct from omission"
        explicitInfallibilityAccepted
    , test "SYS-017 staging subject transfer cannot be omitted"
        missingTransferRejected
    , test "SYS-017 transfer source must match staging requirement"
        transferSourceDriftRejected
    , test "SYS-017 transfer target must match staging requirement"
        transferTargetDriftRejected
    , test "SYS-017 transfer relation revision cannot be empty"
        emptyTransferRevisionRejected
    , test "SYS-017 staging cost account cannot be omitted"
        missingCostRejected
    , test "SYS-017 staging cost is target-required"
        wrongCostClassRejected
    , test "SYS-017 staging cost must account bytes copied"
        missingBytesCopiedRejected
    , test "SYS-017 staging cost must account frequency"
        missingFrequencyRejected
    , test "SYS-017 staging cost identity cannot be reused by distinct copies"
        duplicateCostIdentityRejected
    , test "SYS-017 staging-effect stage identity is deterministic"
        deterministicIdentity
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

uploadPrimitiveRegression :: Either String ()
uploadPrimitiveRegression = do
  bundle <- uploadRuntimePrimitiveStage
  mapLeft show (verifyRuntimePrimitiveStageBundle bundle)

stevePrimitiveRegression :: Either String ()
stevePrimitiveRegression = do
  bundle <- steveRuntimePrimitiveStage
  mapLeft show (verifyRuntimePrimitiveStageBundle bundle)

uploadStagingAccepted :: Either String ()
uploadStagingAccepted = do
  bundle <- uploadStagingEffectStage
  mapLeft show (verifyStagingEffectStageBundle bundle)

steveStagingAccepted :: Either String ()
steveStagingAccepted = do
  bundle <- steveStagingEffectStage
  mapLeft show (verifyStagingEffectStageBundle bundle)

uploadStagingConsequencesPresent :: Either String ()
uploadStagingConsequencesPresent = do
  bundle <- uploadStagingEffectStage
  event <- requireUploadEvent bundle
  assert (stagingEventEffect event /= Nothing)
    "staging effect missing"
  assert (stagingEventAuthority event /= Nothing)
    "staging authority account missing"
  assert (stagingEventFailure event /= Nothing)
    "staging failure surface missing"
  assert (stagingEventSubjectTransfer event /= Nothing)
    "staging subject transfer missing"
  assert (stagingEventCost event /= Nothing)
    "staging cost account missing"

eventOmissionRejected :: Either String ()
eventOmissionRejected = do
  original <- uploadStagingEffectStage
  let events = Map.delete uploadDigestStagingRequirementKey
        (stagingEffectStageEvents original)
      mutated = rebuild original
        (stagingEffectStageRequirements original) events
  case verifyStagingEffectStageBundle mutated of
    Left (StagingEventDomainMismatch expected actual)
      | Set.member uploadDigestStagingRequirementKey expected
          && not (Set.member uploadDigestStagingRequirementKey actual) -> Right ()
    other -> Left ("staging event omission was accepted: " <> show other)

requirementMapKeyRejected :: Either String ()
requirementMapKeyRejected = do
  original <- uploadStagingEffectStage
  requirement <- requireUploadRequirement original
  let wrong = StagingRequirementKey "staging.upload.wrong-key.v1"
      bad = requirement { stagingRequirementKey = wrong }
      requirements = Map.insert uploadDigestStagingRequirementKey bad
        (stagingEffectStageRequirements original)
      mutated = rebuild original requirements (stagingEffectStageEvents original)
  case verifyStagingEffectStageBundle mutated of
    Left (StagingRequirementMapKeyMismatch actual observed)
      | actual == uploadDigestStagingRequirementKey
          && observed == wrong -> Right ()
    other -> Left ("staging requirement key drift was accepted: " <> show other)

unknownSiteRejected :: Either String ()
unknownSiteRejected = do
  original <- uploadStagingEffectStage
  requirement <- requireUploadRequirement original
  let invented = RuntimeSiteKey
        "target.invented"
        (BlockId "target.invented")
        RuntimeTerminatorSite
      bad = requirement { stagingRequirementSourceSite = invented }
  expectRequirementError original bad $ \err -> case err of
    StagingRequirementUnknownSite actual site ->
      actual == uploadDigestStagingRequirementKey && site == invented
    _ -> False

profileDriftRejected :: Either String ()
profileDriftRejected = do
  original <- uploadStagingEffectStage
  requirement <- requireUploadRequirement original
  let invented = RuntimePrimitiveProfileRef "target.invented.profile"
      bad = requirement { stagingRequirementSourceProfile = invented }
  expectRequirementError original bad $ \err -> case err of
    StagingRequirementProfileMismatch actual expected observed ->
      actual == uploadDigestStagingRequirementKey
        && expected == uploadReceivePrimitiveProfile
        && observed == invented
    _ -> False

sourceSubjectDriftRejected :: Either String ()
sourceSubjectDriftRejected = do
  original <- uploadStagingEffectStage
  requirement <- requireUploadRequirement original
  let invented = RuntimePrimitiveExplicitSubject "upload.unrelated"
      bad = requirement { stagingRequirementSourceSubject = invented }
  expectRequirementError original bad $ \err -> case err of
    StagingRequirementSourceSubjectMissing actual subject ->
      actual == uploadDigestStagingRequirementKey && subject == invented
    _ -> False

emptyTargetSubjectRejected :: Either String ()
emptyTargetSubjectRejected = do
  original <- uploadStagingEffectStage
  requirement <- requireUploadRequirement original
  let bad = requirement
        { stagingRequirementTargetSubject = StagingTargetSubject "" }
  expectRequirementError original bad $ \err -> case err of
    StagingRequirementEmptyTargetSubject actual ->
      actual == uploadDigestStagingRequirementKey
    _ -> False

eventRequirementDriftRejected :: Either String ()
eventRequirementDriftRejected = do
  original <- uploadStagingEffectStage
  event <- requireUploadEvent original
  let invented = StagingRequirementKey "staging.upload.other.v1"
      bad = event { stagingEventRequirement = invented }
  expectEventError original bad $ \err -> case err of
    StagingEventRequirementMismatch actual expected observed ->
      actual == uploadDigestStagingRequirementKey
        && expected == uploadDigestStagingRequirementKey
        && observed == invented
    _ -> False

missingEffectRejected :: Either String ()
missingEffectRejected = do
  original <- uploadStagingEffectStage
  event <- requireUploadEvent original
  expectEventError original (event { stagingEventEffect = Nothing }) $ \err ->
    err == StagingEventMissingEffect uploadDigestStagingRequirementKey

emptyEffectRejected :: Either String ()
emptyEffectRejected = do
  original <- uploadStagingEffectStage
  event <- requireUploadEvent original
  expectEventError original
    (event { stagingEventEffect = Just (SemanticEffect "") }) $ \err ->
      err == StagingEventEmptyEffect uploadDigestStagingRequirementKey

missingAuthorityRejected :: Either String ()
missingAuthorityRejected = do
  original <- uploadStagingEffectStage
  event <- requireUploadEvent original
  expectEventError original (event { stagingEventAuthority = Nothing }) $ \err ->
    err == StagingEventMissingAuthority uploadDigestStagingRequirementKey

malformedAuthorityRejected :: Either String ()
malformedAuthorityRejected = do
  original <- uploadStagingEffectStage
  event <- requireUploadEvent original
  let malformed = AuthorityUse
        (AuthoritySubjectKey "")
        (AuthorityOperationKey "write")
  expectEventError original
    (event { stagingEventAuthority = Just (Set.singleton malformed) }) $ \err ->
      err == StagingEventInvalidAuthority
        uploadDigestStagingRequirementKey malformed

missingFailureRejected :: Either String ()
missingFailureRejected = do
  original <- uploadStagingEffectStage
  event <- requireUploadEvent original
  expectEventError original (event { stagingEventFailure = Nothing }) $ \err ->
    err == StagingEventMissingFailureSurface uploadDigestStagingRequirementKey

emptyFailureSetRejected :: Either String ()
emptyFailureSetRejected = do
  original <- uploadStagingEffectStage
  event <- requireUploadEvent original
  expectEventError original
    (event { stagingEventFailure = Just (StagingMayFail Set.empty) }) $ \err ->
      err == StagingEventEmptyFailureSet uploadDigestStagingRequirementKey

explicitInfallibilityAccepted :: Either String ()
explicitInfallibilityAccepted = do
  original <- uploadStagingEffectStage
  event <- requireUploadEvent original
  let mutated = replaceUploadEvent original
        (event { stagingEventFailure = Just StagingInfallible })
  mapLeft show (verifyStagingEffectStageBundle mutated)

missingTransferRejected :: Either String ()
missingTransferRejected = do
  original <- uploadStagingEffectStage
  event <- requireUploadEvent original
  expectEventError original
    (event { stagingEventSubjectTransfer = Nothing }) $ \err ->
      err == StagingEventMissingSubjectTransfer uploadDigestStagingRequirementKey

transferSourceDriftRejected :: Either String ()
transferSourceDriftRejected = do
  original <- uploadStagingEffectStage
  event <- requireUploadEvent original
  transfer <- requireTransfer event
  let invented = RuntimePrimitiveExplicitSubject "upload.unrelated"
      badTransfer = transfer { stagingTransferSource = invented }
  expectEventError original
    (event { stagingEventSubjectTransfer = Just badTransfer }) $ \err ->
      case err of
        StagingEventTransferSourceMismatch actual expected observed ->
          actual == uploadDigestStagingRequirementKey
            && expected == RuntimePrimitiveExplicitSubject "upload.payload"
            && observed == invented
        _ -> False

transferTargetDriftRejected :: Either String ()
transferTargetDriftRejected = do
  original <- uploadStagingEffectStage
  event <- requireUploadEvent original
  transfer <- requireTransfer event
  let invented = StagingTargetSubject "target.upload.payload.other"
      badTransfer = transfer { stagingTransferTarget = invented }
  expectEventError original
    (event { stagingEventSubjectTransfer = Just badTransfer }) $ \err ->
      case err of
        StagingEventTransferTargetMismatch actual expected observed ->
          actual == uploadDigestStagingRequirementKey
            && expected == uploadDigestStagingTargetSubject
            && observed == invented
        _ -> False

emptyTransferRevisionRejected :: Either String ()
emptyTransferRevisionRejected = do
  original <- uploadStagingEffectStage
  event <- requireUploadEvent original
  transfer <- requireTransfer event
  let badTransfer = transfer
        { stagingTransferRevision = StagingTransferRevision "" }
  expectEventError original
    (event { stagingEventSubjectTransfer = Just badTransfer }) $ \err ->
      err == StagingEventEmptyTransferRevision uploadDigestStagingRequirementKey

missingCostRejected :: Either String ()
missingCostRejected = do
  original <- uploadStagingEffectStage
  event <- requireUploadEvent original
  expectEventError original (event { stagingEventCost = Nothing }) $ \err ->
    err == StagingEventMissingCost uploadDigestStagingRequirementKey

wrongCostClassRejected :: Either String ()
wrongCostClassRejected = do
  original <- uploadStagingEffectStage
  event <- requireUploadEvent original
  cost <- requireCost event
  let bad = cost { stagingCostClass = SemanticRequired }
  expectEventError original (event { stagingEventCost = Just bad }) $ \err ->
    case err of
      StagingEventCostClassMismatch actual expected observed ->
        actual == uploadDigestStagingRequirementKey
          && expected == TargetRequired
          && observed == SemanticRequired
      _ -> False

missingBytesCopiedRejected :: Either String ()
missingBytesCopiedRejected = do
  original <- uploadStagingEffectStage
  event <- requireUploadEvent original
  cost <- requireCost event
  let shape = (stagingCostShape cost) { costBytesCopied = Nothing }
      bad = cost { stagingCostShape = shape }
  expectEventError original (event { stagingEventCost = Just bad }) $ \err ->
    err == StagingEventMissingBytesCopied uploadDigestStagingRequirementKey

missingFrequencyRejected :: Either String ()
missingFrequencyRejected = do
  original <- uploadStagingEffectStage
  event <- requireUploadEvent original
  cost <- requireCost event
  let shape = (stagingCostShape cost) { costFrequency = Nothing }
      bad = cost { stagingCostShape = shape }
  expectEventError original (event { stagingEventCost = Just bad }) $ \err ->
    err == StagingEventMissingFrequency uploadDigestStagingRequirementKey

duplicateCostIdentityRejected :: Either String ()
duplicateCostIdentityRejected = do
  original <- uploadStagingEffectStage
  requirement <- requireUploadRequirement original
  event <- requireUploadEvent original
  transfer <- requireTransfer event
  let secondKey = StagingRequirementKey "staging.upload.digest-input.second.v1"
      secondTarget = StagingTargetSubject "target.upload.payload.digest-staging.second"
      secondRequirement = requirement
        { stagingRequirementKey = secondKey
        , stagingRequirementTargetSubject = secondTarget
        }
      secondTransfer = transfer { stagingTransferTarget = secondTarget }
      secondEvent = event
        { stagingEventKey = secondKey
        , stagingEventRequirement = secondKey
        , stagingEventSubjectTransfer = Just secondTransfer
        }
      requirements = Map.insert secondKey secondRequirement
        (stagingEffectStageRequirements original)
      events = Map.insert secondKey secondEvent
        (stagingEffectStageEvents original)
      mutated = rebuild original requirements events
  case verifyStagingEffectStageBundle mutated of
    Left (StagingEventCostIdentityReused _ keys)
      | Set.member uploadDigestStagingRequirementKey keys
          && Set.member secondKey keys -> Right ()
    other -> Left ("duplicate staging cost identity was accepted: " <> show other)

deterministicIdentity :: Either String ()
deterministicIdentity = do
  original <- uploadStagingEffectStage
  let reverseMap value = Map.fromList (reverse (Map.toAscList value))
      rebuilt = makeStagingEffectStageBundle
        (stagingEffectStageBase original)
        (reverseMap (stagingEffectStageRequirements original))
        (reverseMap (stagingEffectStageEvents original))
  assert
    (stagingEffectStageRevision original == stagingEffectStageRevision rebuilt)
    "staging-effect revision changed with map enumeration order"
  mapLeft show (verifyStagingEffectStageBundle rebuilt)

expectRequirementError
  :: StagingEffectStageBundle
  -> StagingRequirement
  -> (StagingEffectVerificationError -> Bool)
  -> Either String ()
expectRequirementError original bad predicate =
  case verifyStagingEffectStageBundle mutated of
    Left err | predicate err -> Right ()
    other -> Left ("requirement mutation was accepted: " <> show other)
  where
    requirements = Map.insert uploadDigestStagingRequirementKey bad
      (stagingEffectStageRequirements original)
    mutated = rebuild original requirements (stagingEffectStageEvents original)

expectEventError
  :: StagingEffectStageBundle
  -> StagingEvent
  -> (StagingEffectVerificationError -> Bool)
  -> Either String ()
expectEventError original bad predicate =
  case verifyStagingEffectStageBundle (replaceUploadEvent original bad) of
    Left err | predicate err -> Right ()
    other -> Left ("event mutation was accepted: " <> show other)

replaceUploadEvent
  :: StagingEffectStageBundle
  -> StagingEvent
  -> StagingEffectStageBundle
replaceUploadEvent original event =
  rebuild original
    (stagingEffectStageRequirements original)
    (Map.insert uploadDigestStagingRequirementKey event
      (stagingEffectStageEvents original))

requireUploadRequirement
  :: StagingEffectStageBundle
  -> Either String StagingRequirement
requireUploadRequirement bundle = maybe
  (Left "upload staging requirement missing")
  Right
  (Map.lookup uploadDigestStagingRequirementKey
    (stagingEffectStageRequirements bundle))

requireUploadEvent
  :: StagingEffectStageBundle
  -> Either String StagingEvent
requireUploadEvent bundle = maybe
  (Left "upload staging event missing")
  Right
  (Map.lookup uploadDigestStagingRequirementKey
    (stagingEffectStageEvents bundle))

requireTransfer :: StagingEvent -> Either String StagingSubjectTransfer
requireTransfer event = maybe
  (Left "staging transfer missing")
  Right
  (stagingEventSubjectTransfer event)

requireCost :: StagingEvent -> Either String StagingCostAccount
requireCost event = maybe
  (Left "staging cost missing")
  Right
  (stagingEventCost event)

rebuild
  :: StagingEffectStageBundle
  -> Map.Map StagingRequirementKey StagingRequirement
  -> Map.Map StagingRequirementKey StagingEvent
  -> StagingEffectStageBundle
rebuild original = makeStagingEffectStageBundle
  (stagingEffectStageBase original)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
