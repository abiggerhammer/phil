{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.BranchResourceFailure
  ( BranchResourceStageRevision (..)
  , BranchControlClass (..)
  , BranchOwnerFate (..)
  , BranchOutcomeContract (..)
  , BranchSiteContract (..)
  , BranchResourceStageBundle (..)
  , BranchResourceStageVerificationError (..)
  , deriveBranchResourceStageRevision
  , makeBranchResourceStageBundle
  , verifyBranchResourceStageBundle
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Static
  ( SemanticForm (..)
  , canonicalSemanticForm
  )
import Phil.Systems.AuthorityEffectCorrespondence
  ( AuthorityEffectStageBundle (..)
  , AuthorityEffectStageRevision (..)
  , AuthorityEffectStageVerificationError
  , verifyAuthorityEffectStageBundle
  )
import Phil.Systems.IR
import Phil.Systems.Phase1Stage
  ( Phase1StageBundle (..)
  , SystemsMechanismKey (..)
  )
import Phil.Systems.ProviderCallCorrespondence
  ( ProviderCallStageBundle (..)
  )
import Phil.Systems.SubjectCorrespondence
  ( SubjectStageBundle (..)
  )

newtype BranchResourceStageRevision = BranchResourceStageRevision
  { unBranchResourceStageRevision :: Text
  }
  deriving (Eq, Ord, Show)

data BranchControlClass
  = BranchContinues
  | BranchEnds Text
  | BranchFatal Text
  deriving (Eq, Ord, Show)

data BranchOwnerFate
  = OwnerContinues
  | OwnerReleased
  | OwnerReturnedAtTerminal
  deriving (Eq, Ord, Show)

data BranchOutcomeContract = BranchOutcomeContract
  { branchOutcomeSemanticRef :: Text
  , branchOutcomeOwnerFates :: Map ValueId BranchOwnerFate
  , branchOutcomeControlClass :: BranchControlClass
  }
  deriving (Eq, Ord, Show)

data BranchSiteContract = BranchSiteContract
  { branchSiteMechanism :: SystemsMechanismKey
  , branchSiteFunction :: Text
  , branchSiteBlock :: BlockId
  , branchSiteTrackedOwners :: Set ValueId
  , branchSiteOutcomes :: Map Text BranchOutcomeContract
  }
  deriving (Eq, Ord, Show)

data BranchResourceStageBundle = BranchResourceStageBundle
  { branchResourceStageBase :: AuthorityEffectStageBundle
  , branchResourceStageRevision :: BranchResourceStageRevision
  , branchResourceStageSites :: Map SystemsMechanismKey BranchSiteContract
  }
  deriving (Eq, Show)

data BranchResourceStageVerificationError
  = BranchResourceBaseStageError AuthorityEffectStageVerificationError
  | BranchResourceStageRevisionMismatch BranchResourceStageRevision BranchResourceStageRevision
  | BranchResourceSiteMapKeyMismatch SystemsMechanismKey SystemsMechanismKey
  | BranchResourceUnknownMechanism SystemsMechanismKey
  | BranchResourceUnknownFunction SystemsMechanismKey Text
  | BranchResourceUnknownBlock SystemsMechanismKey BlockId
  | BranchResourceMechanismMismatch SystemsMechanismKey SystemsMechanismKey
  | BranchResourceSiteNotBranching SystemsMechanismKey
  | BranchResourceOutcomeDomainMismatch SystemsMechanismKey (Set Text) (Set Text)
  | BranchResourceEmptySemanticOutcome SystemsMechanismKey Text
  | BranchResourceTrackedOwnerUnknown SystemsMechanismKey ValueId
  | BranchResourceTrackedValueNotOwning SystemsMechanismKey ValueId SystemsValueRole
  | BranchResourceOwnerFateDomainMismatch SystemsMechanismKey Text (Set ValueId) (Set ValueId)
  | BranchResourceControlClassMismatch SystemsMechanismKey Text BranchControlClass BranchControlClass
  | BranchResourceOwnerReleasedUnexpectedly SystemsMechanismKey Text ValueId
  | BranchResourceOwnerReleaseMissing SystemsMechanismKey Text ValueId
  | BranchResourceOwnerDoubleReleased SystemsMechanismKey Text ValueId Int
  | BranchResourceOwnerContinuesOnTerminal SystemsMechanismKey Text ValueId BranchControlClass
  | BranchResourceOwnerReturnNotTerminal SystemsMechanismKey Text ValueId BranchControlClass
  deriving (Eq, Show)

deriveBranchResourceStageRevision
  :: BranchResourceStageBundle
  -> BranchResourceStageRevision
deriveBranchResourceStageRevision bundle = BranchResourceStageRevision
  ("phil.phase1.branch-resource-stage.canonical.v1:"
    <> canonicalSemanticForm (SemanticRecord (Map.fromList
      [ ("base_stage", SemanticAtom
          (unAuthorityEffectStageRevision
            (authorityEffectStageRevision (branchResourceStageBase bundle))))
      , ("sites", SemanticRecord (Map.fromList
          [ (unSystemsMechanismKey key, semanticSite site)
          | (key, site) <- Map.toAscList (branchResourceStageSites bundle)
          ]))
      ])))

makeBranchResourceStageBundle
  :: AuthorityEffectStageBundle
  -> Map SystemsMechanismKey BranchSiteContract
  -> BranchResourceStageBundle
makeBranchResourceStageBundle base sites =
  provisional
    { branchResourceStageRevision = deriveBranchResourceStageRevision provisional }
  where
    provisional = BranchResourceStageBundle
      { branchResourceStageBase = base
      , branchResourceStageRevision = BranchResourceStageRevision "pending"
      , branchResourceStageSites = sites
      }

verifyBranchResourceStageBundle
  :: BranchResourceStageBundle
  -> Either BranchResourceStageVerificationError ()
verifyBranchResourceStageBundle bundle = do
  mapLeft BranchResourceBaseStageError $
    verifyAuthorityEffectStageBundle (branchResourceStageBase bundle)
  requireEqual BranchResourceStageRevisionMismatch
    (deriveBranchResourceStageRevision bundle)
    (branchResourceStageRevision bundle)
  mapM_ (checkBranchSite bundle) (Map.toAscList (branchResourceStageSites bundle))

checkBranchSite
  :: BranchResourceStageBundle
  -> (SystemsMechanismKey, BranchSiteContract)
  -> Either BranchResourceStageVerificationError ()
checkBranchSite bundle (key, site) = do
  requireEqual BranchResourceSiteMapKeyMismatch key (branchSiteMechanism site)
  let baseStage = subjectStageBase
        (providerCallStageBase
          (authorityEffectStageBase (branchResourceStageBase bundle)))
      mechanisms = phase1StageSystemsMechanisms baseStage
  if Set.member key mechanisms
    then Right ()
    else Left (BranchResourceUnknownMechanism key)
  let artifact = phase1StageSystemsArtifact baseStage
      functions = systemsProgramFunctions (systemsArtifactProgram artifact)
  function <- case Map.lookup (branchSiteFunction site) functions of
    Just value -> Right value
    Nothing -> Left (BranchResourceUnknownFunction key (branchSiteFunction site))
  blockValue <- case Map.lookup (branchSiteBlock site) (systemsFunctionBlocks function) of
    Just value -> Right value
    Nothing -> Left (BranchResourceUnknownBlock key (branchSiteBlock site))
  let actualMechanism = terminatorMechanismKey
        (branchSiteFunction site) (branchSiteBlock site)
        (systemsBlockTerminator blockValue)
  requireEqual BranchResourceMechanismMismatch key actualMechanism
  arms <- case terminatorArms (systemsBlockTerminator blockValue) of
    Just value -> Right value
    Nothing -> Left (BranchResourceSiteNotBranching key)
  requireEqual (BranchResourceOutcomeDomainMismatch key)
    (Map.keysSet arms) (Map.keysSet (branchSiteOutcomes site))
  mapM_ (checkTrackedOwner key function) (Set.toAscList (branchSiteTrackedOwners site))
  mapM_ (checkOutcome key site function arms)
    (Map.toAscList (branchSiteOutcomes site))

checkTrackedOwner
  :: SystemsMechanismKey
  -> SystemsFunction
  -> ValueId
  -> Either BranchResourceStageVerificationError ()
checkTrackedOwner mechanism function owner =
  case Map.lookup owner (systemsFunctionValues function) of
    Nothing -> Left (BranchResourceTrackedOwnerUnknown mechanism owner)
    Just value
      | isOwningRole (systemsValueRole value) -> Right ()
      | otherwise -> Left (BranchResourceTrackedValueNotOwning
          mechanism owner (systemsValueRole value))

checkOutcome
  :: SystemsMechanismKey
  -> BranchSiteContract
  -> SystemsFunction
  -> Map Text BlockId
  -> (Text, BranchOutcomeContract)
  -> Either BranchResourceStageVerificationError ()
checkOutcome mechanism site function arms (label, contract) = do
  if Text.null (branchOutcomeSemanticRef contract)
    then Left (BranchResourceEmptySemanticOutcome mechanism label)
    else Right ()
  let tracked = branchSiteTrackedOwners site
      actualFateDomain = Map.keysSet (branchOutcomeOwnerFates contract)
  requireEqual (BranchResourceOwnerFateDomainMismatch mechanism label)
    tracked actualFateDomain
  target <- case Map.lookup label arms of
    Just value -> Right value
    Nothing -> Left (BranchResourceOutcomeDomainMismatch
      mechanism (Map.keysSet arms) (Map.keysSet (branchSiteOutcomes site)))
  targetBlock <- case Map.lookup target (systemsFunctionBlocks function) of
    Just value -> Right value
    Nothing -> Left (BranchResourceUnknownBlock mechanism target)
  let actualControl = targetControlClass (systemsBlockTerminator targetBlock)
      expectedControl = branchOutcomeControlClass contract
  requireEqual (BranchResourceControlClassMismatch mechanism label)
    expectedControl actualControl
  let releases = releaseCounts (systemsBlockOps targetBlock)
  mapM_ (checkFate mechanism label actualControl releases)
    (Map.toAscList (branchOutcomeOwnerFates contract))

checkFate
  :: SystemsMechanismKey
  -> Text
  -> BranchControlClass
  -> Map ValueId Int
  -> (ValueId, BranchOwnerFate)
  -> Either BranchResourceStageVerificationError ()
checkFate mechanism label control releases (owner, fate) = do
  let count = Map.findWithDefault 0 owner releases
  if count > 1
    then Left (BranchResourceOwnerDoubleReleased mechanism label owner count)
    else case fate of
      OwnerContinues
        | count /= 0 -> Left (BranchResourceOwnerReleasedUnexpectedly mechanism label owner)
        | control /= BranchContinues ->
            Left (BranchResourceOwnerContinuesOnTerminal mechanism label owner control)
        | otherwise -> Right ()
      OwnerReleased
        | count == 1 -> Right ()
        | otherwise -> Left (BranchResourceOwnerReleaseMissing mechanism label owner)
      OwnerReturnedAtTerminal
        | count /= 0 -> Left (BranchResourceOwnerReleasedUnexpectedly mechanism label owner)
        | isNormalTerminal control -> Right ()
        | otherwise -> Left (BranchResourceOwnerReturnNotTerminal mechanism label owner control)

releaseCounts :: [SystemsOp] -> Map ValueId Int
releaseCounts = Map.fromListWith (+) . concatMap releasedByOperation
  where
    releasedByOperation operation = case operation of
      OpReleaseOwner owner _ -> [(owner, 1)]
      OpCleanupPartial owner _ -> [(owner, 1)]
      OpDestroyPending pending frame _ -> [(pending, 1), (frame, 1)]
      _ -> []

terminatorArms :: SystemsTerminator -> Maybe (Map Text BlockId)
terminatorArms terminator = case terminator of
  TermBranch _ trueTarget falseTarget -> Just (Map.fromList
    [("true", trueTarget), ("false", falseTarget)])
  TermRecognize { recognizeSuccess = success, recognizeFailure = failure } ->
    Just (successFailure success failure)
  TermRuntimeCheck { checkSuccess = success, checkFailure = failure } ->
    Just (successFailure success failure)
  TermReceiveExact { exactSuccess = success, exactFailure = failure } ->
    Just (successFailure success failure)
  TermSendExact { sendExactSuccess = success, sendExactFailure = failure } ->
    Just (successFailure success failure)
  TermStore { storeSuccess = success, storeFailure = failure } ->
    Just (successFailure success failure)
  TermSessionOffer { sessionOfferArms = arms } ->
    Just (Map.map choiceArmTarget arms)
  TermRuntimeChoice { runtimeChoiceArms = arms } ->
    Just (Map.map runtimeChoiceArmTarget arms)
  _ -> Nothing
  where
    successFailure success failure = Map.fromList
      [("success", success), ("failure", failure)]

terminatorMechanismKey :: Text -> BlockId -> SystemsTerminator -> SystemsMechanismKey
terminatorMechanismKey functionName blockId terminator = SystemsMechanismKey
  (functionName <> ":" <> unBlockId blockId <> ":term." <> terminatorKind terminator)

terminatorKind :: SystemsTerminator -> Text
terminatorKind terminator = case terminator of
  TermJump {} -> "jump"
  TermBranch {} -> "branch"
  TermRecognize {} -> "recognize"
  TermRuntimeCheck {} -> "runtime-check"
  TermReceiveExact {} -> "receive-exact"
  TermSendExact {} -> "send-exact"
  TermStore {} -> "store"
  TermSessionOffer {} -> "session-offer"
  TermRuntimeChoice { runtimeChoiceName = name } -> "runtime-choice." <> name
  TermReturnScalar {} -> "return-scalar"
  TermEnd reason -> "end." <> reason
  TermFatal reason -> "fatal." <> reason

targetControlClass :: SystemsTerminator -> BranchControlClass
targetControlClass terminator = case terminator of
  TermEnd reason -> BranchEnds reason
  TermFatal reason -> BranchFatal reason
  _ -> BranchContinues

isNormalTerminal :: BranchControlClass -> Bool
isNormalTerminal control = case control of
  BranchEnds _ -> True
  _ -> False

isOwningRole :: SystemsValueRole -> Bool
isOwningRole role = case role of
  TransportHandle -> True
  PendingIngress _ -> True
  FrameOwner _ -> True
  OwnedBuffer _ -> True
  _ -> False

semanticSite :: BranchSiteContract -> SemanticForm
semanticSite site = SemanticRecord (Map.fromList
  [ ("mechanism", SemanticAtom (unSystemsMechanismKey (branchSiteMechanism site)))
  , ("function", SemanticAtom (branchSiteFunction site))
  , ("block", SemanticAtom (unBlockId (branchSiteBlock site)))
  , ("tracked_owners", SemanticUnordered
      (Set.map (SemanticAtom . unValueId) (branchSiteTrackedOwners site)))
  , ("outcomes", SemanticRecord (Map.fromList
      [ (label, semanticOutcome outcome)
      | (label, outcome) <- Map.toAscList (branchSiteOutcomes site)
      ]))
  ])

semanticOutcome :: BranchOutcomeContract -> SemanticForm
semanticOutcome outcome = SemanticRecord (Map.fromList
  [ ("semantic_ref", SemanticAtom (branchOutcomeSemanticRef outcome))
  , ("owner_fates", SemanticRecord (Map.fromList
      [ (unValueId owner, SemanticAtom (ownerFateText fate))
      | (owner, fate) <- Map.toAscList (branchOutcomeOwnerFates outcome)
      ]))
  , ("control", semanticControl (branchOutcomeControlClass outcome))
  ])

ownerFateText :: BranchOwnerFate -> Text
ownerFateText fate = case fate of
  OwnerContinues -> "continues"
  OwnerReleased -> "released"
  OwnerReturnedAtTerminal -> "returned-at-terminal"

semanticControl :: BranchControlClass -> SemanticForm
semanticControl control = case control of
  BranchContinues -> SemanticAtom "continues"
  BranchEnds reason -> SemanticRecord (Map.fromList
    [("kind", SemanticAtom "end"), ("reason", SemanticAtom reason)])
  BranchFatal reason -> SemanticRecord (Map.fromList
    [("kind", SemanticAtom "fatal"), ("reason", SemanticAtom reason)])

requireEqual :: Eq a => (a -> a -> e) -> a -> a -> Either e ()
requireEqual mkError expected actual
  | expected == actual = Right ()
  | otherwise = Left (mkError expected actual)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
