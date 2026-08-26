{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.BoundaryCommitCorrespondence
  ( BoundaryCommitStageRevision (..)
  , BoundaryTransferKey (..)
  , BoundaryDirection (..)
  , BoundaryLengthBinding (..)
  , BoundaryTransferContract (..)
  , BoundaryCommitStageBundle (..)
  , BoundaryCommitVerificationError (..)
  , deriveBoundaryCommitStageRevision
  , makeBoundaryCommitStageBundle
  , verifyBoundaryCommitStageBundle
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types
  ( EvidenceEntryId
  , RevisionId
  )
import Phil.Core.Static
  ( SemanticForm (..)
  , canonicalSemanticForm
  )
import Phil.Systems.AuthorityEffectCorrespondence
  ( AuthorityEffectStageBundle (..)
  )
import Phil.Systems.BranchResourceFailure
  ( BranchResourceStageBundle (..)
  )
import Phil.Systems.ControlStateProjection
  ( ControlStateStageBundle (..)
  )
import Phil.Systems.IR
import Phil.Systems.Phase1Stage
  ( Phase1StageBundle (..)
  )
import Phil.Systems.ProtocolStateCorrespondence
import Phil.Systems.ProviderCallCorrespondence
  ( ProviderCallStageBundle (..)
  )
import Phil.Systems.SubjectCorrespondence
  ( SourceSubjectKey
  , SubjectCorrespondence (..)
  , SubjectStageBundle (..)
  , SystemsValueRef (..)
  )

newtype BoundaryCommitStageRevision = BoundaryCommitStageRevision
  { unBoundaryCommitStageRevision :: Text
  }
  deriving (Eq, Ord, Show)

newtype BoundaryTransferKey = BoundaryTransferKey
  { unBoundaryTransferKey :: Text
  }
  deriving (Eq, Ord, Show)

data BoundaryDirection
  = BoundaryReceiveExact
  | BoundarySendExact
  deriving (Eq, Ord, Show)

data BoundaryLengthBinding
  = ExplicitBoundaryLength
      { boundaryLengthSemanticKey :: Text
      , boundaryLengthValue :: SystemsValueRef
      }
  | OwnerIndexedBoundaryLength
      { boundaryLengthSemanticKey :: Text
      , boundaryLengthOwnerShape :: Text
      }
  deriving (Eq, Ord, Show)

data BoundaryTransferContract = BoundaryTransferContract
  { boundaryTransferKey :: BoundaryTransferKey
  , boundaryTransferDirection :: BoundaryDirection
  , boundaryTransferSourceFact :: Text
  , boundaryTransferSubject :: SourceSubjectKey
  , boundaryTransferTargetSite :: ProtocolTargetSite
  , boundaryTransferTransport :: SystemsValueRef
  , boundaryTransferOwner :: SystemsValueRef
  , boundaryTransferExpectedOwnerShape :: Text
  , boundaryTransferLength :: BoundaryLengthBinding
  , boundaryTransferProtocolTransition :: ProtocolTransitionKey
  , boundaryTransferCommitOutcome :: Text
  , boundaryTransferFailureOutcome :: Maybe Text
  }
  deriving (Eq, Ord, Show)

data BoundaryCommitStageBundle = BoundaryCommitStageBundle
  { boundaryCommitStageBase :: ProtocolStateStageBundle
  , boundaryCommitStageRevision :: BoundaryCommitStageRevision
  , boundaryCommitStageTransfers :: Map BoundaryTransferKey BoundaryTransferContract
  }
  deriving (Eq, Show)

data BoundaryCommitVerificationError
  = BoundaryCommitBaseStageError ProtocolStateVerificationError
  | BoundaryCommitStageRevisionMismatch BoundaryCommitStageRevision BoundaryCommitStageRevision
  | BoundaryTransferMapKeyMismatch BoundaryTransferKey BoundaryTransferKey
  | BoundaryTransferEmptySourceFact BoundaryTransferKey
  | BoundaryTransferUnknownSourceFact BoundaryTransferKey Text
  | BoundaryTransferSourceFactNotRuntimeRetained BoundaryTransferKey Text
  | BoundaryTransferSourceFactMissingRevision BoundaryTransferKey Text
  | BoundaryTransferTransportFunctionMismatch BoundaryTransferKey SystemsValueRef Text
  | BoundaryTransferOwnerFunctionMismatch BoundaryTransferKey SystemsValueRef Text
  | BoundaryTransferUnknownFunction BoundaryTransferKey Text
  | BoundaryTransferUnknownBlock BoundaryTransferKey BlockId
  | BoundaryTransferUnknownOperation BoundaryTransferKey Int
  | BoundaryTransferUnknownValue BoundaryTransferKey SystemsValueRef
  | BoundaryTransferValueNotTransport BoundaryTransferKey SystemsValueRef SystemsValueRole
  | BoundaryTransferValueNotOwner BoundaryTransferKey SystemsValueRef SystemsValueRole
  | BoundaryTransferOwnerShapeMismatch BoundaryTransferKey Text SystemsValueRole
  | BoundaryTransferUnknownSubject BoundaryTransferKey SourceSubjectKey
  | BoundaryTransferSubjectMismatch BoundaryTransferKey SourceSubjectKey SystemsValueRef
  | BoundaryTransferLengthFunctionMismatch BoundaryTransferKey SystemsValueRef Text
  | BoundaryTransferLengthValueMismatch BoundaryTransferKey SystemsValueRef SystemsValueRef
  | BoundaryTransferLengthModeMismatch BoundaryTransferKey BoundaryDirection BoundaryLengthBinding
  | BoundaryTransferTargetNotExactBoundary BoundaryTransferKey ProtocolTargetSite
  | BoundaryTransferTransportMismatch BoundaryTransferKey SystemsValueRef SystemsValueRef
  | BoundaryTransferOwnerMismatch BoundaryTransferKey SystemsValueRef SystemsValueRef
  | BoundaryTransferRuntimeSiteKindMismatch BoundaryTransferKey RuntimeSiteKind RuntimeSiteKind
  | BoundaryTransferRuntimeRevisionMismatch BoundaryTransferKey RevisionId RevisionId
  | BoundaryTransferRuntimeEvidenceMismatch BoundaryTransferKey EvidenceEntryId EvidenceEntryId
  | BoundaryTransferLegacySendInputsMismatch BoundaryTransferKey [ValueId]
  | BoundaryTransferLegacySendOutputsMismatch BoundaryTransferKey [ValueId]
  | BoundaryTransferUnknownProtocolTransition BoundaryTransferKey ProtocolTransitionKey
  | BoundaryTransferProtocolTargetMismatch BoundaryTransferKey ProtocolTargetSite ProtocolTargetSite
  | BoundaryTransferProtocolTransportMismatch BoundaryTransferKey SystemsValueRef SystemsValueRef
  | BoundaryTransferCommitOutcomeMissing BoundaryTransferKey Text
  | BoundaryTransferCommitOutcomeNotSuccessor BoundaryTransferKey Text ProtocolTransitionOutcome
  | BoundaryTransferFailureOutcomeMissing BoundaryTransferKey Text
  | BoundaryTransferFailureOutcomeNotTerminal BoundaryTransferKey Text ProtocolTransitionOutcome
  deriving (Eq, Show)

deriveBoundaryCommitStageRevision
  :: BoundaryCommitStageBundle
  -> BoundaryCommitStageRevision
deriveBoundaryCommitStageRevision bundle = BoundaryCommitStageRevision
  ("phil.phase1.boundary-commit-stage.canonical.v1:"
    <> canonicalSemanticForm (SemanticRecord (Map.fromList
      [ ("base_stage", SemanticAtom (protocolBaseRevisionText
          (boundaryCommitStageBase bundle)))
      , ("transfers", SemanticRecord (Map.fromList
          [ (unBoundaryTransferKey key, semanticTransfer transfer)
          | (key, transfer) <- Map.toAscList (boundaryCommitStageTransfers bundle)
          ]))
      ])))

makeBoundaryCommitStageBundle
  :: ProtocolStateStageBundle
  -> Map BoundaryTransferKey BoundaryTransferContract
  -> BoundaryCommitStageBundle
makeBoundaryCommitStageBundle base transfers = provisional
  { boundaryCommitStageRevision = deriveBoundaryCommitStageRevision provisional }
  where
    provisional = BoundaryCommitStageBundle
      { boundaryCommitStageBase = base
      , boundaryCommitStageRevision = BoundaryCommitStageRevision "pending"
      , boundaryCommitStageTransfers = transfers
      }

verifyBoundaryCommitStageBundle
  :: BoundaryCommitStageBundle
  -> Either BoundaryCommitVerificationError ()
verifyBoundaryCommitStageBundle bundle = do
  mapLeft BoundaryCommitBaseStageError $
    verifyProtocolStateStageBundle (boundaryCommitStageBase bundle)
  requireEqual BoundaryCommitStageRevisionMismatch
    (deriveBoundaryCommitStageRevision bundle)
    (boundaryCommitStageRevision bundle)
  mapM_ (checkTransfer bundle)
    (Map.toAscList (boundaryCommitStageTransfers bundle))

checkTransfer
  :: BoundaryCommitStageBundle
  -> (BoundaryTransferKey, BoundaryTransferContract)
  -> Either BoundaryCommitVerificationError ()
checkTransfer bundle (key, transfer) = do
  requireEqual BoundaryTransferMapKeyMismatch key (boundaryTransferKey transfer)
  if Text.null (boundaryTransferSourceFact transfer)
    then Left (BoundaryTransferEmptySourceFact key)
    else Right ()
  (sourceRevision, sourceEvidence) <- sourceRuntimeFact
    key (boundaryTransferSourceFact transfer) artifact
  let targetSite = boundaryTransferTargetSite transfer
      functionName = targetSiteFunction targetSite
      transportRef = boundaryTransferTransport transfer
      ownerRef = boundaryTransferOwner transfer
  if systemsValueRefFunction transportRef /= functionName
    then Left (BoundaryTransferTransportFunctionMismatch key transportRef functionName)
    else Right ()
  if systemsValueRefFunction ownerRef /= functionName
    then Left (BoundaryTransferOwnerFunctionMismatch key ownerRef functionName)
    else Right ()
  function <- lookupFunction key functionName program
  transportValue <- lookupValue key function transportRef
  ownerValue <- lookupValue key function ownerRef
  case systemsValueRole transportValue of
    TransportHandle -> Right ()
    role -> Left (BoundaryTransferValueNotTransport key transportRef role)
  case systemsValueRole ownerValue of
    OwnedBuffer shape
      | shape == boundaryTransferExpectedOwnerShape transfer -> Right ()
      | otherwise -> Left (BoundaryTransferOwnerShapeMismatch key
          (boundaryTransferExpectedOwnerShape transfer) (systemsValueRole ownerValue))
    role -> Left (BoundaryTransferValueNotOwner key ownerRef role)
  checkSubject key transfer subjectStage
  runtimeSite <- checkTarget key transfer function
  let expectedKind = case boundaryTransferDirection transfer of
        BoundaryReceiveExact -> ExactReceiveBoundary
        BoundarySendExact -> ExactSendBoundary
  requireEqual (BoundaryTransferRuntimeSiteKindMismatch key)
    expectedKind (runtimeSiteKind runtimeSite)
  requireEqual (BoundaryTransferRuntimeRevisionMismatch key)
    sourceRevision (runtimeSiteRevision runtimeSite)
  requireEqual (BoundaryTransferRuntimeEvidenceMismatch key)
    sourceEvidence (runtimeSiteEvidence runtimeSite)
  checkProtocolCommit key transfer (boundaryCommitStageBase bundle)
  where
    protocolBase = boundaryCommitStageBase bundle
    subjectStage = protocolSubjectStage protocolBase
    artifact = phase1StageSystemsArtifact (subjectStageBase subjectStage)
    program = systemsArtifactProgram artifact

checkSubject
  :: BoundaryTransferKey
  -> BoundaryTransferContract
  -> SubjectStageBundle
  -> Either BoundaryCommitVerificationError ()
checkSubject key transfer subjectStage =
  case Map.lookup (boundaryTransferSubject transfer)
      (subjectStageCorrespondences subjectStage) of
    Nothing -> Left (BoundaryTransferUnknownSubject key (boundaryTransferSubject transfer))
    Just correspondence ->
      if Set.member (boundaryTransferOwner transfer)
          (subjectCorrespondenceSystemsValues correspondence)
        then Right ()
        else Left (BoundaryTransferSubjectMismatch key
          (boundaryTransferSubject transfer) (boundaryTransferOwner transfer))

checkTarget
  :: BoundaryTransferKey
  -> BoundaryTransferContract
  -> SystemsFunction
  -> Either BoundaryCommitVerificationError RuntimeSiteRef
checkTarget key transfer function =
  case boundaryTransferTargetSite transfer of
    ProtocolTerminatorSite _ blockId -> do
      blockValue <- lookupBlock key blockId function
      case (boundaryTransferDirection transfer, systemsBlockTerminator blockValue) of
        ( BoundaryReceiveExact
          , TermReceiveExact actualTransport actualLength actualOwner site _ _
          ) -> do
            requireRefEqual (BoundaryTransferTransportMismatch key)
              (boundaryTransferTransport transfer) function actualTransport
            requireRefEqual (BoundaryTransferOwnerMismatch key)
              (boundaryTransferOwner transfer) function actualOwner
            case boundaryTransferLength transfer of
              ExplicitBoundaryLength _ lengthRef -> do
                checkLengthFunction key lengthRef (systemsFunctionName function)
                _ <- lookupValue key function lengthRef
                requireRefEqual (BoundaryTransferLengthValueMismatch key)
                  lengthRef function actualLength
              binding -> Left (BoundaryTransferLengthModeMismatch key
                  BoundaryReceiveExact binding)
            Right site
        ( BoundarySendExact
          , TermSendExact actualTransport actualOwner site _ _
          ) -> do
            requireRefEqual (BoundaryTransferTransportMismatch key)
              (boundaryTransferTransport transfer) function actualTransport
            requireRefEqual (BoundaryTransferOwnerMismatch key)
              (boundaryTransferOwner transfer) function actualOwner
            checkOwnerIndexedLength key transfer
            Right site
        _ -> Left (BoundaryTransferTargetNotExactBoundary key
            (boundaryTransferTargetSite transfer))
    ProtocolOperationSite _ blockId operationIndex -> do
      blockValue <- lookupBlock key blockId function
      operation <- maybe
        (Left (BoundaryTransferUnknownOperation key operationIndex))
        Right
        (indexMaybe operationIndex (systemsBlockOps blockValue))
      case (boundaryTransferDirection transfer, operation) of
        ( BoundarySendExact
          , OpRuntimeCall
              { runtimeCallInputs = inputs
              , runtimeCallOutputs = outputs
              , runtimeCallSite = Just site
              }
          ) -> do
            let transport = systemsValueRefValue (boundaryTransferTransport transfer)
                owner = systemsValueRefValue (boundaryTransferOwner transfer)
            if inputs == [transport, owner]
              then Right ()
              else Left (BoundaryTransferLegacySendInputsMismatch key inputs)
            if null outputs
              then Right ()
              else Left (BoundaryTransferLegacySendOutputsMismatch key outputs)
            checkOwnerIndexedLength key transfer
            Right site
        _ -> Left (BoundaryTransferTargetNotExactBoundary key
            (boundaryTransferTargetSite transfer))

checkOwnerIndexedLength
  :: BoundaryTransferKey
  -> BoundaryTransferContract
  -> Either BoundaryCommitVerificationError ()
checkOwnerIndexedLength key transfer =
  case boundaryTransferLength transfer of
    OwnerIndexedBoundaryLength semanticKey ownerShape
      | not (Text.null semanticKey)
          && ownerShape == boundaryTransferExpectedOwnerShape transfer -> Right ()
      | otherwise -> Left (BoundaryTransferLengthModeMismatch key
          BoundarySendExact (boundaryTransferLength transfer))
    binding -> Left (BoundaryTransferLengthModeMismatch key BoundarySendExact binding)

checkLengthFunction
  :: BoundaryTransferKey
  -> SystemsValueRef
  -> Text
  -> Either BoundaryCommitVerificationError ()
checkLengthFunction key ref functionName
  | systemsValueRefFunction ref == functionName = Right ()
  | otherwise = Left (BoundaryTransferLengthFunctionMismatch key ref functionName)

checkProtocolCommit
  :: BoundaryTransferKey
  -> BoundaryTransferContract
  -> ProtocolStateStageBundle
  -> Either BoundaryCommitVerificationError ()
checkProtocolCommit key transfer base = do
  transition <- maybe
    (Left (BoundaryTransferUnknownProtocolTransition key
      (boundaryTransferProtocolTransition transfer)))
    Right
    (Map.lookup (boundaryTransferProtocolTransition transfer)
      (protocolStateStageTransitions base))
  requireEqual (BoundaryTransferProtocolTargetMismatch key)
    (boundaryTransferTargetSite transfer)
    (protocolTransitionTargetSite transition)
  requireEqual (BoundaryTransferProtocolTransportMismatch key)
    (boundaryTransferTransport transfer)
    (protocolTransitionTransport transition)
  commit <- maybe
    (Left (BoundaryTransferCommitOutcomeMissing key
      (boundaryTransferCommitOutcome transfer)))
    Right
    (Map.lookup (boundaryTransferCommitOutcome transfer)
      (protocolTransitionOutcomes transition))
  case commit of
    ProtocolSuccessor _ -> Right ()
    outcome -> Left (BoundaryTransferCommitOutcomeNotSuccessor key
      (boundaryTransferCommitOutcome transfer) outcome)
  case boundaryTransferFailureOutcome transfer of
    Nothing -> Right ()
    Just label -> do
      failure <- maybe
        (Left (BoundaryTransferFailureOutcomeMissing key label))
        Right
        (Map.lookup label (protocolTransitionOutcomes transition))
      case failure of
        ProtocolTerminal _ -> Right ()
        outcome -> Left (BoundaryTransferFailureOutcomeNotTerminal key label outcome)

sourceRuntimeFact
  :: BoundaryTransferKey
  -> Text
  -> SystemsArtifact
  -> Either BoundaryCommitVerificationError (RevisionId, EvidenceEntryId)
sourceRuntimeFact key factId artifact =
  case [fact | fact <- stageFacts (systemsArtifactStageContract artifact)
             , factTransferId fact == factId] of
    [] -> Left (BoundaryTransferUnknownSourceFact key factId)
    fact : _ -> case factSourceRevision fact of
      Nothing -> Left (BoundaryTransferSourceFactMissingRevision key factId)
      Just revision -> case factDisposition fact of
        FactRuntimeRetained evidence -> Right (revision, evidence)
        _ -> Left (BoundaryTransferSourceFactNotRuntimeRetained key factId)

lookupFunction
  :: BoundaryTransferKey
  -> Text
  -> SystemsProgram
  -> Either BoundaryCommitVerificationError SystemsFunction
lookupFunction key functionName program = maybe
  (Left (BoundaryTransferUnknownFunction key functionName))
  Right
  (Map.lookup functionName (systemsProgramFunctions program))

lookupBlock
  :: BoundaryTransferKey
  -> BlockId
  -> SystemsFunction
  -> Either BoundaryCommitVerificationError SystemsBlock
lookupBlock key blockId function = maybe
  (Left (BoundaryTransferUnknownBlock key blockId))
  Right
  (Map.lookup blockId (systemsFunctionBlocks function))

lookupValue
  :: BoundaryTransferKey
  -> SystemsFunction
  -> SystemsValueRef
  -> Either BoundaryCommitVerificationError SystemsValue
lookupValue key function ref = maybe
  (Left (BoundaryTransferUnknownValue key ref))
  Right
  (Map.lookup (systemsValueRefValue ref) (systemsFunctionValues function))

requireRefEqual
  :: (SystemsValueRef -> SystemsValueRef -> BoundaryCommitVerificationError)
  -> SystemsValueRef
  -> SystemsFunction
  -> ValueId
  -> Either BoundaryCommitVerificationError ()
requireRefEqual mkError expected function actualValue =
  requireEqual mkError expected (SystemsValueRef (systemsFunctionName function) actualValue)

protocolSubjectStage :: ProtocolStateStageBundle -> SubjectStageBundle
protocolSubjectStage =
  providerCallStageBase
  . authorityEffectStageBase
  . branchResourceStageBase
  . controlStateStageBase
  . protocolStateStageBase

protocolBaseRevisionText :: ProtocolStateStageBundle -> Text
protocolBaseRevisionText bundle =
  unProtocolStateStageRevision (protocolStateStageRevision bundle)

targetSiteFunction :: ProtocolTargetSite -> Text
targetSiteFunction site = case site of
  ProtocolOperationSite functionName _ _ -> functionName
  ProtocolTerminatorSite functionName _ -> functionName

indexMaybe :: Int -> [a] -> Maybe a
indexMaybe index values
  | index < 0 = Nothing
  | otherwise = case drop index values of
      value : _ -> Just value
      [] -> Nothing

semanticTransfer :: BoundaryTransferContract -> SemanticForm
semanticTransfer transfer = SemanticRecord (Map.fromList
  [ ("key", SemanticAtom (unBoundaryTransferKey (boundaryTransferKey transfer)))
  , ("direction", SemanticAtom (directionText (boundaryTransferDirection transfer)))
  , ("source_fact", SemanticAtom (boundaryTransferSourceFact transfer))
  , ("subject", SemanticAtom (showText (boundaryTransferSubject transfer)))
  , ("target_site", semanticTargetSite (boundaryTransferTargetSite transfer))
  , ("transport", semanticValueRef (boundaryTransferTransport transfer))
  , ("owner", semanticValueRef (boundaryTransferOwner transfer))
  , ("owner_shape", SemanticAtom (boundaryTransferExpectedOwnerShape transfer))
  , ("length", semanticLength (boundaryTransferLength transfer))
  , ("protocol_transition", SemanticAtom
      (unProtocolTransitionKey (boundaryTransferProtocolTransition transfer)))
  , ("commit_outcome", SemanticAtom (boundaryTransferCommitOutcome transfer))
  , ("failure_outcome", maybe (SemanticAtom "none") SemanticAtom
      (boundaryTransferFailureOutcome transfer))
  ])

directionText :: BoundaryDirection -> Text
directionText direction = case direction of
  BoundaryReceiveExact -> "receive-exact"
  BoundarySendExact -> "send-exact"

semanticLength :: BoundaryLengthBinding -> SemanticForm
semanticLength binding = case binding of
  ExplicitBoundaryLength semanticKey ref -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "explicit-value")
    , ("semantic_key", SemanticAtom semanticKey)
    , ("value", semanticValueRef ref)
    ])
  OwnerIndexedBoundaryLength semanticKey ownerShape -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "owner-indexed")
    , ("semantic_key", SemanticAtom semanticKey)
    , ("owner_shape", SemanticAtom ownerShape)
    ])

semanticTargetSite :: ProtocolTargetSite -> SemanticForm
semanticTargetSite site = case site of
  ProtocolOperationSite functionName blockId operationIndex -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "operation")
    , ("function", SemanticAtom functionName)
    , ("block", SemanticAtom (unBlockId blockId))
    , ("index", SemanticAtom (Text.pack (show operationIndex)))
    ])
  ProtocolTerminatorSite functionName blockId -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "terminator")
    , ("function", SemanticAtom functionName)
    , ("block", SemanticAtom (unBlockId blockId))
    ])

semanticValueRef :: SystemsValueRef -> SemanticForm
semanticValueRef ref = SemanticRecord (Map.fromList
  [ ("function", SemanticAtom (systemsValueRefFunction ref))
  , ("value", SemanticAtom (unValueId (systemsValueRefValue ref)))
  ])

showText :: Show a => a -> Text
showText = Text.pack . show

requireEqual :: Eq a => (a -> a -> e) -> a -> a -> Either e ()
requireEqual mkError expected actual
  | expected == actual = Right ()
  | otherwise = Left (mkError expected actual)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
