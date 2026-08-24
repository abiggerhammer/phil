{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.RecognitionFailure
  ( RecognitionFailureWitness (..)
  , RecognitionFailureBundle (..)
  , RecognitionFailureError (..)
  , phase0RecognitionFailureWitnesses
  , phase0RecognitionFailureBundle
  , verifyRecognitionFailureBundle
  , verifyRecognitionFailureWitnesses
  ) where

import Control.Monad (foldM, forM_, unless, when)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Assurance.Types
import Phil.Systems.ClientOutbound
import Phil.Systems.Dataflow
import Phil.Systems.IR
import Phil.Systems.Verify

data RecognitionFailureWitness = RecognitionFailureWitness
  { recognitionFailureFunction :: Text
  , recognitionFailureRecognitionBlock :: BlockId
  , recognitionFailureFailureBlock :: BlockId
  , recognitionFailurePending :: ValueId
  , recognitionFailureFrameOwner :: ValueId
  , recognitionFailureGrammar :: Text
  , recognitionFailureReason :: ValueId
  , recognitionFailureMaterializeCall :: Text
  , recognitionFailureEffectCall :: Text
  , recognitionFailureFatalClass :: Text
  }
  deriving (Eq, Show)

data RecognitionFailureBundle = RecognitionFailureBundle
  { recognitionFailureArtifact :: SystemsArtifact
  , recognitionFailureContext :: SystemsVerificationContext
  , recognitionFailurePredecessor :: ClientOutboundBundle
  , recognitionFailureWitnesses :: [RecognitionFailureWitness]
  }
  deriving (Eq, Show)

data RecognitionFailureError
  = RecognitionFailurePredecessorError ClientOutboundError
  | RecognitionFailureSystemsError SystemsVerificationError
  | RecognitionFailureDataflowError ScalarDataflowError
  | RecognitionFailureClientOutboundRegression ClientOutboundError
  | RecognitionFailureFunctionMissing Text
  | RecognitionFailureBlockMissing Text BlockId
  | RecognitionFailureValueMissing Text ValueId
  | RecognitionFailureValueRoleMismatch Text ValueId SystemsValueRole
  | RecognitionFailureUnexpectedValuePresent Text ValueId
  | RecognitionFailureGateMismatch Text BlockId SystemsTerminator
  | RecognitionFailureLegacyBlockMismatch Text BlockId [SystemsOp] SystemsTerminator
  | RecognitionFailureFlowMismatch Text BlockId [SystemsOp] SystemsTerminator
  | RecognitionFailureReasonUseMismatch ValueId [(BlockId, Text)]
  | RecognitionFailureReasonIdentityCollision ValueId
  | RecognitionFailureDecisionAlreadyPresent DecisionId
  | RecognitionFailureDecisionMissing DecisionId
  | RecognitionFailureDecisionMismatch DecisionId
  deriving (Eq, Show)

recognitionFailureDecisionId :: DecisionId
recognitionFailureDecisionId = DecisionId "lower.recognition.failure_detail"

phase0RecognitionFailureWitnesses :: [RecognitionFailureWitness]
phase0RecognitionFailureWitnesses =
  [ RecognitionFailureWitness
      { recognitionFailureFunction = "UploadServer"
      , recognitionFailureRecognitionBlock = BlockId "server.entry"
      , recognitionFailureFailureBlock = BlockId "server.hello.recognition_failure"
      , recognitionFailurePending = ValueId "server.pending.hello"
      , recognitionFailureFrameOwner = ValueId "server.frame.hello"
      , recognitionFailureGrammar = "Hello"
      , recognitionFailureReason = ValueId "server.hello_recognition_reason"
      , recognitionFailureMaterializeCall = "materialize recognition failure reason Hello"
      , recognitionFailureEffectCall = "fail recognition Hello"
      , recognitionFailureFatalClass = "RecognitionFailure[Hello]"
      }
  , RecognitionFailureWitness
      { recognitionFailureFunction = "UploadServer"
      , recognitionFailureRecognitionBlock = BlockId "server.version"
      , recognitionFailureFailureBlock = BlockId "server.begin.recognition_failure"
      , recognitionFailurePending = ValueId "server.pending.begin"
      , recognitionFailureFrameOwner = ValueId "server.frame.begin"
      , recognitionFailureGrammar = "Begin"
      , recognitionFailureReason = ValueId "server.begin_recognition_reason"
      , recognitionFailureMaterializeCall = "materialize recognition failure reason Begin"
      , recognitionFailureEffectCall = "fail recognition Begin"
      , recognitionFailureFatalClass = "RecognitionFailure[Begin]"
      }
  ]

phase0RecognitionFailureBundle
  :: Either RecognitionFailureError RecognitionFailureBundle
phase0RecognitionFailureBundle = do
  predecessor <- mapLeft RecognitionFailurePredecessorError phase0ClientOutboundBundle
  let baseArtifact = clientOutboundArtifact predecessor
      baseContext = clientOutboundContext predecessor
      witnesses = phase0RecognitionFailureWitnesses
      predecessorDecisions = loweringLedgerDecisions (systemsArtifactLoweringLedger baseArtifact)
  when (Map.member recognitionFailureDecisionId predecessorDecisions) $
    Left (RecognitionFailureDecisionAlreadyPresent recognitionFailureDecisionId)
  verifyDistinctReasons witnesses
  program <- foldM
    (flip (materializeRecognitionFailure recognitionFailureDecisionId))
    (systemsArtifactProgram baseArtifact)
    witnesses
  let baseContract = systemsArtifactStageContract baseArtifact
      targetDigest = systemsProgramDigest program
      contract = baseContract
        { stageTargetArtifactDigest = targetDigest
        , stageTraceRelation = stageTraceRelation baseContract <>
            [ "Hello recognition rejected(reason) -> explicit failure-only server.hello_recognition_reason -> exact fail recognition Hello effect"
            , "Begin recognition rejected(reason) -> explicit failure-only server.begin_recognition_reason -> exact fail recognition Begin effect"
            , "recognition failure detail remains grammar-specific and pending-owner-specific; existing pending/frame cleanup remains mandatory"
            ]
        , stageResourceFailureRelation = stageResourceFailureRelation baseContract <>
            [ "Hello recognition failure preserves its exact reason through the fatal effect before terminal cleanup completion"
            , "Begin recognition failure preserves its exact reason through the fatal effect before terminal cleanup completion"
            ]
        }
      sourceDigest = stageSourceArtifactDigest contract
      rebound = Map.map (rebindDecisionTarget targetDigest) predecessorDecisions
      decision = deriveRecognitionFailureDecision sourceDigest targetDigest witnesses
      decisions = Map.insert recognitionFailureDecisionId decision rebound
      loweringRoot = deriveLoweringLedgerRoot decisions
      artifact = SystemsArtifact program contract (LoweringLedger decisions loweringRoot)
      assuranceLedger = systemsAssuranceLedger baseContext
      baseManifest = systemsAssuranceManifest baseContext
      provisionalManifest = baseManifest
        { manifestImplementationDigest = systemsArtifactDigest artifact
        , manifestLoweringLedgerRoot = loweringRoot
        }
      manifest = provisionalManifest
        { manifestId = deriveManifestId assuranceLedger provisionalManifest }
      baseVerification = systemsAssuranceVerificationContext baseContext
      verification = baseVerification
        { verificationImplementationDigest = systemsArtifactDigest artifact
        , verificationLoweringLedgerRoot = loweringRoot
        }
      context = baseContext
        { systemsAssuranceManifest = manifest
        , systemsAssuranceVerificationContext = verification
        }
      bundle = RecognitionFailureBundle artifact context predecessor witnesses
  verifyRecognitionFailureBundle bundle
  pure bundle

verifyRecognitionFailureBundle
  :: RecognitionFailureBundle
  -> Either RecognitionFailureError ()
verifyRecognitionFailureBundle bundle = do
  mapLeft RecognitionFailurePredecessorError $
    verifyClientOutboundBundle (recognitionFailurePredecessor bundle)
  mapLeft RecognitionFailureSystemsError $
    verifySystemsArtifact
      (recognitionFailureContext bundle)
      (recognitionFailureArtifact bundle)
  mapLeft RecognitionFailureDataflowError $
    verifyScalarDataflow (recognitionFailureArtifact bundle)
  mapLeft RecognitionFailureClientOutboundRegression $
    verifyClientOutboundWitness
      (recognitionFailureArtifact bundle)
      phase0ClientOutboundWitness
  verifyDistinctReasons (recognitionFailureWitnesses bundle)
  verifyRecognitionFailureWitnesses
    (recognitionFailureArtifact bundle)
    (recognitionFailureWitnesses bundle)
  let artifact = recognitionFailureArtifact bundle
      program = systemsArtifactProgram artifact
      sourceDigest = stageSourceArtifactDigest (systemsArtifactStageContract artifact)
      targetDigest = systemsProgramDigest program
      decisions = loweringLedgerDecisions (systemsArtifactLoweringLedger artifact)
      expected = deriveRecognitionFailureDecision
        sourceDigest targetDigest (recognitionFailureWitnesses bundle)
  case Map.lookup recognitionFailureDecisionId decisions of
    Nothing -> Left (RecognitionFailureDecisionMissing recognitionFailureDecisionId)
    Just actual -> unless (actual == expected) $
      Left (RecognitionFailureDecisionMismatch recognitionFailureDecisionId)

verifyRecognitionFailureWitnesses
  :: SystemsArtifact
  -> [RecognitionFailureWitness]
  -> Either RecognitionFailureError ()
verifyRecognitionFailureWitnesses artifact witnesses = do
  verifyDistinctReasons witnesses
  forM_ witnesses (verifyRecognitionFailureWitness artifact)

verifyRecognitionFailureWitness
  :: SystemsArtifact
  -> RecognitionFailureWitness
  -> Either RecognitionFailureError ()
verifyRecognitionFailureWitness artifact witness = do
  let program = systemsArtifactProgram artifact
      functionName = recognitionFailureFunction witness
  function <- lookupFunction functionName program
  verifyRole functionName function
    (recognitionFailurePending witness)
    (PendingIngress (recognitionFailureGrammar witness))
  verifyRole functionName function
    (recognitionFailureFrameOwner witness)
    (FrameOwner (recognitionFailureGrammar witness))
  verifyRole functionName function
    (recognitionFailureReason witness)
    (RuntimeOpaque (reasonRole witness))

  recognitionBlock <- lookupBlock functionName function
    (recognitionFailureRecognitionBlock witness)
  case systemsBlockTerminator recognitionBlock of
    TermRecognize pending _raw site _success failure
      | pending == recognitionFailurePending witness
          && runtimeSiteKind site == RecognitionBoundary (recognitionFailureGrammar witness)
          && failure == recognitionFailureFailureBlock witness -> pure ()
    other -> Left (RecognitionFailureGateMismatch
      functionName
      (recognitionFailureRecognitionBlock witness)
      other)

  failureBlock <- lookupBlock functionName function
    (recognitionFailureFailureBlock witness)
  case systemsBlockOps failureBlock of
    [ OpRuntimeCall materializeName [materializePending] [reason] Nothing materializeDecision
      , OpRuntimeCall effectName [effectPending, effectReason] [] Nothing effectDecision
      , OpDestroyPending destroyPending destroyFrame _cleanupDecision
      ]
      | materializeName == recognitionFailureMaterializeCall witness
          && materializePending == recognitionFailurePending witness
          && reason == recognitionFailureReason witness
          && materializeDecision == recognitionFailureDecisionId
          && effectName == recognitionFailureEffectCall witness
          && effectPending == recognitionFailurePending witness
          && effectReason == recognitionFailureReason witness
          && effectDecision == recognitionFailureDecisionId
          && destroyPending == recognitionFailurePending witness
          && destroyFrame == recognitionFailureFrameOwner witness
          && systemsBlockTerminator failureBlock == TermFatal (recognitionFailureFatalClass witness)
          -> pure ()
    operations -> Left (RecognitionFailureFlowMismatch
      functionName
      (recognitionFailureFailureBlock witness)
      operations
      (systemsBlockTerminator failureBlock))

  let uses = reasonUses (recognitionFailureReason witness) function
      expectedUses =
        [ (recognitionFailureFailureBlock witness,
            "runtime-call:" <> recognitionFailureEffectCall witness)
        ]
  unless (uses == expectedUses) $
    Left (RecognitionFailureReasonUseMismatch
      (recognitionFailureReason witness)
      uses)

materializeRecognitionFailure
  :: DecisionId
  -> RecognitionFailureWitness
  -> SystemsProgram
  -> Either RecognitionFailureError SystemsProgram
materializeRecognitionFailure decisionId witness program = do
  let functionName = recognitionFailureFunction witness
  function <- lookupFunction functionName program
  verifyRole functionName function
    (recognitionFailurePending witness)
    (PendingIngress (recognitionFailureGrammar witness))
  verifyRole functionName function
    (recognitionFailureFrameOwner witness)
    (FrameOwner (recognitionFailureGrammar witness))
  requireAbsent functionName function (recognitionFailureReason witness)

  recognitionBlock <- lookupBlock functionName function
    (recognitionFailureRecognitionBlock witness)
  case systemsBlockTerminator recognitionBlock of
    TermRecognize pending _raw site _success failure
      | pending == recognitionFailurePending witness
          && runtimeSiteKind site == RecognitionBoundary (recognitionFailureGrammar witness)
          && failure == recognitionFailureFailureBlock witness -> pure ()
    other -> Left (RecognitionFailureGateMismatch
      functionName
      (recognitionFailureRecognitionBlock witness)
      other)

  failureBlock <- lookupBlock functionName function
    (recognitionFailureFailureBlock witness)
  destroyOperation <- case systemsBlockOps failureBlock of
    [ operation@OpDestroyPending
        { destroyPending = pending
        , destroyFrameOwner = frame
        }
      ]
      | pending == recognitionFailurePending witness
          && frame == recognitionFailureFrameOwner witness
          && systemsBlockTerminator failureBlock == TermFatal (recognitionFailureFatalClass witness)
          -> Right operation
    operations -> Left (RecognitionFailureLegacyBlockMismatch
      functionName
      (recognitionFailureFailureBlock witness)
      operations
      (systemsBlockTerminator failureBlock))

  let reason = SystemsValue
        (recognitionFailureReason witness)
        (RuntimeOpaque (reasonRole witness))
        Nothing
      failureBlock' = failureBlock
        { systemsBlockOps =
            [ OpRuntimeCall
                (recognitionFailureMaterializeCall witness)
                [recognitionFailurePending witness]
                [recognitionFailureReason witness]
                Nothing
                decisionId
            , OpRuntimeCall
                (recognitionFailureEffectCall witness)
                [ recognitionFailurePending witness
                , recognitionFailureReason witness
                ]
                []
                Nothing
                decisionId
            , destroyOperation
            ]
        }
      function' = function
        { systemsFunctionValues = Map.insert
            (recognitionFailureReason witness)
            reason
            (systemsFunctionValues function)
        , systemsFunctionBlocks = Map.insert
            (recognitionFailureFailureBlock witness)
            failureBlock'
            (systemsFunctionBlocks function)
        }
  pure program
    { systemsProgramFunctions = Map.insert
        functionName function' (systemsProgramFunctions program)
    }

verifyDistinctReasons
  :: [RecognitionFailureWitness]
  -> Either RecognitionFailureError ()
verifyDistinctReasons witnesses = go Map.empty witnesses
  where
    go _ [] = pure ()
    go seen (witness : rest) =
      let reason = recognitionFailureReason witness
      in case Map.lookup reason seen of
          Nothing -> go (Map.insert reason () seen) rest
          Just () -> Left (RecognitionFailureReasonIdentityCollision reason)

reasonRole :: RecognitionFailureWitness -> Text
reasonRole witness =
  "RecognitionReason[" <> recognitionFailureGrammar witness <> "]"

reasonUses :: ValueId -> SystemsFunction -> [(BlockId, Text)]
reasonUses valueId function =
  [ (systemsBlockId blockValue, "runtime-call:" <> name)
  | blockValue <- Map.elems (systemsFunctionBlocks function)
  , OpRuntimeCall name inputs _outputs _site _decision <- systemsBlockOps blockValue
  , valueId `elem` inputs
  ]

lookupFunction
  :: Text
  -> SystemsProgram
  -> Either RecognitionFailureError SystemsFunction
lookupFunction functionName program =
  case Map.lookup functionName (systemsProgramFunctions program) of
    Nothing -> Left (RecognitionFailureFunctionMissing functionName)
    Just value -> Right value

lookupBlock
  :: Text
  -> SystemsFunction
  -> BlockId
  -> Either RecognitionFailureError SystemsBlock
lookupBlock functionName function blockId =
  case Map.lookup blockId (systemsFunctionBlocks function) of
    Nothing -> Left (RecognitionFailureBlockMissing functionName blockId)
    Just value -> Right value

verifyRole
  :: Text
  -> SystemsFunction
  -> ValueId
  -> SystemsValueRole
  -> Either RecognitionFailureError ()
verifyRole functionName function valueId expected =
  case Map.lookup valueId (systemsFunctionValues function) of
    Nothing -> Left (RecognitionFailureValueMissing functionName valueId)
    Just value -> unless (systemsValueRole value == expected) $
      Left (RecognitionFailureValueRoleMismatch
        functionName valueId (systemsValueRole value))

requireAbsent
  :: Text
  -> SystemsFunction
  -> ValueId
  -> Either RecognitionFailureError ()
requireAbsent functionName function valueId =
  when (Map.member valueId (systemsFunctionValues function)) $
    Left (RecognitionFailureUnexpectedValuePresent functionName valueId)

rebindDecisionTarget :: Digest -> LoweringDecision -> LoweringDecision
rebindDecisionTarget targetDigest lowering = provisional
  { loweringDecisionDigest = deriveLoweringDecisionDigest provisional }
  where
    provisional = lowering { loweringTargetArtifactDigest = targetDigest }

deriveRecognitionFailureDecision
  :: Digest
  -> Digest
  -> [RecognitionFailureWitness]
  -> LoweringDecision
deriveRecognitionFailureDecision sourceDigest targetDigest witnesses = provisional
  { loweringDecisionDigest = deriveLoweringDecisionDigest provisional }
  where
    provisional = LoweringDecision
      { loweringDecisionId = recognitionFailureDecisionId
      , loweringDecisionDigest = Digest ""
      , loweringSourceArtifactDigest = sourceDigest
      , loweringTargetArtifactDigest = targetDigest
      , loweringSourceRepresentation =
          "recognition rejected(reason) source branches with grammar-specific failure details"
      , loweringTargetRepresentation =
          "failure-only opaque recognition-reason identities forwarded into exact fatal recognition effects"
      , loweringSemanticEntities = concatMap witnessEntities witnesses
      , loweringObligationRevisions = []
      , loweringAssuranceEntries = []
      , loweringAssuranceUses = []
      , loweringAction = Materialize
      , loweringRepresentationBefore =
          "recognition failure represented only by a dedicated CFG edge and fatal class"
      , loweringRepresentationAfter =
          "dedicated failure edge plus opaque reason identity, exact pending provenance, fatal forwarding effect, and existing cleanup"
      , loweringInvariantsPreserved =
          [ "recognition success/failure control split"
          , "pending ingress identity and grammar provenance"
          , "recognition failure remains terminal"
          , "pending/frame cleanup remains mandatory on failure"
          , "Hello and Begin failure reasons remain distinct identities"
          ]
      , loweringInvariantsTransferred = []
      , loweringRuntimeResidue =
          [ "recognizer supplies a grammar-specific failure detail on the failure edge"
          , "physical reason representation is not selected in Systems"
          , "physical fatal-diagnostic effect ABI is not selected in Systems"
          ]
      , loweringCostClass = Just SemanticRequired
      , loweringCostShape = emptyCostShape
          { costCodeSize = Just "two failure-only reason identities and forwarding effects"
          , costFrequency = Just "only on Hello or Begin recognition failure"
          }
      , loweringTargetPreconditions =
          [ "the failure edge is reachable only from the matching recognition boundary"
          , "the reason identity is produced only on that dedicated failure path"
          , "cleanup still destroys the exact pending/frame owners"
          ]
      , loweringAssumptions = []
      , loweringDerivedObligations = []
      , loweringInspectionPlan =
          [ "verify each reason is grammar-specific and pending-specific"
          , "verify each reason has exactly one semantic forwarding use"
          , "verify the exact pending owner is carried into materialization and fatal effect"
          , "verify existing pending/frame cleanup and fatal class remain unchanged"
          ]
      }

witnessEntities :: RecognitionFailureWitness -> [Text]
witnessEntities witness =
  [ "grammar:" <> recognitionFailureGrammar witness
  , "pending:" <> unValueId (recognitionFailurePending witness)
  , "reason:" <> unValueId (recognitionFailureReason witness)
  , "failure-block:" <> unBlockId (recognitionFailureFailureBlock witness)
  ]

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
