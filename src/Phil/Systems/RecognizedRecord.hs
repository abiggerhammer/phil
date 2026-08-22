{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.RecognizedRecord
  ( RecognizedRecordWitness (..)
  , RecognizedRecordBundle (..)
  , RecognizedRecordError (..)
  , phase0BeginRecordWitness
  , phase0RecognizedRecordBundle
  , verifyRecognizedRecordBundle
  , verifyRecognizedRecordWitnesses
  ) where

import Control.Monad (forM_, unless)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Assurance.Types
import Phil.Systems.Dataflow
import Phil.Systems.FieldProjection
import Phil.Systems.IR
import Phil.Systems.Verify

data RecognizedRecordWitness = RecognizedRecordWitness
  { recognizedRecordFunction :: Text
  , recognizedRecordRecognitionBlock :: BlockId
  , recognizedRecordSuccessBlock :: BlockId
  , recognizedRecordPending :: ValueId
  , recognizedRecordGrammar :: Text
  , recognizedRecordValue :: ValueId
  , recognizedRecordField :: Text
  , recognizedRecordProjectionOutput :: ValueId
  , recognizedRecordProjectionType :: ScalarType
  , recognizedRecordMaterializationDecision :: DecisionId
  , recognizedRecordProjectionDecision :: DecisionId
  }
  deriving (Eq, Show)

data RecognizedRecordBundle = RecognizedRecordBundle
  { recognizedRecordArtifact :: SystemsArtifact
  , recognizedRecordContext :: SystemsVerificationContext
  , recognizedRecordWitnesses :: [RecognizedRecordWitness]
  }
  deriving (Eq, Show)

data RecognizedRecordError
  = RecognizedRecordFieldProjectionError FieldProjectionError
  | RecognizedRecordSystemsError SystemsVerificationError
  | RecognizedRecordScalarDataflowError ScalarDataflowError
  | RecognizedRecordFunctionMissing Text
  | RecognizedRecordRecognitionBlockMissing Text BlockId
  | RecognizedRecordSuccessBlockMissing Text BlockId
  | RecognizedRecordPendingMissing Text ValueId
  | RecognizedRecordPendingGrammarMismatch Text ValueId Text
  | RecognizedRecordRecognitionMismatch Text BlockId ValueId BlockId
  | RecognizedRecordValueMissing Text ValueId
  | RecognizedRecordValueRoleMismatch Text ValueId Text SystemsValueRole
  | RecognizedRecordProjectionOutputMissing Text ValueId
  | RecognizedRecordProjectionOutputTypeMismatch Text ValueId ScalarType SystemsValueRole
  | RecognizedRecordSchemaMismatch Text Text ScalarType
  | RecognizedRecordCommitMissing Text BlockId ValueId
  | RecognizedRecordMaterializationMissing Text BlockId ValueId
  | RecognizedRecordMaterializationMultiple Text BlockId ValueId Int
  | RecognizedRecordProjectionMissing Text BlockId ValueId
  | RecognizedRecordProjectionMultiple Text BlockId ValueId Int
  | RecognizedRecordOrderingMismatch Text BlockId
  | RecognizedRecordDecisionMissing DecisionId
  | RecognizedRecordDecisionMismatch DecisionId
  | RecognizedRecordExactReceiveUseMissing Text ValueId
  deriving (Eq, Show)

phase0BeginRecordWitness :: RecognizedRecordWitness
phase0BeginRecordWitness = RecognizedRecordWitness
  { recognizedRecordFunction = "UploadServer"
  , recognizedRecordRecognitionBlock = BlockId "server.version"
  , recognizedRecordSuccessBlock = BlockId "server.begin.commit"
  , recognizedRecordPending = ValueId "server.pending.begin"
  , recognizedRecordGrammar = "Begin"
  , recognizedRecordValue = ValueId "server.begin"
  , recognizedRecordField = "length"
  , recognizedRecordProjectionOutput = ValueId "server.begin_length"
  , recognizedRecordProjectionType = ScalarUInt 64
  , recognizedRecordMaterializationDecision = DecisionId "phase0.begin.record.materialization"
  , recognizedRecordProjectionDecision = DecisionId "phase0.begin.length.projection"
  }

-- | Candidate Systems artifact for the recognized-record ABI. It is derived from
-- the already-verified field-projection candidate rather than mutating that
-- historical artifact in place.
phase0RecognizedRecordBundle :: Either RecognizedRecordError RecognizedRecordBundle
phase0RecognizedRecordBundle = do
  fieldBundle <- mapLeft RecognizedRecordFieldProjectionError phase0FieldProjectionBundle
  let baseArtifact = fieldProjectionArtifact fieldBundle
      baseContext = fieldProjectionContext fieldBundle
  program <- materializeRecognizedRecordProgram
    phase0BeginRecordWitness
    (systemsArtifactProgram baseArtifact)
  let baseContract = systemsArtifactStageContract baseArtifact
      targetDigest = systemsProgramDigest program
      contract = baseContract
        { stageTargetArtifactDigest = targetDigest
        , stageTraceRelation = stageTraceRelation baseContract <>
            ["recognized Begin semantic value -> explicit server.begin runtime record"]
        }
      sourceDigest = stageSourceArtifactDigest contract
      baseDecisions = loweringLedgerDecisions (systemsArtifactLoweringLedger baseArtifact)
      reboundDecisions = Map.map (rebindDecisionTarget targetDigest) baseDecisions
      materializationDecision = deriveRecordMaterializationDecision
        sourceDigest targetDigest phase0BeginRecordWitness
      projectionDecision = deriveRecordProjectionDecision
        sourceDigest targetDigest phase0BeginRecordWitness
      decisions = Map.insert
        (recognizedRecordMaterializationDecision phase0BeginRecordWitness)
        materializationDecision $
        Map.insert
          (recognizedRecordProjectionDecision phase0BeginRecordWitness)
          projectionDecision
          reboundDecisions
      loweringRoot = deriveLoweringLedgerRoot decisions
      loweringLedger = LoweringLedger
        { loweringLedgerDecisions = decisions
        , loweringLedgerRoot = loweringRoot
        }
      artifact = SystemsArtifact
        { systemsArtifactProgram = program
        , systemsArtifactStageContract = contract
        , systemsArtifactLoweringLedger = loweringLedger
        }
      assuranceLedger = systemsAssuranceLedger baseContext
      baseManifest = systemsAssuranceManifest baseContext
      provisionalManifest = baseManifest
        { manifestImplementationDigest = systemsArtifactDigest artifact
        , manifestLoweringLedgerRoot = loweringRoot
        }
      manifest = provisionalManifest
        { manifestId = deriveManifestId assuranceLedger provisionalManifest }
      baseAssuranceContext = systemsAssuranceVerificationContext baseContext
      assuranceContext = baseAssuranceContext
        { verificationImplementationDigest = systemsArtifactDigest artifact
        , verificationLoweringLedgerRoot = loweringRoot
        }
      systemsContext = baseContext
        { systemsAssuranceManifest = manifest
        , systemsAssuranceVerificationContext = assuranceContext
        }
      bundle = RecognizedRecordBundle
        { recognizedRecordArtifact = artifact
        , recognizedRecordContext = systemsContext
        , recognizedRecordWitnesses = [phase0BeginRecordWitness]
        }
  verifyRecognizedRecordBundle bundle
  Right bundle

verifyRecognizedRecordBundle
  :: RecognizedRecordBundle
  -> Either RecognizedRecordError ()
verifyRecognizedRecordBundle bundle = do
  mapLeft RecognizedRecordSystemsError $
    verifySystemsArtifact
      (recognizedRecordContext bundle)
      (recognizedRecordArtifact bundle)
  mapLeft RecognizedRecordScalarDataflowError $
    verifyScalarDataflow (recognizedRecordArtifact bundle)
  verifyRecognizedRecordWitnesses
    (recognizedRecordArtifact bundle)
    (recognizedRecordWitnesses bundle)

verifyRecognizedRecordWitnesses
  :: SystemsArtifact
  -> [RecognizedRecordWitness]
  -> Either RecognizedRecordError ()
verifyRecognizedRecordWitnesses artifact witnesses =
  forM_ witnesses (verifyRecognizedRecordWitness artifact)

verifyRecognizedRecordWitness
  :: SystemsArtifact
  -> RecognizedRecordWitness
  -> Either RecognizedRecordError ()
verifyRecognizedRecordWitness artifact witness = do
  let program = systemsArtifactProgram artifact
      functionName = recognizedRecordFunction witness
  function <- case Map.lookup functionName (systemsProgramFunctions program) of
    Nothing -> Left (RecognizedRecordFunctionMissing functionName)
    Just value -> Right value
  pendingValue <- case Map.lookup
      (recognizedRecordPending witness)
      (systemsFunctionValues function) of
    Nothing -> Left (RecognizedRecordPendingMissing functionName (recognizedRecordPending witness))
    Just value -> Right value
  case systemsValueRole pendingValue of
    PendingIngress grammar
      | grammar == recognizedRecordGrammar witness -> pure ()
      | otherwise -> Left (RecognizedRecordPendingGrammarMismatch
          functionName
          (recognizedRecordPending witness)
          grammar)
    _ -> Left (RecognizedRecordPendingGrammarMismatch
      functionName
      (recognizedRecordPending witness)
      "not-pending-ingress")
  recognitionBlock <- case Map.lookup
      (recognizedRecordRecognitionBlock witness)
      (systemsFunctionBlocks function) of
    Nothing -> Left (RecognizedRecordRecognitionBlockMissing
      functionName
      (recognizedRecordRecognitionBlock witness))
    Just value -> Right value
  case systemsBlockTerminator recognitionBlock of
    TermRecognize
      { recognizePending = pending
      , recognizeSuccess = success
      }
      | pending == recognizedRecordPending witness
          && success == recognizedRecordSuccessBlock witness -> pure ()
    _ -> Left (RecognizedRecordRecognitionMismatch
      functionName
      (recognizedRecordRecognitionBlock witness)
      (recognizedRecordPending witness)
      (recognizedRecordSuccessBlock witness))
  recordValue <- case Map.lookup
      (recognizedRecordValue witness)
      (systemsFunctionValues function) of
    Nothing -> Left (RecognizedRecordValueMissing functionName (recognizedRecordValue witness))
    Just value -> Right value
  case systemsValueRole recordValue of
    RuntimeRecord grammar
      | grammar == recognizedRecordGrammar witness -> pure ()
      | otherwise -> Left (RecognizedRecordValueRoleMismatch
          functionName
          (recognizedRecordValue witness)
          (recognizedRecordGrammar witness)
          (systemsValueRole recordValue))
    other -> Left (RecognizedRecordValueRoleMismatch
      functionName
      (recognizedRecordValue witness)
      (recognizedRecordGrammar witness)
      other)
  outputValue <- case Map.lookup
      (recognizedRecordProjectionOutput witness)
      (systemsFunctionValues function) of
    Nothing -> Left (RecognizedRecordProjectionOutputMissing
      functionName
      (recognizedRecordProjectionOutput witness))
    Just value -> Right value
  case systemsValueRole outputValue of
    TypedScalar actualType
      | actualType == recognizedRecordProjectionType witness -> pure ()
      | otherwise -> Left (RecognizedRecordProjectionOutputTypeMismatch
          functionName
          (recognizedRecordProjectionOutput witness)
          (recognizedRecordProjectionType witness)
          (systemsValueRole outputValue))
    other -> Left (RecognizedRecordProjectionOutputTypeMismatch
      functionName
      (recognizedRecordProjectionOutput witness)
      (recognizedRecordProjectionType witness)
      other)
  unless
    (recordSchemaType
      (recognizedRecordGrammar witness)
      (recognizedRecordField witness)
      == Just (recognizedRecordProjectionType witness)) $
    Left (RecognizedRecordSchemaMismatch
      (recognizedRecordGrammar witness)
      (recognizedRecordField witness)
      (recognizedRecordProjectionType witness))
  successBlock <- case Map.lookup
      (recognizedRecordSuccessBlock witness)
      (systemsFunctionBlocks function) of
    Nothing -> Left (RecognizedRecordSuccessBlockMissing
      functionName
      (recognizedRecordSuccessBlock witness))
    Just value -> Right value
  let operations = systemsBlockOps successBlock
      commitIndices =
        [ index
        | (index, OpCommitIngress { commitPending = pending }) <- zip [0 :: Int ..] operations
        , pending == recognizedRecordPending witness
        ]
      materializationIndices =
        [ index
        | (index, OpRuntimeCall
            { runtimeCallName = name
            , runtimeCallInputs = inputs
            , runtimeCallOutputs = outputs
            , runtimeCallSite = Nothing
            , runtimeCallDecision = decisionId
            }) <- zip [0 :: Int ..] operations
        , name == recordMaterializationCallName witness
        , null inputs
        , outputs == [recognizedRecordValue witness]
        , decisionId == recognizedRecordMaterializationDecision witness
        ]
      projectionIndices =
        [ index
        | (index, OpRuntimeCall
            { runtimeCallName = name
            , runtimeCallInputs = inputs
            , runtimeCallOutputs = outputs
            , runtimeCallSite = Nothing
            , runtimeCallDecision = decisionId
            }) <- zip [0 :: Int ..] operations
        , name == recordProjectionCallName witness
        , inputs == [recognizedRecordValue witness]
        , outputs == [recognizedRecordProjectionOutput witness]
        , decisionId == recognizedRecordProjectionDecision witness
        ]
  commitIndex <- case commitIndices of
    [] -> Left (RecognizedRecordCommitMissing
      functionName
      (recognizedRecordSuccessBlock witness)
      (recognizedRecordPending witness))
    firstIndex : _ -> Right firstIndex
  materializationIndex <- case materializationIndices of
    [] -> Left (RecognizedRecordMaterializationMissing
      functionName
      (recognizedRecordSuccessBlock witness)
      (recognizedRecordValue witness))
    [index] -> Right index
    many -> Left (RecognizedRecordMaterializationMultiple
      functionName
      (recognizedRecordSuccessBlock witness)
      (recognizedRecordValue witness)
      (length many))
  projectionIndex <- case projectionIndices of
    [] -> Left (RecognizedRecordProjectionMissing
      functionName
      (recognizedRecordSuccessBlock witness)
      (recognizedRecordProjectionOutput witness))
    [index] -> Right index
    many -> Left (RecognizedRecordProjectionMultiple
      functionName
      (recognizedRecordSuccessBlock witness)
      (recognizedRecordProjectionOutput witness)
      (length many))
  unless (commitIndex < materializationIndex && materializationIndex < projectionIndex) $
    Left (RecognizedRecordOrderingMismatch
      functionName
      (recognizedRecordSuccessBlock witness))
  let decisions = loweringLedgerDecisions (systemsArtifactLoweringLedger artifact)
      sourceDigest = stageSourceArtifactDigest (systemsArtifactStageContract artifact)
      targetDigest = systemsProgramDigest program
      expectedMaterializationDecision = deriveRecordMaterializationDecision
        sourceDigest targetDigest witness
      expectedProjectionDecision = deriveRecordProjectionDecision
        sourceDigest targetDigest witness
  verifyDecision decisions
    (recognizedRecordMaterializationDecision witness)
    expectedMaterializationDecision
  verifyDecision decisions
    (recognizedRecordProjectionDecision witness)
    expectedProjectionDecision
  unless (any (usesExactLength (recognizedRecordProjectionOutput witness))
      (Map.elems (systemsFunctionBlocks function))) $
    Left (RecognizedRecordExactReceiveUseMissing
      functionName
      (recognizedRecordProjectionOutput witness))

verifyDecision
  :: Map.Map DecisionId LoweringDecision
  -> DecisionId
  -> LoweringDecision
  -> Either RecognizedRecordError ()
verifyDecision decisions decisionId expected =
  case Map.lookup decisionId decisions of
    Nothing -> Left (RecognizedRecordDecisionMissing decisionId)
    Just actual ->
      unless (actual == expected) $
        Left (RecognizedRecordDecisionMismatch decisionId)

materializeRecognizedRecordProgram
  :: RecognizedRecordWitness
  -> SystemsProgram
  -> Either RecognizedRecordError SystemsProgram
materializeRecognizedRecordProgram witness program = do
  let functionName = recognizedRecordFunction witness
  function <- case Map.lookup functionName (systemsProgramFunctions program) of
    Nothing -> Left (RecognizedRecordFunctionMissing functionName)
    Just value -> Right value
  successBlock <- case Map.lookup
      (recognizedRecordSuccessBlock witness)
      (systemsFunctionBlocks function) of
    Nothing -> Left (RecognizedRecordSuccessBlockMissing
      functionName
      (recognizedRecordSuccessBlock witness))
    Just value -> Right value
  let recordValue = SystemsValue
        { systemsValueId = recognizedRecordValue witness
        , systemsValueRole = RuntimeRecord (recognizedRecordGrammar witness)
        , systemsStorageIdentity = Nothing
        }
      materializationOperation = OpRuntimeCall
        { runtimeCallName = recordMaterializationCallName witness
        , runtimeCallInputs = []
        , runtimeCallOutputs = [recognizedRecordValue witness]
        , runtimeCallSite = Nothing
        , runtimeCallDecision = recognizedRecordMaterializationDecision witness
        }
      rewriteProjection operation = case operation of
        OpRuntimeCall
          { runtimeCallName = name
          , runtimeCallOutputs = outputs
          , runtimeCallSite = Nothing
          , runtimeCallDecision = decisionId
          }
          | name == recordProjectionCallName witness
              && outputs == [recognizedRecordProjectionOutput witness]
              && decisionId == recognizedRecordProjectionDecision witness ->
              operation { runtimeCallInputs = [recognizedRecordValue witness] }
        _ -> operation
      operationsWithRecord = insertAfterCommit
        (recognizedRecordPending witness)
        materializationOperation
        (systemsBlockOps successBlock)
      successBlock' = successBlock
        { systemsBlockOps = map rewriteProjection operationsWithRecord }
      function' = function
        { systemsFunctionValues = Map.insert
            (recognizedRecordValue witness)
            recordValue
            (systemsFunctionValues function)
        , systemsFunctionBlocks = Map.insert
            (recognizedRecordSuccessBlock witness)
            successBlock'
            (systemsFunctionBlocks function)
        }
  Right program
    { systemsProgramFunctions = Map.insert
        functionName
        function'
        (systemsProgramFunctions program)
    }

insertAfterCommit :: ValueId -> SystemsOp -> [SystemsOp] -> [SystemsOp]
insertAfterCommit pending operation operations =
  case break isCommit operations of
    (_, []) -> operations
    (before, commitOperation : after) ->
      before <> [commitOperation, operation] <> after
  where
    isCommit candidate = case candidate of
      OpCommitIngress { commitPending = candidatePending } -> candidatePending == pending
      _ -> False

recordMaterializationCallName :: RecognizedRecordWitness -> Text
recordMaterializationCallName witness =
  "materialize recognized " <> recognizedRecordGrammar witness

recordProjectionCallName :: RecognizedRecordWitness -> Text
recordProjectionCallName witness =
  "project recognized "
    <> recognizedRecordGrammar witness
    <> "."
    <> recognizedRecordField witness

recordSchemaType :: Text -> Text -> Maybe ScalarType
recordSchemaType grammar fieldName = case (grammar, fieldName) of
  ("Begin", "length") -> Just (ScalarUInt 64)
  _ -> Nothing

usesExactLength :: ValueId -> SystemsBlock -> Bool
usesExactLength valueId blockValue = case systemsBlockTerminator blockValue of
  TermReceiveExact { exactLength = candidate } -> candidate == valueId
  _ -> False

rebindDecisionTarget :: Digest -> LoweringDecision -> LoweringDecision
rebindDecisionTarget targetDigest lowering = provisional
  { loweringDecisionDigest = deriveLoweringDecisionDigest provisional }
  where
    provisional = lowering { loweringTargetArtifactDigest = targetDigest }

deriveRecordMaterializationDecision
  :: Digest
  -> Digest
  -> RecognizedRecordWitness
  -> LoweringDecision
deriveRecordMaterializationDecision sourceDigest targetDigest witness = provisional
  { loweringDecisionDigest = deriveLoweringDecisionDigest provisional }
  where
    provisional = LoweringDecision
      { loweringDecisionId = recognizedRecordMaterializationDecision witness
      , loweringDecisionDigest = Digest ""
      , loweringSourceArtifactDigest = sourceDigest
      , loweringTargetArtifactDigest = targetDigest
      , loweringSourceRepresentation =
          "recognized " <> recognizedRecordGrammar witness <> " semantic value"
      , loweringTargetRepresentation =
          "runtime record " <> unValueId (recognizedRecordValue witness)
      , loweringSemanticEntities =
          [ "record:" <> recognizedRecordGrammar witness
          , "value:" <> unValueId (recognizedRecordValue witness)
          ]
      , loweringObligationRevisions = []
      , loweringAssuranceEntries = []
      , loweringAssuranceUses = []
      , loweringAction = Materialize
      , loweringRepresentationBefore =
          "successful recognition event for " <> recognizedRecordGrammar witness
      , loweringRepresentationAfter =
          "explicit runtime semantic record value"
      , loweringInvariantsPreserved =
          [ "recognition provenance"
          , "record grammar identity"
          , "success-path dominance"
          ]
      , loweringInvariantsTransferred = []
      , loweringRuntimeResidue =
          ["target ABI chooses the physical record handle representation"]
      , loweringCostClass = Just SemanticRequired
      , loweringCostShape = emptyCostShape
          { costCodeSize = Just "one explicit semantic record identity"
          , costFrequency = Just "once per successful Begin recognition"
          }
      , loweringTargetPreconditions =
          [ "matching recognition succeeds before record materialization"
          , "record grammar matches the recognition grammar"
          ]
      , loweringAssumptions = []
      , loweringDerivedObligations = []
      , loweringInspectionPlan =
          [ "verify record identity is bound to the matching recognition event"
          , "verify record use is success-dominated"
          ]
      }

deriveRecordProjectionDecision
  :: Digest
  -> Digest
  -> RecognizedRecordWitness
  -> LoweringDecision
deriveRecordProjectionDecision sourceDigest targetDigest witness = provisional
  { loweringDecisionDigest = deriveLoweringDecisionDigest provisional }
  where
    semanticField = recognizedRecordGrammar witness <> "." <> recognizedRecordField witness
    provisional = LoweringDecision
      { loweringDecisionId = recognizedRecordProjectionDecision witness
      , loweringDecisionDigest = Digest ""
      , loweringSourceArtifactDigest = sourceDigest
      , loweringTargetArtifactDigest = targetDigest
      , loweringSourceRepresentation =
          "field " <> semanticField <> " of record " <> unValueId (recognizedRecordValue witness)
      , loweringTargetRepresentation =
          "typed scalar " <> unValueId (recognizedRecordProjectionOutput witness)
      , loweringSemanticEntities =
          [ "record:" <> unValueId (recognizedRecordValue witness)
          , "field:" <> semanticField
          , "value:" <> unValueId (recognizedRecordProjectionOutput witness)
          ]
      , loweringObligationRevisions = []
      , loweringAssuranceEntries = []
      , loweringAssuranceUses = []
      , loweringAction = Materialize
      , loweringRepresentationBefore =
          "recognized semantic record field " <> semanticField
      , loweringRepresentationAfter =
          "typed scalar projection with explicit record operand"
      , loweringInvariantsPreserved =
          [ "record identity"
          , "field identity"
          , "scalar width"
          , "recognition provenance"
          ]
      , loweringInvariantsTransferred = []
      , loweringRuntimeResidue =
          ["field extraction remains explicit at the target ABI boundary"]
      , loweringCostClass = Just SemanticRequired
      , loweringCostShape = emptyCostShape
          { costCodeSize = Just "one typed field accessor operation"
          , costFrequency = Just "once per successfully recognized Begin value"
          }
      , loweringTargetPreconditions =
          [ "record operand is the matching recognized semantic record"
          , "projected field is declared by the semantic record schema"
          , "successful recognition dominates field projection"
          ]
      , loweringAssumptions = []
      , loweringDerivedObligations = []
      , loweringInspectionPlan =
          [ "verify exact record operand survives lowering"
          , "verify exact field and scalar width survive lowering"
          , "verify exact receive consumes the projected scalar"
          ]
      }

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
