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

-- | Systems-level semantic identity for a record produced by a successful
-- recognition boundary.  This is deliberately not a physical pointer layout;
-- the LLVM/runtime ABI is allowed to choose an opaque handle representation.
data RecognizedRecordWitness = RecognizedRecordWitness
  { recognizedRecordFunction :: Text
  , recognizedRecordRecognitionBlock :: BlockId
  , recognizedRecordSuccessBlock :: BlockId
  , recognizedRecordPending :: ValueId
  , recognizedRecordGrammar :: Text
  , recognizedRecordValue :: ValueId
  , recognizedRecordProjection :: FieldProjectionWitness
  , recognizedRecordDecision :: DecisionId
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
  | RecognizedRecordProjectionTypeMismatch Text ValueId ScalarType SystemsValueRole
  | RecognizedRecordCommitMissing Text BlockId ValueId
  | RecognizedRecordProjectionCallMissing Text BlockId ValueId
  | RecognizedRecordProjectionCallMultiple Text BlockId ValueId Int
  | RecognizedRecordProjectionBeforeCommit Text BlockId ValueId
  | RecognizedRecordProjectionInputMismatch Text BlockId ValueId [ValueId]
  | RecognizedRecordProjectionDecisionMissing DecisionId
  | RecognizedRecordProjectionDecisionTargetMismatch DecisionId Digest Digest
  | RecognizedRecordDecisionMissing DecisionId
  | RecognizedRecordDecisionMismatch DecisionId
  | RecognizedRecordExactReceiveUseMissing Text ValueId
  deriving (Eq, Show)

phase0BeginRecordWitness :: RecognizedRecordWitness
phase0BeginRecordWitness = RecognizedRecordWitness
  { recognizedRecordFunction = fieldProjectionFunction phase0BeginLengthProjection
  , recognizedRecordRecognitionBlock = fieldProjectionRecognitionBlock phase0BeginLengthProjection
  , recognizedRecordSuccessBlock = fieldProjectionSuccessBlock phase0BeginLengthProjection
  , recognizedRecordPending = fieldProjectionPending phase0BeginLengthProjection
  , recognizedRecordGrammar = fieldProjectionGrammar phase0BeginLengthProjection
  , recognizedRecordValue = ValueId "server.begin_record"
  , recognizedRecordProjection = phase0BeginLengthProjection
  , recognizedRecordDecision = DecisionId "phase0.begin.record.identity"
  }

-- | Successor candidate to the certified semantic field-projection artifact.
-- It gives the recognized Begin value an explicit Systems identity and makes
-- Begin.length consume that exact record.  No physical record layout is chosen
-- here; the LLVM recognized-record ABI slice owns that choice.
phase0RecognizedRecordBundle :: Either RecognizedRecordError RecognizedRecordBundle
phase0RecognizedRecordBundle = do
  fieldBundle <- mapLeft RecognizedRecordFieldProjectionError phase0FieldProjectionBundle
  let witness = phase0BeginRecordWitness
  program <- materializeRecognizedRecordProgram
    witness
    (systemsArtifactProgram (fieldProjectionArtifact fieldBundle))
  let baseArtifact = fieldProjectionArtifact fieldBundle
      baseContract = systemsArtifactStageContract baseArtifact
      targetDigest = systemsProgramDigest program
      contract = baseContract
        { stageTargetArtifactDigest = targetDigest
        , stageTraceRelation = stageTraceRelation baseContract <>
            ["successful Begin recognition -> semantic RuntimeRecord Begin identity"]
        }
      sourceDigest = stageSourceArtifactDigest contract
      baseDecisions = loweringLedgerDecisions (systemsArtifactLoweringLedger baseArtifact)
      reboundDecisions = Map.map (rebindDecisionTarget targetDigest) baseDecisions
      recordDecision = deriveRecognizedRecordDecision sourceDigest targetDigest witness
      decisions = Map.insert (recognizedRecordDecision witness) recordDecision reboundDecisions
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
      baseSystemsContext = fieldProjectionContext fieldBundle
      baseManifest = systemsAssuranceManifest baseSystemsContext
      provisionalManifest = baseManifest
        { manifestImplementationDigest = systemsArtifactDigest artifact
        , manifestLoweringLedgerRoot = loweringRoot
        }
      manifest = provisionalManifest
        { manifestId = deriveManifestId
            (systemsAssuranceLedger baseSystemsContext)
            provisionalManifest
        }
      baseAssuranceContext = systemsAssuranceVerificationContext baseSystemsContext
      assuranceContext = baseAssuranceContext
        { verificationImplementationDigest = systemsArtifactDigest artifact
        , verificationLoweringLedgerRoot = loweringRoot
        }
      systemsContext = baseSystemsContext
        { systemsAssuranceManifest = manifest
        , systemsAssuranceVerificationContext = assuranceContext
        }
      bundle = RecognizedRecordBundle
        { recognizedRecordArtifact = artifact
        , recognizedRecordContext = systemsContext
        , recognizedRecordWitnesses = [witness]
        }
  verifyRecognizedRecordBundle bundle
  Right bundle

verifyRecognizedRecordBundle :: RecognizedRecordBundle -> Either RecognizedRecordError ()
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
      projection = recognizedRecordProjection witness
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
          functionName (recognizedRecordPending witness) grammar)
    other -> Left (RecognizedRecordPendingGrammarMismatch
      functionName (recognizedRecordPending witness) (showRole other))
  recognitionBlock <- case Map.lookup
      (recognizedRecordRecognitionBlock witness)
      (systemsFunctionBlocks function) of
    Nothing -> Left (RecognizedRecordRecognitionBlockMissing
      functionName (recognizedRecordRecognitionBlock witness))
    Just value -> Right value
  case systemsBlockTerminator recognitionBlock of
    TermRecognize { recognizePending = pending, recognizeSuccess = success }
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
          functionName (recognizedRecordValue witness) (recognizedRecordGrammar witness)
          (systemsValueRole recordValue))
    other -> Left (RecognizedRecordValueRoleMismatch
      functionName (recognizedRecordValue witness) (recognizedRecordGrammar witness) other)
  outputValue <- case Map.lookup
      (fieldProjectionOutput projection)
      (systemsFunctionValues function) of
    Nothing -> Left (RecognizedRecordProjectionOutputMissing
      functionName (fieldProjectionOutput projection))
    Just value -> Right value
  case systemsValueRole outputValue of
    TypedScalar actualType
      | actualType == fieldProjectionType projection -> pure ()
      | otherwise -> Left (RecognizedRecordProjectionTypeMismatch
          functionName (fieldProjectionOutput projection) (fieldProjectionType projection)
          (systemsValueRole outputValue))
    other -> Left (RecognizedRecordProjectionTypeMismatch
      functionName (fieldProjectionOutput projection) (fieldProjectionType projection) other)
  successBlock <- case Map.lookup
      (recognizedRecordSuccessBlock witness)
      (systemsFunctionBlocks function) of
    Nothing -> Left (RecognizedRecordSuccessBlockMissing
      functionName (recognizedRecordSuccessBlock witness))
    Just value -> Right value
  let operations = systemsBlockOps successBlock
      commitIndices =
        [ index
        | (index, OpCommitIngress { commitPending = pending }) <- zip [0 :: Int ..] operations
        , pending == recognizedRecordPending witness
        ]
      projectionCalls =
        [ (index, inputs)
        | (index, OpRuntimeCall
            { runtimeCallName = name
            , runtimeCallInputs = inputs
            , runtimeCallOutputs = outputs
            , runtimeCallSite = Nothing
            , runtimeCallDecision = decisionId
            }) <- zip [0 :: Int ..] operations
        , name == projectionRuntimeCallName projection
        , outputs == [fieldProjectionOutput projection]
        , decisionId == fieldProjectionDecision projection
        ]
  commitIndex <- case commitIndices of
    [] -> Left (RecognizedRecordCommitMissing
      functionName (recognizedRecordSuccessBlock witness) (recognizedRecordPending witness))
    firstIndex : _ -> Right firstIndex
  (projectionIndex, projectionInputs) <- case projectionCalls of
    [] -> Left (RecognizedRecordProjectionCallMissing
      functionName (recognizedRecordSuccessBlock witness) (fieldProjectionOutput projection))
    [single] -> Right single
    many -> Left (RecognizedRecordProjectionCallMultiple
      functionName (recognizedRecordSuccessBlock witness)
      (fieldProjectionOutput projection) (length many))
  unless (projectionIndex > commitIndex) $
    Left (RecognizedRecordProjectionBeforeCommit
      functionName (recognizedRecordSuccessBlock witness) (fieldProjectionOutput projection))
  unless (projectionInputs == [recognizedRecordValue witness]) $
    Left (RecognizedRecordProjectionInputMismatch
      functionName (recognizedRecordSuccessBlock witness)
      (fieldProjectionOutput projection) projectionInputs)
  let decisions = loweringLedgerDecisions (systemsArtifactLoweringLedger artifact)
      targetDigest = systemsProgramDigest program
  case Map.lookup (fieldProjectionDecision projection) decisions of
    Nothing -> Left (RecognizedRecordProjectionDecisionMissing (fieldProjectionDecision projection))
    Just decisionValue ->
      unless (loweringTargetArtifactDigest decisionValue == targetDigest) $
        Left (RecognizedRecordProjectionDecisionTargetMismatch
          (fieldProjectionDecision projection)
          targetDigest
          (loweringTargetArtifactDigest decisionValue))
  let expectedRecordDecision = deriveRecognizedRecordDecision
        (stageSourceArtifactDigest (systemsArtifactStageContract artifact))
        targetDigest
        witness
  case Map.lookup (recognizedRecordDecision witness) decisions of
    Nothing -> Left (RecognizedRecordDecisionMissing (recognizedRecordDecision witness))
    Just actualDecision ->
      unless (actualDecision == expectedRecordDecision) $
        Left (RecognizedRecordDecisionMismatch (recognizedRecordDecision witness))
  unless (any (usesExactLength (fieldProjectionOutput projection))
      (Map.elems (systemsFunctionBlocks function))) $
    Left (RecognizedRecordExactReceiveUseMissing
      functionName (fieldProjectionOutput projection))

materializeRecognizedRecordProgram
  :: RecognizedRecordWitness
  -> SystemsProgram
  -> Either RecognizedRecordError SystemsProgram
materializeRecognizedRecordProgram witness program = do
  let functionName = recognizedRecordFunction witness
      projection = recognizedRecordProjection witness
  function <- case Map.lookup functionName (systemsProgramFunctions program) of
    Nothing -> Left (RecognizedRecordFunctionMissing functionName)
    Just value -> Right value
  successBlock <- case Map.lookup
      (recognizedRecordSuccessBlock witness)
      (systemsFunctionBlocks function) of
    Nothing -> Left (RecognizedRecordSuccessBlockMissing
      functionName (recognizedRecordSuccessBlock witness))
    Just value -> Right value
  operations <- rewriteProjectionInputs functionName witness (systemsBlockOps successBlock)
  let recordValue = SystemsValue
        { systemsValueId = recognizedRecordValue witness
        , systemsValueRole = RuntimeRecord (recognizedRecordGrammar witness)
        , systemsStorageIdentity = Nothing
        }
      successBlock' = successBlock { systemsBlockOps = operations }
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
  where
    rewriteProjectionInputs functionName' witness' operations =
      case matchingIndices of
        [] -> Left (RecognizedRecordProjectionCallMissing
          functionName'
          (recognizedRecordSuccessBlock witness')
          (fieldProjectionOutput projection'))
        [_] -> Right (map rewrite operations)
        many -> Left (RecognizedRecordProjectionCallMultiple
          functionName'
          (recognizedRecordSuccessBlock witness')
          (fieldProjectionOutput projection')
          (length many))
      where
        projection' = recognizedRecordProjection witness'
        matchingIndices =
          [ index
          | (index, OpRuntimeCall
              { runtimeCallName = name
              , runtimeCallOutputs = outputs
              , runtimeCallSite = Nothing
              , runtimeCallDecision = decisionId
              }) <- zip [0 :: Int ..] operations
          , name == projectionRuntimeCallName projection'
          , outputs == [fieldProjectionOutput projection']
          , decisionId == fieldProjectionDecision projection'
          ]
        rewrite operation = case operation of
          call@OpRuntimeCall
            { runtimeCallName = name
            , runtimeCallOutputs = outputs
            , runtimeCallSite = Nothing
            , runtimeCallDecision = decisionId
            }
            | name == projectionRuntimeCallName projection'
                && outputs == [fieldProjectionOutput projection']
                && decisionId == fieldProjectionDecision projection' ->
                  call { runtimeCallInputs = [recognizedRecordValue witness'] }
          _ -> operation

rebindDecisionTarget :: Digest -> LoweringDecision -> LoweringDecision
rebindDecisionTarget targetDigest lowering = provisional
  { loweringDecisionDigest = deriveLoweringDecisionDigest provisional }
  where
    provisional = lowering { loweringTargetArtifactDigest = targetDigest }

deriveRecognizedRecordDecision
  :: Digest
  -> Digest
  -> RecognizedRecordWitness
  -> LoweringDecision
deriveRecognizedRecordDecision sourceDigest targetDigest witness = provisional
  { loweringDecisionDigest = deriveLoweringDecisionDigest provisional }
  where
    projection = recognizedRecordProjection witness
    recordName = unValueId (recognizedRecordValue witness)
    semanticRecord = recognizedRecordGrammar witness
    provisional = LoweringDecision
      { loweringDecisionId = recognizedRecordDecision witness
      , loweringDecisionDigest = Digest ""
      , loweringSourceArtifactDigest = sourceDigest
      , loweringTargetArtifactDigest = targetDigest
      , loweringSourceRepresentation = "successfully recognized semantic record " <> semanticRecord
      , loweringTargetRepresentation = "RuntimeRecord " <> semanticRecord <> " identity " <> recordName
      , loweringSemanticEntities =
          [ "record:" <> semanticRecord
          , "value:" <> recordName
          , "field:" <> semanticRecord <> "." <> fieldProjectionField projection
          ]
      , loweringObligationRevisions = []
      , loweringAssuranceEntries = []
      , loweringAssuranceUses = []
      , loweringAction = Materialize
      , loweringRepresentationBefore = "recognition-success semantic value"
      , loweringRepresentationAfter = "explicit Systems RuntimeRecord identity"
      , loweringInvariantsPreserved =
          [ "recognition provenance"
          , "record grammar identity"
          , "field projection consumes exact recognized record"
          ]
      , loweringInvariantsTransferred = []
      , loweringRuntimeResidue =
          ["physical record representation remains a target/runtime ABI choice"]
      , loweringCostClass = Just SemanticRequired
      , loweringCostShape = emptyCostShape
          { costCodeSize = Just "semantic record identity only"
          , costFrequency = Just "once per successfully recognized Begin value"
          }
      , loweringTargetPreconditions =
          [ "record identity is available only on recognition-success path"
          , "field projection consumes the exact recognized record"
          ]
      , loweringAssumptions = []
      , loweringDerivedObligations = []
      , loweringInspectionPlan =
          [ "verify LLVM record handle comes from the matching recognition result"
          , "verify typed accessor consumes that exact handle"
          ]
      }

projectionRuntimeCallName :: FieldProjectionWitness -> Text
projectionRuntimeCallName projection =
  "project recognized "
    <> fieldProjectionGrammar projection
    <> "."
    <> fieldProjectionField projection

usesExactLength :: ValueId -> SystemsBlock -> Bool
usesExactLength valueId blockValue = case systemsBlockTerminator blockValue of
  TermReceiveExact { exactLength = candidate } -> candidate == valueId
  _ -> False

showRole :: SystemsValueRole -> Text
showRole = fromString . show
  where
    fromString = Data.Text.pack

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
