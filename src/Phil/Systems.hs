module Phil.Systems
  ( module Phil.Systems.IR
  , module Phil.Systems.Verify
  , module Phil.Systems.Phase0
  , ScalarDataflowError (..)
  , verifyScalarDataflow
  , FieldProjectionWitness (..)
  , FieldProjectionBundle (..)
  , FieldProjectionError (..)
  , phase0BeginLengthProjection
  , phase0FieldProjectionBundle
  , verifyFieldProjectionBundle
  , verifyFieldProjectionWitnesses
  ) where

import Control.Monad (forM_, unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Assurance.Types
import Phil.Systems.IR
import Phil.Systems.Phase0
import Phil.Systems.Verify

data ScalarDataflowError
  = ScalarDefinitionMissing Text ValueId
  | ScalarDefinitionMultiple Text ValueId [(BlockId, Int)]
  | ScalarUseBeforeDefinition Text ValueId BlockId Int BlockId Int
  deriving (Eq, Show)

data ScalarSite = ScalarSite
  { scalarSiteBlock :: BlockId
  , scalarSiteIndex :: Int
  }
  deriving (Eq, Ord, Show)

data FieldProjectionWitness = FieldProjectionWitness
  { fieldProjectionFunction :: Text
  , fieldProjectionRecognitionBlock :: BlockId
  , fieldProjectionSuccessBlock :: BlockId
  , fieldProjectionPending :: ValueId
  , fieldProjectionGrammar :: Text
  , fieldProjectionField :: Text
  , fieldProjectionOutput :: ValueId
  , fieldProjectionType :: ScalarType
  , fieldProjectionDecision :: DecisionId
  }
  deriving (Eq, Show)

data FieldProjectionBundle = FieldProjectionBundle
  { fieldProjectionArtifact :: SystemsArtifact
  , fieldProjectionContext :: SystemsVerificationContext
  , fieldProjectionWitnesses :: [FieldProjectionWitness]
  }
  deriving (Eq, Show)

data FieldProjectionError
  = FieldProjectionSystemsError SystemsVerificationError
  | FieldProjectionScalarDataflowError ScalarDataflowError
  | FieldProjectionFunctionMissing Text
  | FieldProjectionRecognitionBlockMissing Text BlockId
  | FieldProjectionSuccessBlockMissing Text BlockId
  | FieldProjectionPendingMissing Text ValueId
  | FieldProjectionPendingGrammarMismatch Text ValueId Text
  | FieldProjectionRecognitionMismatch Text BlockId ValueId BlockId
  | FieldProjectionOutputMissing Text ValueId
  | FieldProjectionOutputTypeMismatch Text ValueId ScalarType SystemsValueRole
  | FieldProjectionSchemaMismatch Text Text ScalarType
  | FieldProjectionCommitMissing Text BlockId ValueId
  | FieldProjectionCallMissing Text BlockId ValueId
  | FieldProjectionCallMultiple Text BlockId ValueId Int
  | FieldProjectionCallBeforeCommit Text BlockId ValueId
  | FieldProjectionDecisionMissing DecisionId
  | FieldProjectionDecisionMismatch DecisionId
  | FieldProjectionExactReceiveUseMissing Text ValueId
  deriving (Eq, Show)

phase0BeginLengthProjection :: FieldProjectionWitness
phase0BeginLengthProjection = FieldProjectionWitness
  { fieldProjectionFunction = "UploadServer"
  , fieldProjectionRecognitionBlock = BlockId "server.version"
  , fieldProjectionSuccessBlock = BlockId "server.begin.commit"
  , fieldProjectionPending = ValueId "server.pending.begin"
  , fieldProjectionGrammar = "Begin"
  , fieldProjectionField = "length"
  , fieldProjectionOutput = ValueId "server.begin_length"
  , fieldProjectionType = ScalarUInt 64
  , fieldProjectionDecision = DecisionId "phase0.begin.length.projection"
  }

-- | Candidate next Phase 0 artifact.  The already-certified Phase 0 artifact is
-- intentionally left untouched: PHIL-LLVM-CERT-001 binds its exact digest.
-- This bundle materializes the source-level `begin.length` projection as a
-- typed scalar while retaining an explicit provenance witness and a dedicated
-- lowering decision.  A later certification slice can promote this candidate
-- after the runtime record/field ABI is selected.
phase0FieldProjectionBundle :: Either FieldProjectionError FieldProjectionBundle
phase0FieldProjectionBundle = do
  program <- materializeFieldProjectionProgram
    phase0BeginLengthProjection
    (systemsArtifactProgram phase0SystemsArtifact)
  let baseArtifact = phase0SystemsArtifact
      baseContract = systemsArtifactStageContract baseArtifact
      targetDigest = systemsProgramDigest program
      contract = baseContract
        { stageTargetArtifactDigest = targetDigest
        , stageTraceRelation = stageTraceRelation baseContract <>
            [ "recognized Begin.length -> typed server.begin_length scalar"
            ]
        }
      sourceDigest = stageSourceArtifactDigest contract
      baseDecisions = loweringLedgerDecisions (systemsArtifactLoweringLedger baseArtifact)
      reboundDecisions = Map.map (rebindDecisionTarget targetDigest) baseDecisions
      projectionDecision = deriveFieldProjectionDecision
        sourceDigest targetDigest phase0BeginLengthProjection
      decisions = Map.insert
        (fieldProjectionDecision phase0BeginLengthProjection)
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
      provisionalManifest = phase0SystemsAssuranceManifest
        { manifestImplementationDigest = systemsArtifactDigest artifact
        , manifestLoweringLedgerRoot = loweringRoot
        }
      manifest = provisionalManifest
        { manifestId = deriveManifestId phase0SystemsAssuranceLedger provisionalManifest }
      assuranceContext = phase0SystemsAssuranceContext
        { verificationImplementationDigest = systemsArtifactDigest artifact
        , verificationLoweringLedgerRoot = loweringRoot
        }
      systemsContext = phase0SystemsVerificationContext
        { systemsAssuranceManifest = manifest
        , systemsAssuranceVerificationContext = assuranceContext
        }
      bundle = FieldProjectionBundle
        { fieldProjectionArtifact = artifact
        , fieldProjectionContext = systemsContext
        , fieldProjectionWitnesses = [phase0BeginLengthProjection]
        }
  verifyFieldProjectionBundle bundle
  Right bundle

verifyFieldProjectionBundle :: FieldProjectionBundle -> Either FieldProjectionError ()
verifyFieldProjectionBundle bundle = do
  mapLeft FieldProjectionSystemsError $
    verifySystemsArtifact
      (fieldProjectionContext bundle)
      (fieldProjectionArtifact bundle)
  mapLeft FieldProjectionScalarDataflowError $
    verifyScalarDataflow (fieldProjectionArtifact bundle)
  verifyFieldProjectionWitnesses
    (fieldProjectionArtifact bundle)
    (fieldProjectionWitnesses bundle)

verifyFieldProjectionWitnesses
  :: SystemsArtifact
  -> [FieldProjectionWitness]
  -> Either FieldProjectionError ()
verifyFieldProjectionWitnesses artifact witnesses =
  forM_ witnesses (verifyFieldProjectionWitness artifact)

verifyFieldProjectionWitness
  :: SystemsArtifact
  -> FieldProjectionWitness
  -> Either FieldProjectionError ()
verifyFieldProjectionWitness artifact witness = do
  let program = systemsArtifactProgram artifact
      functionName = fieldProjectionFunction witness
  function <- case Map.lookup functionName (systemsProgramFunctions program) of
    Nothing -> Left (FieldProjectionFunctionMissing functionName)
    Just value -> Right value
  pendingValue <- case Map.lookup
      (fieldProjectionPending witness)
      (systemsFunctionValues function) of
    Nothing -> Left (FieldProjectionPendingMissing functionName (fieldProjectionPending witness))
    Just value -> Right value
  case systemsValueRole pendingValue of
    PendingIngress grammar
      | grammar == fieldProjectionGrammar witness -> pure ()
      | otherwise -> Left (FieldProjectionPendingGrammarMismatch
          functionName
          (fieldProjectionPending witness)
          grammar)
    _ -> Left (FieldProjectionPendingGrammarMismatch
      functionName
      (fieldProjectionPending witness)
      "not-pending-ingress")
  recognitionBlock <- case Map.lookup
      (fieldProjectionRecognitionBlock witness)
      (systemsFunctionBlocks function) of
    Nothing -> Left (FieldProjectionRecognitionBlockMissing
      functionName
      (fieldProjectionRecognitionBlock witness))
    Just value -> Right value
  case systemsBlockTerminator recognitionBlock of
    TermRecognize
      { recognizePending = pending
      , recognizeSuccess = success
      }
      | pending == fieldProjectionPending witness
          && success == fieldProjectionSuccessBlock witness -> pure ()
    _ -> Left (FieldProjectionRecognitionMismatch
      functionName
      (fieldProjectionRecognitionBlock witness)
      (fieldProjectionPending witness)
      (fieldProjectionSuccessBlock witness))
  outputValue <- case Map.lookup
      (fieldProjectionOutput witness)
      (systemsFunctionValues function) of
    Nothing -> Left (FieldProjectionOutputMissing functionName (fieldProjectionOutput witness))
    Just value -> Right value
  case systemsValueRole outputValue of
    TypedScalar actualType
      | actualType == fieldProjectionType witness -> pure ()
      | otherwise -> Left (FieldProjectionOutputTypeMismatch
          functionName
          (fieldProjectionOutput witness)
          (fieldProjectionType witness)
          (systemsValueRole outputValue))
    other -> Left (FieldProjectionOutputTypeMismatch
      functionName
      (fieldProjectionOutput witness)
      (fieldProjectionType witness)
      other)
  unless
    (fieldProjectionSchemaType
      (fieldProjectionGrammar witness)
      (fieldProjectionField witness)
      == Just (fieldProjectionType witness)) $
    Left (FieldProjectionSchemaMismatch
      (fieldProjectionGrammar witness)
      (fieldProjectionField witness)
      (fieldProjectionType witness))
  successBlock <- case Map.lookup
      (fieldProjectionSuccessBlock witness)
      (systemsFunctionBlocks function) of
    Nothing -> Left (FieldProjectionSuccessBlockMissing
      functionName
      (fieldProjectionSuccessBlock witness))
    Just value -> Right value
  let operations = systemsBlockOps successBlock
      commitIndices =
        [ index
        | (index, OpCommitIngress { commitPending = pending }) <- zip [0 ..] operations
        , pending == fieldProjectionPending witness
        ]
      projectionIndices =
        [ index
        | (index, OpRuntimeCall
            { runtimeCallName = name
            , runtimeCallInputs = inputs
            , runtimeCallOutputs = outputs
            , runtimeCallSite = Nothing
            , runtimeCallDecision = decisionId
            }) <- zip [0 ..] operations
        , name == fieldProjectionRuntimeCallName witness
        , null inputs
        , outputs == [fieldProjectionOutput witness]
        , decisionId == fieldProjectionDecision witness
        ]
  commitIndex <- case commitIndices of
    [] -> Left (FieldProjectionCommitMissing
      functionName
      (fieldProjectionSuccessBlock witness)
      (fieldProjectionPending witness))
    firstIndex : _ -> Right firstIndex
  projectionIndex <- case projectionIndices of
    [] -> Left (FieldProjectionCallMissing
      functionName
      (fieldProjectionSuccessBlock witness)
      (fieldProjectionOutput witness))
    [index] -> Right index
    many -> Left (FieldProjectionCallMultiple
      functionName
      (fieldProjectionSuccessBlock witness)
      (fieldProjectionOutput witness)
      (length many))
  unless (projectionIndex > commitIndex) $
    Left (FieldProjectionCallBeforeCommit
      functionName
      (fieldProjectionSuccessBlock witness)
      (fieldProjectionOutput witness))
  let decisions = loweringLedgerDecisions (systemsArtifactLoweringLedger artifact)
      sourceDigest = stageSourceArtifactDigest (systemsArtifactStageContract artifact)
      targetDigest = systemsProgramDigest program
      expectedDecision = deriveFieldProjectionDecision sourceDigest targetDigest witness
  case Map.lookup (fieldProjectionDecision witness) decisions of
    Nothing -> Left (FieldProjectionDecisionMissing (fieldProjectionDecision witness))
    Just actualDecision ->
      unless (actualDecision == expectedDecision) $
        Left (FieldProjectionDecisionMismatch (fieldProjectionDecision witness))
  unless (any (usesExactLength (fieldProjectionOutput witness))
      (Map.elems (systemsFunctionBlocks function))) $
    Left (FieldProjectionExactReceiveUseMissing
      functionName
      (fieldProjectionOutput witness))

materializeFieldProjectionProgram
  :: FieldProjectionWitness
  -> SystemsProgram
  -> Either FieldProjectionError SystemsProgram
materializeFieldProjectionProgram witness program = do
  let functionName = fieldProjectionFunction witness
  function <- case Map.lookup functionName (systemsProgramFunctions program) of
    Nothing -> Left (FieldProjectionFunctionMissing functionName)
    Just value -> Right value
  outputValue <- case Map.lookup
      (fieldProjectionOutput witness)
      (systemsFunctionValues function) of
    Nothing -> Left (FieldProjectionOutputMissing functionName (fieldProjectionOutput witness))
    Just value -> Right value
  successBlock <- case Map.lookup
      (fieldProjectionSuccessBlock witness)
      (systemsFunctionBlocks function) of
    Nothing -> Left (FieldProjectionSuccessBlockMissing
      functionName
      (fieldProjectionSuccessBlock witness))
    Just value -> Right value
  let projectionOperation = OpRuntimeCall
        { runtimeCallName = fieldProjectionRuntimeCallName witness
        , runtimeCallInputs = []
        , runtimeCallOutputs = [fieldProjectionOutput witness]
        , runtimeCallSite = Nothing
        , runtimeCallDecision = fieldProjectionDecision witness
        }
  operations <- insertAfterCommit
    functionName
    (fieldProjectionSuccessBlock witness)
    (fieldProjectionPending witness)
    projectionOperation
    (systemsBlockOps successBlock)
  let outputValue' = outputValue
        { systemsValueRole = TypedScalar (fieldProjectionType witness) }
      successBlock' = successBlock { systemsBlockOps = operations }
      function' = function
        { systemsFunctionValues = Map.insert
            (fieldProjectionOutput witness)
            outputValue'
            (systemsFunctionValues function)
        , systemsFunctionBlocks = Map.insert
            (fieldProjectionSuccessBlock witness)
            successBlock'
            (systemsFunctionBlocks function)
        }
  Right program
    { systemsProgramFunctions = Map.insert
        functionName
        function'
        (systemsProgramFunctions program)
    }

insertAfterCommit
  :: Text
  -> BlockId
  -> ValueId
  -> SystemsOp
  -> [SystemsOp]
  -> Either FieldProjectionError [SystemsOp]
insertAfterCommit functionName blockId pending projectionOperation operations =
  case break isCommit operations of
    (_, []) -> Left (FieldProjectionCommitMissing functionName blockId pending)
    (before, commitOperation : after) ->
      Right (before <> [commitOperation, projectionOperation] <> after)
  where
    isCommit operation = case operation of
      OpCommitIngress { commitPending = candidate } -> candidate == pending
      _ -> False

rebindDecisionTarget :: Digest -> LoweringDecision -> LoweringDecision
rebindDecisionTarget targetDigest lowering = provisional
  { loweringDecisionDigest = deriveLoweringDecisionDigest provisional }
  where
    provisional = lowering { loweringTargetArtifactDigest = targetDigest }

deriveFieldProjectionDecision
  :: Digest
  -> Digest
  -> FieldProjectionWitness
  -> LoweringDecision
deriveFieldProjectionDecision sourceDigest targetDigest witness = provisional
  { loweringDecisionDigest = deriveLoweringDecisionDigest provisional }
  where
    semanticField = fieldProjectionGrammar witness <> "." <> fieldProjectionField witness
    provisional = LoweringDecision
      { loweringDecisionId = fieldProjectionDecision witness
      , loweringDecisionDigest = Digest ""
      , loweringSourceArtifactDigest = sourceDigest
      , loweringTargetArtifactDigest = targetDigest
      , loweringSourceRepresentation = "recognized semantic record field " <> semanticField
      , loweringTargetRepresentation =
          "typed scalar " <> unValueId (fieldProjectionOutput witness)
      , loweringSemanticEntities =
          [ "field:" <> semanticField
          , "value:" <> unValueId (fieldProjectionOutput witness)
          ]
      , loweringObligationRevisions = []
      , loweringAssuranceEntries = []
      , loweringAssuranceUses = []
      , loweringAction = Materialize
      , loweringRepresentationBefore =
          "recognized " <> fieldProjectionGrammar witness <> " semantic value"
      , loweringRepresentationAfter =
          "typed scalar field " <> unValueId (fieldProjectionOutput witness)
      , loweringInvariantsPreserved =
          [ "recognition provenance"
          , "field identity"
          , "scalar width"
          ]
      , loweringInvariantsTransferred = []
      , loweringRuntimeResidue =
          [ "field extraction remains an explicit semantic call until a concrete record ABI is selected" ]
      , loweringCostClass = Just SemanticRequired
      , loweringCostShape = emptyCostShape
          { costCodeSize = Just "one explicit field-projection operation"
          , costFrequency = Just "once per successfully recognized Begin value"
          }
      , loweringTargetPreconditions =
          [ "successful recognition dominates field projection"
          , "projected field is declared by the semantic record schema"
          ]
      , loweringAssumptions = []
      , loweringDerivedObligations = []
      , loweringInspectionPlan =
          [ "verify the projection stays in the recognition-success path"
          , "verify exact receive consumes the projected scalar"
          ]
      }

fieldProjectionRuntimeCallName :: FieldProjectionWitness -> Text
fieldProjectionRuntimeCallName witness =
  "project recognized "
    <> fieldProjectionGrammar witness
    <> "."
    <> fieldProjectionField witness

fieldProjectionSchemaType :: Text -> Text -> Maybe ScalarType
fieldProjectionSchemaType grammar fieldName = case (grammar, fieldName) of
  ("Begin", "length") -> Just (ScalarUInt 64)
  _ -> Nothing

usesExactLength :: ValueId -> SystemsBlock -> Bool
usesExactLength valueId blockValue = case systemsBlockTerminator blockValue of
  TermReceiveExact { exactLength = candidate } -> candidate == valueId
  _ -> False

verifyScalarDataflow :: SystemsArtifact -> Either ScalarDataflowError ()
verifyScalarDataflow artifact =
  forM_ (Map.elems (systemsProgramFunctions (systemsArtifactProgram artifact))) verifyFunction

verifyFunction :: SystemsFunction -> Either ScalarDataflowError ()
verifyFunction function = do
  let functionName = systemsFunctionName function
      typedScalars = Set.fromList
        [ valueId
        | (valueId, value) <- Map.toAscList (systemsFunctionValues function)
        , TypedScalar _ <- [systemsValueRole value]
        ]
      definitions = collectDefinitions function typedScalars
      uses = collectUses function typedScalars
  forM_ (Set.toAscList typedScalars) $ \valueId ->
    case Map.findWithDefault [] valueId definitions of
      [] -> Left (ScalarDefinitionMissing functionName valueId)
      [_] -> pure ()
      sites -> Left
        (ScalarDefinitionMultiple functionName valueId
          [ (scalarSiteBlock site, scalarSiteIndex site) | site <- sites ])
  forM_ uses $ \(valueId, useSite) ->
    case Map.findWithDefault [] valueId definitions of
      [definitionSite] ->
        unless (definitionPrecedesUse function definitionSite useSite) $
          Left (ScalarUseBeforeDefinition
            functionName
            valueId
            (scalarSiteBlock definitionSite)
            (scalarSiteIndex definitionSite)
            (scalarSiteBlock useSite)
            (scalarSiteIndex useSite))
      _ -> pure ()

collectDefinitions
  :: SystemsFunction
  -> Set.Set ValueId
  -> Map.Map ValueId [ScalarSite]
collectDefinitions function typedScalars = Map.fromListWith (<>)
  [ (valueId, [ScalarSite (systemsBlockId blockValue) operationIndex])
  | blockValue <- Map.elems (systemsFunctionBlocks function)
  , (operationIndex, operation) <- zip [0 ..] (systemsBlockOps blockValue)
  , valueId <- operationDefinitions operation
  , Set.member valueId typedScalars
  ]

collectUses
  :: SystemsFunction
  -> Set.Set ValueId
  -> [(ValueId, ScalarSite)]
collectUses function typedScalars = concat
  [ operationUsesInBlock blockValue <> terminatorUsesInBlock blockValue
  | blockValue <- Map.elems (systemsFunctionBlocks function)
  ]
  where
    operationUsesInBlock blockValue =
      [ (valueId, ScalarSite (systemsBlockId blockValue) operationIndex)
      | (operationIndex, operation) <- zip [0 ..] (systemsBlockOps blockValue)
      , valueId <- operationUses operation
      , Set.member valueId typedScalars
      ]
    terminatorUsesInBlock blockValue =
      [ (valueId, ScalarSite (systemsBlockId blockValue) (length (systemsBlockOps blockValue)))
      | valueId <- terminatorUses (systemsBlockTerminator blockValue)
      , Set.member valueId typedScalars
      ]

operationDefinitions :: SystemsOp -> [ValueId]
operationDefinitions operation = case operation of
  OpRuntimeCall { runtimeCallOutputs = outputs } -> outputs
  OpCopy { copyTarget = target } -> [target]
  OpScalarLiteral { scalarLiteralOutput = output } -> [output]
  _ -> []

operationUses :: SystemsOp -> [ValueId]
operationUses operation = case operation of
  OpRuntimeCall { runtimeCallInputs = inputs } -> inputs
  OpCopy { copySource = source } -> [source]
  _ -> []

terminatorUses :: SystemsTerminator -> [ValueId]
terminatorUses terminator = case terminator of
  TermBranch condition _ _ -> [condition]
  TermRuntimeCheck { checkInputs = inputs } -> inputs
  TermReceiveExact { exactLength = lengthValue } -> [lengthValue]
  TermReturnScalar valueId -> [valueId]
  _ -> []

definitionPrecedesUse :: SystemsFunction -> ScalarSite -> ScalarSite -> Bool
definitionPrecedesUse function definitionSite useSite
  | scalarSiteBlock definitionSite == scalarSiteBlock useSite =
      scalarSiteIndex definitionSite < scalarSiteIndex useSite
  | otherwise = blockDominates function (scalarSiteBlock definitionSite) (scalarSiteBlock useSite)

blockDominates :: SystemsFunction -> BlockId -> BlockId -> Bool
blockDominates function definitionBlock useBlock =
  not (reachableAvoiding function (Set.singleton definitionBlock) (systemsFunctionEntry function) useBlock)

reachableAvoiding
  :: SystemsFunction
  -> Set.Set BlockId
  -> BlockId
  -> BlockId
  -> Bool
reachableAvoiding function avoided start target
  | Set.member start avoided = False
  | otherwise = go Set.empty [start]
  where
    go _ [] = False
    go seen (current : rest)
      | current == target = True
      | Set.member current seen = go seen rest
      | Set.member current avoided = go seen rest
      | otherwise =
          let successors = case Map.lookup current (systemsFunctionBlocks function) of
                Nothing -> []
                Just blockValue -> blockSuccessors blockValue
          in go (Set.insert current seen) (successors <> rest)

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
