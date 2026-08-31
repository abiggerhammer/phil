{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.GenericLowering
  ( CoreSystemsValueRole (..)
  , CoreSystemsOperation (..)
  , CoreSystemsTerminator (..)
  , CoreSystemsBlock (..)
  , CoreSystemsFunction (..)
  , CoreSystemsProgram (..)
  , RealizedOperation (..)
  , RealizedTargetChoice (..)
  , GenericRealizationContext (..)
  , GenericLoweringError (..)
  , coreSystemsProgramSemanticForm
  , lowerGenericSystems
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types (Digest, RevisionId (..), digestText)
import Phil.Core.Static
  ( ArchitectureRealizationDescriptor (..)
  , CheckedArchitectureInstance (..)
  , InstanceRevision (..)
  , SemanticForm (..)
  , canonicalSemanticForm
  , deriveArchitectureRealizationIdentity
  , identityInstanceRevision
  , identityRealizationRevision
  )
import Phil.Systems.IR
import Phil.Systems.Phase1Stage

-- | Target-abstract, already-checked Core execution vocabulary consumed by the
-- generic Phase-1 Systems producer. This is deliberately smaller than Systems
-- IR: runtime symbols, ABI/layout choices, target assumptions, qualifications,
-- and costs enter only through 'GenericRealizationContext'.
data CoreSystemsValueRole
  = CoreOwnedValue Text
  | CoreBorrowedValue Text
  | CoreInputValue Text
  deriving (Eq, Ord, Show)

data CoreSystemsOperation
  = CoreSystemsCall
      { coreCallOperation :: Text
      , coreCallInputs :: [Text]
      , coreCallOutputs :: [Text]
      }
  | CoreSystemsTrace Text
  deriving (Eq, Ord, Show)

data CoreSystemsTerminator
  = CoreSystemsJump Text
  | CoreSystemsChoice
      { coreChoiceOperation :: Text
      , coreChoiceInputs :: [Text]
      , coreChoiceArms :: Map Text Text
      }
  | CoreSystemsEnd Text
  deriving (Eq, Ord, Show)

data CoreSystemsBlock = CoreSystemsBlock
  { coreBlockKey :: Text
  , coreBlockOperations :: [CoreSystemsOperation]
  , coreBlockTerminator :: CoreSystemsTerminator
  }
  deriving (Eq, Ord, Show)

data CoreSystemsFunction = CoreSystemsFunction
  { coreFunctionKey :: Text
  , coreFunctionEntry :: Text
  , coreFunctionValues :: Map Text CoreSystemsValueRole
  , coreFunctionBlocks :: Map Text CoreSystemsBlock
  }
  deriving (Eq, Ord, Show)

-- | Presentation is deliberately absent from semantic identity. Renaming a
-- witness therefore cannot select another lowering rule.
data CoreSystemsProgram = CoreSystemsProgram
  { coreProgramLabel :: Text
  , coreProgramProfile :: CompilationProfile
  , coreProgramFunctions :: Map Text CoreSystemsFunction
  , coreProgramFacts :: Set Text
  }
  deriving (Eq, Show)

data RealizedOperation = RealizedOperation
  { realizedOperationRuntimeName :: Text
  , realizedOperationQualificationRefs :: Set Text
  , realizedOperationAssumptions :: Set Text
  , realizedOperationCostClass :: CostClass
  , realizedOperationCostShape :: CostShape
  , realizedOperationTargetPreconditions :: [Text]
  , realizedOperationDerivedObligations :: [RevisionId]
  }
  deriving (Eq, Ord, Show)

data RealizedTargetChoice = RealizedTargetChoice
  { realizedTargetDecisionId :: DecisionId
  , realizedTargetSourceRepresentation :: Text
  , realizedTargetRepresentation :: Text
  , realizedTargetSemanticEntities :: [Text]
  , realizedTargetAction :: LoweringAction
  , realizedTargetCostClass :: CostClass
  , realizedTargetCostShape :: CostShape
  , realizedTargetPreconditions :: [Text]
  , realizedTargetAssumptions :: [Text]
  , realizedTargetDerivedObligations :: [RevisionId]
  , realizedTargetInspectionPlan :: [Text]
  }
  deriving (Eq, Ord, Show)

-- | Explicit ADR-020 realization input. There is no program or witness
-- discriminator. Ambient runtime discovery is not realization authority.
data GenericRealizationContext = GenericRealizationContext
  { genericContextRevision :: Text
  , genericContextSemantics :: SemanticForm
  , genericContextVerifierProfile :: Text
  , genericContextRealizationRefs :: Set Text
  , genericContextQualificationRefs :: Set Text
  , genericContextAssumptions :: Set Text
  , genericContextOperations :: Map Text RealizedOperation
  , genericContextTargetChoices :: [RealizedTargetChoice]
  }
  deriving (Eq, Show)

data GenericLoweringError
  = GenericLoweringEmptyVerifierProfile
  | GenericLoweringEmptyContextRevision
  | GenericLoweringEmptyRealizationRefs
  | GenericLoweringEmptyFacts
  | GenericLoweringEmptyFunctions
  | GenericLoweringMissingEntry Text Text
  | GenericLoweringBlockKeyMismatch Text Text Text
  | GenericLoweringUnknownBlockTarget Text Text Text
  | GenericLoweringUnknownValue Text Text Text
  | GenericLoweringMissingOperationRealization Text
  | GenericLoweringDuplicateDecision DecisionId
  | GenericLoweringStageRejected Phase1StageVerificationError
  deriving (Eq, Show)

coreSystemsProgramSemanticForm :: CoreSystemsProgram -> SemanticForm
coreSystemsProgramSemanticForm program = SemanticRecord (Map.fromList
  [ ("profile", SemanticAtom (profileText (coreProgramProfile program)))
  , ("facts", SemanticUnordered (Set.map SemanticAtom (coreProgramFacts program)))
  , ("functions", SemanticRecord
      (Map.map functionSemanticForm (coreProgramFunctions program)))
  ])

lowerGenericSystems
  :: CheckedArchitectureInstance
  -> CoreSystemsProgram
  -> GenericRealizationContext
  -> Either GenericLoweringError Phase1StageBundle
lowerGenericSystems checked program context = do
  validateInputs program context
  systemsProgram <- lowerProgram program context
  let sourceDigest = deriveSourceDigest checked program
      targetDigest = systemsProgramDigest systemsProgram
  opDecisions <- operationDecisions sourceDigest targetDigest program context
  targetDecisions <- mapM (targetDecision sourceDigest targetDigest)
    (genericContextTargetChoices context)
  decisions <- uniqueDecisions (opDecisions <> targetDecisions)
  let ledger = LoweringLedger
        { loweringLedgerDecisions = decisions
        , loweringLedgerRoot = deriveLoweringLedgerRoot decisions
        }
      contract = makeStageContract
        checked sourceDigest targetDigest program context decisions
      artifact = SystemsArtifact
        { systemsArtifactProgram = systemsProgram
        , systemsArtifactStageContract = contract
        , systemsArtifactLoweringLedger = ledger
        }
      instanceIdentity = checkedArchitectureIdentity checked
      realizationIdentity = deriveArchitectureRealizationIdentity
        ArchitectureRealizationDescriptor
          { realizationInstanceIdentity = instanceIdentity
          , realizationSemantics = realizationSemanticForm program context
          }
      assumptions = Set.unions
        [ genericContextAssumptions context
        , Set.unions
            [ realizedOperationAssumptions realized
            | realized <- Map.elems (genericContextOperations context)
            ]
        , Set.fromList
            (concatMap realizedTargetAssumptions
              (genericContextTargetChoices context))
        ]
      facts = collectSourceFacts artifact
      mechanisms = collectSystemsMechanisms artifact
      dispositions = Map.fromSet
        (const (phase1FactDisposition mechanisms assumptions)) facts
      qualifications = Set.union
        (genericContextQualificationRefs context)
        (Set.unions
          [ realizedOperationQualificationRefs realized
          | realized <- Map.elems (genericContextOperations context)
          ])
      justifications = Map.fromSet
        (const SystemsJustification
          { systemsJustificationSourceFacts = facts
          , systemsJustificationRealizationRefs =
              genericContextRealizationRefs context
          , systemsJustificationQualificationRefs = qualifications
          , systemsJustificationAssumptionRefs = assumptions
          })
        mechanisms
      bundle = makePhase1StageBundle
        (identityInstanceRevision instanceIdentity)
        (identityRealizationRevision realizationIdentity)
        (genericContextVerifierProfile context)
        artifact
        dispositions
        justifications
  case verifyPhase1StageBundle bundle of
    Left err -> Left (GenericLoweringStageRejected err)
    Right () -> Right bundle

validateInputs
  :: CoreSystemsProgram
  -> GenericRealizationContext
  -> Either GenericLoweringError ()
validateInputs program context = do
  require (not (Text.null (genericContextVerifierProfile context)))
    GenericLoweringEmptyVerifierProfile
  require (not (Text.null (genericContextRevision context)))
    GenericLoweringEmptyContextRevision
  require (not (Set.null (genericContextRealizationRefs context)))
    GenericLoweringEmptyRealizationRefs
  require (not (Set.null (coreProgramFacts program)))
    GenericLoweringEmptyFacts
  require (not (Map.null (coreProgramFunctions program)))
    GenericLoweringEmptyFunctions
  mapM_ validateFunction (Map.toAscList (coreProgramFunctions program))
  mapM_ requireOperation (Set.toAscList (programOperationKeys program))
  where
    requireOperation key =
      require (Map.member key (genericContextOperations context))
        (GenericLoweringMissingOperationRealization key)

validateFunction :: (Text, CoreSystemsFunction) -> Either GenericLoweringError ()
validateFunction (functionMapKey, function) = do
  require (Map.member (coreFunctionEntry function) blocks)
    (GenericLoweringMissingEntry functionMapKey (coreFunctionEntry function))
  mapM_ validateRole (Map.toAscList values)
  mapM_ validateBlock (Map.toAscList blocks)
  where
    values = coreFunctionValues function
    blocks = coreFunctionBlocks function

    validateRole (_, role) = case role of
      CoreBorrowedValue owner -> validateValue owner
      CoreOwnedValue _ -> Right ()
      CoreInputValue _ -> Right ()

    validateBlock (blockMapKey, blockValue) = do
      require (blockMapKey == coreBlockKey blockValue)
        (GenericLoweringBlockKeyMismatch functionMapKey blockMapKey
          (coreBlockKey blockValue))
      mapM_ validateOperationValues (coreBlockOperations blockValue)
      validateTerminatorValues (coreBlockTerminator blockValue)
      mapM_ validateTarget (terminatorTargets (coreBlockTerminator blockValue))

    validateOperationValues operation = case operation of
      CoreSystemsCall _ inputs outputs -> mapM_ validateValue (inputs <> outputs)
      CoreSystemsTrace _ -> Right ()

    validateTerminatorValues terminator = case terminator of
      CoreSystemsJump _ -> Right ()
      CoreSystemsChoice _ inputs _ -> mapM_ validateValue inputs
      CoreSystemsEnd _ -> Right ()

    validateValue key =
      require (Map.member key values)
        (GenericLoweringUnknownValue functionMapKey (coreFunctionKey function) key)

    validateTarget target =
      require (Map.member target blocks)
        (GenericLoweringUnknownBlockTarget functionMapKey
          (coreFunctionKey function) target)

lowerProgram
  :: CoreSystemsProgram
  -> GenericRealizationContext
  -> Either GenericLoweringError SystemsProgram
lowerProgram program context = do
  functions <- Map.traverseWithKey lowerFunction (coreProgramFunctions program)
  pure SystemsProgram
    { systemsProgramName = "phil.phase1.core:" <> canonicalProgramIdentity program
    , systemsProgramProfile = coreProgramProfile program
    , systemsProgramFunctions = functions
    }
  where
    lowerFunction _ function = do
      blocks <- Map.traverseWithKey (lowerBlock function)
        (coreFunctionBlocks function)
      pure SystemsFunction
        { systemsFunctionName = coreFunctionKey function
        , systemsFunctionEntry = BlockId (coreFunctionEntry function)
        , systemsFunctionValues = Map.fromList
            [ (ValueId key, lowerValue key role)
            | (key, role) <- Map.toAscList (coreFunctionValues function)
            ]
        , systemsFunctionBlocks = blocks
        }

    lowerBlock function blockMapKey blockValue = do
      operations <- mapM
        (uncurry (lowerOperation function blockMapKey))
        (zip [(0 :: Int) ..] (coreBlockOperations blockValue))
      terminator <- lowerTerminator (coreBlockTerminator blockValue)
      pure SystemsBlock
        { systemsBlockId = BlockId (coreBlockKey blockValue)
        , systemsBlockOps = operations
        , systemsBlockTerminator = terminator
        }

    lowerOperation function blockKey index operation = case operation of
      CoreSystemsTrace label -> Right (OpTraceEvent label)
      CoreSystemsCall operationKey inputs outputs -> do
        realized <- realizedFor operationKey context
        pure OpRuntimeCall
          { runtimeCallName = realizedOperationRuntimeName realized
          , runtimeCallInputs = map ValueId inputs
          , runtimeCallOutputs = map ValueId outputs
          , runtimeCallSite = Nothing
          , runtimeCallDecision = operationDecisionId
              (coreFunctionKey function) blockKey
              ("op." <> Text.pack (show index))
          }

    lowerTerminator terminator = case terminator of
      CoreSystemsJump target -> Right (TermJump (BlockId target))
      CoreSystemsEnd outcome -> Right (TermEnd outcome)
      CoreSystemsChoice operationKey inputs arms -> do
        realized <- realizedFor operationKey context
        pure TermRuntimeChoice
          { runtimeChoiceName = realizedOperationRuntimeName realized
          , runtimeChoiceInputs = map ValueId inputs
          , runtimeChoiceSite = Nothing
          , runtimeChoiceArms = Map.map
              (SystemsRuntimeChoiceArm Nothing . BlockId) arms
          }

lowerValue :: Text -> CoreSystemsValueRole -> SystemsValue
lowerValue key role = SystemsValue
  { systemsValueId = ValueId key
  , systemsValueRole = case role of
      CoreOwnedValue _ -> OwnedBuffer "CoreOwned"
      CoreBorrowedValue owner -> BorrowedSlice (ValueId owner)
      CoreInputValue description -> RuntimeInput description
  , systemsStorageIdentity = case role of
      CoreOwnedValue storage -> Just storage
      CoreBorrowedValue _ -> Nothing
      CoreInputValue _ -> Nothing
  }

operationDecisions
  :: Digest
  -> Digest
  -> CoreSystemsProgram
  -> GenericRealizationContext
  -> Either GenericLoweringError [(DecisionId, LoweringDecision)]
operationDecisions sourceDigest targetDigest program context =
  concat <$> mapM functionDecisions (Map.toAscList (coreProgramFunctions program))
  where
    functionDecisions (_, function) =
      concat <$> mapM (blockDecisions function)
        (Map.toAscList (coreFunctionBlocks function))

    blockDecisions function (blockKey, blockValue) = do
      opItems <- fmap concat $ mapM
        (uncurry (operationItem function blockKey))
        (zip [(0 :: Int) ..] (coreBlockOperations blockValue))
      termItems <- terminatorItem function blockKey
        (coreBlockTerminator blockValue)
      pure (opItems <> termItems)

    operationItem function blockKey index operation = case operation of
      CoreSystemsTrace _ -> Right []
      CoreSystemsCall key _ _ -> do
        realized <- realizedFor key context
        let decisionId = operationDecisionId
              (coreFunctionKey function) blockKey
              ("op." <> Text.pack (show index))
        pure [(decisionId, realizedDecision
          sourceDigest targetDigest decisionId key realized)]

    terminatorItem function blockKey terminator = case terminator of
      CoreSystemsChoice key _ _ -> do
        realized <- realizedFor key context
        let decisionId = operationDecisionId
              (coreFunctionKey function) blockKey "term"
        pure [(decisionId, realizedDecision
          sourceDigest targetDigest decisionId key realized)]
      CoreSystemsJump _ -> Right []
      CoreSystemsEnd _ -> Right []

realizedDecision
  :: Digest
  -> Digest
  -> DecisionId
  -> Text
  -> RealizedOperation
  -> LoweringDecision
realizedDecision sourceDigest targetDigest decisionId operationKey realized =
  provisional { loweringDecisionDigest = deriveLoweringDecisionDigest provisional }
  where
    provisional = LoweringDecision
      { loweringDecisionId = decisionId
      , loweringDecisionDigest = digestText "pending"
      , loweringSourceArtifactDigest = sourceDigest
      , loweringTargetArtifactDigest = targetDigest
      , loweringSourceRepresentation = "checked-core-operation:" <> operationKey
      , loweringTargetRepresentation =
          "systems-runtime-operation:" <> realizedOperationRuntimeName realized
      , loweringSemanticEntities = [operationKey]
      , loweringObligationRevisions = []
      , loweringAssuranceEntries = []
      , loweringAssuranceUses = []
      , loweringAction = Materialize
      , loweringRepresentationBefore = "checked Core operation"
      , loweringRepresentationAfter = "Systems runtime operation/control"
      , loweringInvariantsPreserved = ["core-operation-correspondence"]
      , loweringInvariantsTransferred = []
      , loweringRuntimeResidue = []
      , loweringCostClass = Just (realizedOperationCostClass realized)
      , loweringCostShape = realizedOperationCostShape realized
      , loweringTargetPreconditions = realizedOperationTargetPreconditions realized
      , loweringAssumptions = Set.toAscList (realizedOperationAssumptions realized)
      , loweringDerivedObligations = realizedOperationDerivedObligations realized
      , loweringInspectionPlan =
          ["verify exact checked-Core operation correspondence"]
      }

targetDecision
  :: Digest
  -> Digest
  -> RealizedTargetChoice
  -> Either GenericLoweringError (DecisionId, LoweringDecision)
targetDecision sourceDigest targetDigest choice = Right
  (decisionId, provisional
    { loweringDecisionDigest = deriveLoweringDecisionDigest provisional })
  where
    decisionId = realizedTargetDecisionId choice
    provisional = LoweringDecision
      { loweringDecisionId = decisionId
      , loweringDecisionDigest = digestText "pending"
      , loweringSourceArtifactDigest = sourceDigest
      , loweringTargetArtifactDigest = targetDigest
      , loweringSourceRepresentation = realizedTargetSourceRepresentation choice
      , loweringTargetRepresentation = realizedTargetRepresentation choice
      , loweringSemanticEntities = realizedTargetSemanticEntities choice
      , loweringObligationRevisions = []
      , loweringAssuranceEntries = []
      , loweringAssuranceUses = []
      , loweringAction = realizedTargetAction choice
      , loweringRepresentationBefore = realizedTargetSourceRepresentation choice
      , loweringRepresentationAfter = realizedTargetRepresentation choice
      , loweringInvariantsPreserved = ["explicit-target-realization-choice"]
      , loweringInvariantsTransferred = []
      , loweringRuntimeResidue = []
      , loweringCostClass = Just (realizedTargetCostClass choice)
      , loweringCostShape = realizedTargetCostShape choice
      , loweringTargetPreconditions = realizedTargetPreconditions choice
      , loweringAssumptions = realizedTargetAssumptions choice
      , loweringDerivedObligations = realizedTargetDerivedObligations choice
      , loweringInspectionPlan = realizedTargetInspectionPlan choice
      }

uniqueDecisions
  :: [(DecisionId, LoweringDecision)]
  -> Either GenericLoweringError (Map DecisionId LoweringDecision)
uniqueDecisions = go Map.empty
  where
    go result [] = Right result
    go result ((key, value) : rest)
      | Map.member key result = Left (GenericLoweringDuplicateDecision key)
      | otherwise = go (Map.insert key value result) rest

makeStageContract
  :: CheckedArchitectureInstance
  -> Digest
  -> Digest
  -> CoreSystemsProgram
  -> GenericRealizationContext
  -> Map DecisionId LoweringDecision
  -> StageContract
makeStageContract checked sourceDigest targetDigest program context decisions =
  StageContract
    { stageContractId =
        "phil.phase1.generic.core-to-systems.v1:" <> genericContextRevision context
    , stageSourceArtifactDigest = sourceDigest
    , stageTargetArtifactDigest = targetDigest
    , stageFacts =
        [ FactTransfer
            { factTransferId = fact
            , factSourceRevision = Nothing
            , factDisposition = FactConsumed
                "preserved by generic checked-Core to Systems accounting"
            }
        | fact <- Set.toAscList (coreProgramFacts program)
        ]
    , stageInvariants = Map.empty
    , stageRequiredEdges = []
    , stageDerivedObligations = Set.toAscList (Set.fromList
        (concatMap loweringDerivedObligations (Map.elems decisions)))
    , stageAssumptions = Set.toAscList (Set.unions
        [ genericContextAssumptions context
        , Set.unions
            [ Set.fromList (loweringAssumptions decision)
            | decision <- Map.elems decisions
            ]
        ])
    , stageTraceRelation =
        [ "architecture-instance="
            <> unInstanceRevision
              (identityInstanceRevision (checkedArchitectureIdentity checked))
        ]
        <> correspondenceTrace program
    , stageResourceFailureRelation =
        [ "checked Core resource/failure obligations remain explicit facts or "
            <> "realization assumptions; Systems lowering may not silently drop them"
        ]
    }

realizationSemanticForm
  :: CoreSystemsProgram
  -> GenericRealizationContext
  -> SemanticForm
realizationSemanticForm program context = SemanticRecord (Map.fromList
  [ ("core", coreSystemsProgramSemanticForm program)
  , ("context_revision", SemanticAtom (genericContextRevision context))
  , ("context", genericContextSemantics context)
  , ("realization_refs", SemanticUnordered
      (Set.map SemanticAtom (genericContextRealizationRefs context)))
  , ("qualification_refs", SemanticUnordered
      (Set.map SemanticAtom (genericContextQualificationRefs context)))
  , ("assumptions", SemanticUnordered
      (Set.map SemanticAtom (genericContextAssumptions context)))
  , ("operations", SemanticRecord
      (Map.map realizedOperationSemanticForm (genericContextOperations context)))
  , ("verifier_profile", SemanticAtom (genericContextVerifierProfile context))
  , ("target_choices", SemanticUnordered (Set.fromList
      (map targetChoiceSemanticForm (genericContextTargetChoices context))))
  ])

deriveSourceDigest
  :: CheckedArchitectureInstance
  -> CoreSystemsProgram
  -> Digest
deriveSourceDigest checked program = digestText
  ("phil.phase1.checked-core-source.v1:"
    <> unInstanceRevision
      (identityInstanceRevision (checkedArchitectureIdentity checked))
    <> ":" <> canonicalProgramIdentity program)

canonicalProgramIdentity :: CoreSystemsProgram -> Text
canonicalProgramIdentity = canonicalSemanticForm . coreSystemsProgramSemanticForm

functionSemanticForm :: CoreSystemsFunction -> SemanticForm
functionSemanticForm function = SemanticRecord (Map.fromList
  [ ("key", SemanticAtom (coreFunctionKey function))
  , ("entry", SemanticAtom (coreFunctionEntry function))
  , ("values", SemanticRecord
      (Map.map valueRoleSemanticForm (coreFunctionValues function)))
  , ("blocks", SemanticRecord
      (Map.map blockSemanticForm (coreFunctionBlocks function)))
  ])

valueRoleSemanticForm :: CoreSystemsValueRole -> SemanticForm
valueRoleSemanticForm role = case role of
  CoreOwnedValue storage -> tagged "owned" [SemanticAtom storage]
  CoreBorrowedValue owner -> tagged "borrowed" [SemanticAtom owner]
  CoreInputValue description -> tagged "input" [SemanticAtom description]

blockSemanticForm :: CoreSystemsBlock -> SemanticForm
blockSemanticForm blockValue = SemanticRecord (Map.fromList
  [ ("key", SemanticAtom (coreBlockKey blockValue))
  , ("operations", SemanticOrdered
      (map operationSemanticForm (coreBlockOperations blockValue)))
  , ("terminator", terminatorSemanticForm (coreBlockTerminator blockValue))
  ])

operationSemanticForm :: CoreSystemsOperation -> SemanticForm
operationSemanticForm operation = case operation of
  CoreSystemsTrace label -> tagged "trace" [SemanticAtom label]
  CoreSystemsCall key inputs outputs -> tagged "call"
    [ SemanticAtom key
    , SemanticOrdered (map SemanticAtom inputs)
    , SemanticOrdered (map SemanticAtom outputs)
    ]

terminatorSemanticForm :: CoreSystemsTerminator -> SemanticForm
terminatorSemanticForm terminator = case terminator of
  CoreSystemsJump target -> tagged "jump" [SemanticAtom target]
  CoreSystemsEnd outcome -> tagged "end" [SemanticAtom outcome]
  CoreSystemsChoice key inputs arms -> tagged "choice"
    [ SemanticAtom key
    , SemanticOrdered (map SemanticAtom inputs)
    , SemanticRecord (Map.map SemanticAtom arms)
    ]

realizedOperationSemanticForm :: RealizedOperation -> SemanticForm
realizedOperationSemanticForm realized = SemanticRecord (Map.fromList
  [ ("runtime", SemanticAtom (realizedOperationRuntimeName realized))
  , ("qualification_refs", SemanticUnordered
      (Set.map SemanticAtom (realizedOperationQualificationRefs realized)))
  , ("assumptions", SemanticUnordered
      (Set.map SemanticAtom (realizedOperationAssumptions realized)))
  , ("cost_class", SemanticAtom
      (costClassText (realizedOperationCostClass realized)))
  , ("cost_shape", costShapeSemanticForm (realizedOperationCostShape realized))
  , ("target_preconditions", SemanticOrdered
      (map SemanticAtom (realizedOperationTargetPreconditions realized)))
  , ("derived_obligations", SemanticOrdered
      (map (SemanticAtom . revisionText)
        (realizedOperationDerivedObligations realized)))
  ])

targetChoiceSemanticForm :: RealizedTargetChoice -> SemanticForm
targetChoiceSemanticForm choice = SemanticRecord (Map.fromList
  [ ("decision", SemanticAtom (unDecisionId (realizedTargetDecisionId choice)))
  , ("source", SemanticAtom (realizedTargetSourceRepresentation choice))
  , ("target", SemanticAtom (realizedTargetRepresentation choice))
  , ("entities", SemanticOrdered
      (map SemanticAtom (realizedTargetSemanticEntities choice)))
  , ("action", SemanticAtom (actionText (realizedTargetAction choice)))
  , ("cost_class", SemanticAtom (costClassText (realizedTargetCostClass choice)))
  , ("cost_shape", costShapeSemanticForm (realizedTargetCostShape choice))
  , ("preconditions", SemanticOrdered
      (map SemanticAtom (realizedTargetPreconditions choice)))
  , ("assumptions", SemanticOrdered
      (map SemanticAtom (realizedTargetAssumptions choice)))
  , ("derived", SemanticOrdered
      (map (SemanticAtom . revisionText)
        (realizedTargetDerivedObligations choice)))
  ])

programOperationKeys :: CoreSystemsProgram -> Set Text
programOperationKeys program = Set.fromList
  (concatMap functionKeys (Map.elems (coreProgramFunctions program)))
  where
    functionKeys function =
      concatMap blockKeys (Map.elems (coreFunctionBlocks function))

    blockKeys blockValue =
      [ key | CoreSystemsCall key _ _ <- coreBlockOperations blockValue ]
      <> case coreBlockTerminator blockValue of
          CoreSystemsChoice key _ _ -> [key]
          CoreSystemsJump _ -> []
          CoreSystemsEnd _ -> []

terminatorTargets :: CoreSystemsTerminator -> [Text]
terminatorTargets terminator = case terminator of
  CoreSystemsJump target -> [target]
  CoreSystemsChoice _ _ arms -> Map.elems arms
  CoreSystemsEnd _ -> []

operationDecisionId :: Text -> Text -> Text -> DecisionId
operationDecisionId functionKey blockKey suffix = DecisionId
  ("lower.generic.op:" <> functionKey <> ":" <> blockKey <> ":" <> suffix)

realizedFor
  :: Text
  -> GenericRealizationContext
  -> Either GenericLoweringError RealizedOperation
realizedFor key context = maybe
  (Left (GenericLoweringMissingOperationRealization key))
  Right
  (Map.lookup key (genericContextOperations context))

correspondenceTrace :: CoreSystemsProgram -> [Text]
correspondenceTrace program =
  [ "core-function:" <> coreFunctionKey function <> "->systems-function:"
      <> coreFunctionKey function
  | function <- Map.elems (coreProgramFunctions program)
  ]

phase1FactDisposition :: Set SystemsMechanismKey -> Set Text -> Phase1FactDisposition
phase1FactDisposition mechanisms assumptions
  | Set.null assumptions = Phase1FactRealized mechanisms
  | otherwise = Phase1FactAssumptionDependent assumptions
      (Phase1FactRealized mechanisms)

require :: Bool -> GenericLoweringError -> Either GenericLoweringError ()
require True _ = Right ()
require False err = Left err

tagged :: Text -> [SemanticForm] -> SemanticForm
tagged tag values = SemanticRecord (Map.fromList
  [ ("tag", SemanticAtom tag)
  , ("args", SemanticOrdered values)
  ])

profileText :: CompilationProfile -> Text
profileText profile = case profile of
  CheckedRuntime -> "checked-runtime"
  CertifiedRelease -> "certified-release"

costClassText :: CostClass -> Text
costClassText costClass = case costClass of
  SemanticRequired -> "semantic-required"
  RuntimeAssuranceRequired -> "runtime-assurance-required"
  TargetRequired -> "target-required"
  DefensiveProfile -> "defensive-profile"
  ConservativeLowering -> "conservative-lowering"

actionText :: LoweringAction -> Text
actionText action = case action of
  Retain -> "retain"
  Materialize -> "materialize"
  Erase -> "erase"
  Fuse -> "fuse"
  Specialize -> "specialize"
  Copy -> "copy"
  Borrow -> "borrow"
  ChooseLayout -> "choose-layout"
  InsertCheck -> "insert-check"
  RemoveCheck -> "remove-check"
  RepresentAsControlFlow -> "represent-as-control-flow"
  Cleanup -> "cleanup"

costShapeSemanticForm :: CostShape -> SemanticForm
costShapeSemanticForm shape = SemanticRecord (Map.fromList
  [ ("compile_time", maybeAtom (costCompileTime shape))
  , ("code_size", maybeAtom (costCodeSize shape))
  , ("allocation_count", maybeAtom (costAllocationCount shape))
  , ("peak_live_memory", maybeAtom (costPeakLiveMemory shape))
  , ("bytes_copied", maybeAtom (costBytesCopied shape))
  , ("dynamic_check_count", maybeAtom (costDynamicCheckCount shape))
  , ("branch_or_dispatch", maybeAtom (costBranchOrDispatch shape))
  , ("hash_or_crypto_work", maybeAtom (costHashOrCryptoWork shape))
  , ("synchronization", maybeAtom (costSynchronization shape))
  , ("frequency", maybeAtom (costFrequency shape))
  ])
  where
    maybeAtom = SemanticAtom . maybe "" id

revisionText :: RevisionId -> Text
revisionText = unRevisionId