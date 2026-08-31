{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.GenericLowering
  ( CoreSystemsValueRole (..)
  , CoreSystemsValue (..)
  , CoreSystemsOperation (..)
  , CoreSystemsTerminator (..)
  , CoreSystemsBlock (..)
  , CoreSystemsFunction (..)
  , CoreSystemsProgram (..)
  , GenericDecisionSpec (..)
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
import Phil.Assurance.Types
  ( AssuranceUseId
  , Digest
  , RevisionId
  , digestText
  )
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

-- | Target-abstract checked-Core storage/value roles.  These are semantic roles,
-- not concrete ABI/layout choices.
data CoreSystemsValueRole
  = CoreTransportHandle
  | CorePendingIngress Text
  | CoreFrameOwner Text
  | CoreOwnedBuffer Text
  | CoreBorrowedValue Text
  | CoreRuntimeScalar Text
  | CoreRuntimeInput Text
  deriving (Eq, Ord, Show)

data CoreSystemsValue = CoreSystemsValue
  { coreValueKey :: Text
  , coreValueRole :: CoreSystemsValueRole
  , coreValueStorageIdentity :: Maybe Text
  }
  deriving (Eq, Ord, Show)

-- | Checked-Core operations retain semantic control/resource structure while
-- referring to realization decisions only by witness-neutral keys.
data CoreSystemsOperation
  = CoreReceiveFrame Text Text Text Text Text
  | CoreBorrowView Text Text Text
  | CoreCommitIngress Text Text Text
  | CoreDestroyPending Text Text Text
  | CoreReleaseOwner Text Text
  | CoreCleanupPartial Text Text
  | CoreRuntimeCall Text Text [Text] [Text] (Maybe Text)
  | CoreEraseFact Text RevisionId AssuranceUseId
  | CoreTrace Text
  deriving (Eq, Ord, Show)

-- | Terminator runtime sites are realization-context references.  Source control
-- flow and source-visible operation names remain in checked Core.
data CoreSystemsTerminator
  = CoreSystemsJump Text
  | CoreSystemsBranch Text Text Text
  | CoreSystemsRecognize Text Text Text Text Text
  | CoreSystemsRuntimeCheck Text [Text] Text Text
  | CoreSystemsReceiveExact Text Text Text Text Text Text
  | CoreSystemsStore Text Text Text Text Text
  | CoreSystemsRuntimeChoice Text [Text] (Maybe Text) (Map Text Text)
  | CoreSystemsEnd Text
  | CoreSystemsFatal Text
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
  , coreFunctionValues :: Map Text CoreSystemsValue
  , coreFunctionBlocks :: Map Text CoreSystemsBlock
  }
  deriving (Eq, Ord, Show)

-- | Presentation is deliberately absent from semantic identity.  Source facts
-- retain their exact obligation revision where one exists, because later runtime
-- claim binding is revision-indexed.
data CoreSystemsProgram = CoreSystemsProgram
  { coreProgramLabel :: Text
  , coreProgramProfile :: CompilationProfile
  , coreProgramFunctions :: Map Text CoreSystemsFunction
  , coreProgramFacts :: Map Text (Maybe RevisionId)
  }
  deriving (Eq, Show)

-- | Explicit lowering/realization choice.  The producer seals source/target
-- digests itself, so callers cannot smuggle a pre-built Systems artifact through
-- this structure.
data GenericDecisionSpec = GenericDecisionSpec
  { genericDecisionId :: DecisionId
  , genericDecisionSourceRepresentation :: Text
  , genericDecisionTargetRepresentation :: Text
  , genericDecisionSemanticEntities :: [Text]
  , genericDecisionAction :: LoweringAction
  , genericDecisionCostClass :: Maybe CostClass
  , genericDecisionCostShape :: CostShape
  , genericDecisionTargetPreconditions :: [Text]
  , genericDecisionAssumptions :: [Text]
  , genericDecisionDerivedObligations :: [RevisionId]
  }
  deriving (Eq, Ord, Show)

-- | ADR-020 realization input.  There is no program/witness discriminator.
-- Runtime-site evidence, lowering decisions, qualifications, assumptions, and
-- target choices are explicit data. Runtime-site map keys are exact source fact
-- keys: this lets the producer retain the right fact without guessing from a
-- revision that may also index an erased or transferred representation.
data GenericRealizationContext = GenericRealizationContext
  { genericContextRevision :: Text
  , genericContextSemantics :: SemanticForm
  , genericContextVerifierProfile :: Text
  , genericContextRealizationRefs :: Set Text
  , genericContextQualificationRefs :: Set Text
  , genericContextAssumptions :: Set Text
  , genericContextDecisions :: Map Text GenericDecisionSpec
  , genericContextRuntimeSites :: Map Text RuntimeSiteRef
  }
  deriving (Eq, Show)

data GenericLoweringError
  = GenericLoweringEmptyVerifierProfile
  | GenericLoweringEmptyContextRevision
  | GenericLoweringEmptyRealizationRefs
  | GenericLoweringEmptyFacts
  | GenericLoweringEmptyFunctions
  | GenericLoweringFunctionKeyMismatch Text Text
  | GenericLoweringValueKeyMismatch Text Text Text
  | GenericLoweringMissingEntry Text Text
  | GenericLoweringBlockKeyMismatch Text Text Text
  | GenericLoweringUnknownBlockTarget Text Text Text
  | GenericLoweringUnknownValue Text Text Text
  | GenericLoweringMissingDecision Text
  | GenericLoweringMissingRuntimeSite Text
  | GenericLoweringUnknownRuntimeFact Text
  | GenericLoweringRuntimeFactMissingRevision Text
  | GenericLoweringRuntimeFactRevisionMismatch Text RevisionId RevisionId
  | GenericLoweringDuplicateDecision DecisionId
  | GenericLoweringStageRejected Phase1StageVerificationError
  deriving (Eq, Show)

coreSystemsProgramSemanticForm :: CoreSystemsProgram -> SemanticForm
coreSystemsProgramSemanticForm program = SemanticRecord (Map.fromList
  [ ("profile", SemanticAtom (profileText (coreProgramProfile program)))
  , ("facts", SemanticRecord
      (Map.map factRevisionSemanticForm (coreProgramFacts program)))
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
  decisions <- lowerDecisionLedger sourceDigest targetDigest context
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
      decisionAssumptions = Set.fromList
        (concatMap genericDecisionAssumptions
          (Map.elems (genericContextDecisions context)))
      assumptions = Set.union
        (genericContextAssumptions context)
        decisionAssumptions
      facts = collectSourceFacts artifact
      mechanisms = collectSystemsMechanisms artifact
      dispositions = Map.fromSet
        (const (phase1FactDisposition mechanisms assumptions)) facts
      justifications = Map.fromSet
        (const SystemsJustification
          { systemsJustificationSourceFacts = facts
          , systemsJustificationRealizationRefs =
              genericContextRealizationRefs context
          , systemsJustificationQualificationRefs =
              genericContextQualificationRefs context
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
  require (not (Map.null (coreProgramFacts program)))
    GenericLoweringEmptyFacts
  require (not (Map.null (coreProgramFunctions program)))
    GenericLoweringEmptyFunctions
  mapM_ (validateRuntimeFact program)
    (Map.toAscList (genericContextRuntimeSites context))
  mapM_ (validateFunction context) (Map.toAscList (coreProgramFunctions program))

validateRuntimeFact
  :: CoreSystemsProgram
  -> (Text, RuntimeSiteRef)
  -> Either GenericLoweringError ()
validateRuntimeFact program (factKey, site) =
  case Map.lookup factKey (coreProgramFacts program) of
    Nothing -> Left (GenericLoweringUnknownRuntimeFact factKey)
    Just Nothing -> Left (GenericLoweringRuntimeFactMissingRevision factKey)
    Just (Just expectedRevision) ->
      require (expectedRevision == runtimeSiteRevision site)
        (GenericLoweringRuntimeFactRevisionMismatch
          factKey expectedRevision (runtimeSiteRevision site))

validateFunction
  :: GenericRealizationContext
  -> (Text, CoreSystemsFunction)
  -> Either GenericLoweringError ()
validateFunction context (functionMapKey, function) = do
  require (functionMapKey == coreFunctionKey function)
    (GenericLoweringFunctionKeyMismatch functionMapKey (coreFunctionKey function))
  require (Map.member (coreFunctionEntry function) blocks)
    (GenericLoweringMissingEntry functionMapKey (coreFunctionEntry function))
  mapM_ validateValueEntry (Map.toAscList values)
  mapM_ validateRole (Map.elems values)
  mapM_ validateBlock (Map.toAscList blocks)
  where
    values = coreFunctionValues function
    blocks = coreFunctionBlocks function

    validateValueEntry (valueMapKey, value) =
      require (valueMapKey == coreValueKey value)
        (GenericLoweringValueKeyMismatch functionMapKey valueMapKey (coreValueKey value))

    validateRole value = case coreValueRole value of
      CoreBorrowedValue owner -> validateValue owner
      _ -> Right ()

    validateBlock (blockMapKey, blockValue) = do
      require (blockMapKey == coreBlockKey blockValue)
        (GenericLoweringBlockKeyMismatch functionMapKey blockMapKey
          (coreBlockKey blockValue))
      mapM_ validateOperation (coreBlockOperations blockValue)
      validateTerminator (coreBlockTerminator blockValue)
      mapM_ validateTarget (terminatorTargets (coreBlockTerminator blockValue))

    validateOperation operation = case operation of
      CoreReceiveFrame decision pending frame transport _ -> do
        validateDecision decision
        mapM_ validateValue [pending, frame, transport]
      CoreBorrowView decision view owner -> do
        validateDecision decision
        mapM_ validateValue [view, owner]
      CoreCommitIngress decision pending transport -> do
        validateDecision decision
        mapM_ validateValue [pending, transport]
      CoreDestroyPending decision pending frame -> do
        validateDecision decision
        mapM_ validateValue [pending, frame]
      CoreReleaseOwner decision owner -> do
        validateDecision decision
        validateValue owner
      CoreCleanupPartial decision owner -> do
        validateDecision decision
        validateValue owner
      CoreRuntimeCall decision _ inputs outputs site -> do
        validateDecision decision
        mapM_ validateValue (inputs <> outputs)
        mapM_ validateSite site
      CoreEraseFact decision _ _ -> validateDecision decision
      CoreTrace _ -> Right ()

    validateTerminator terminator = case terminator of
      CoreSystemsJump _ -> Right ()
      CoreSystemsBranch value _ _ -> validateValue value
      CoreSystemsRecognize site pending raw _ _ -> do
        validateSite site
        mapM_ validateValue [pending, raw]
      CoreSystemsRuntimeCheck site inputs _ _ -> do
        validateSite site
        mapM_ validateValue inputs
      CoreSystemsReceiveExact site transport lengthValue owner _ _ -> do
        validateSite site
        mapM_ validateValue [transport, lengthValue, owner]
      CoreSystemsStore site owner result _ _ -> do
        validateSite site
        mapM_ validateValue [owner, result]
      CoreSystemsRuntimeChoice _ inputs site _ -> do
        mapM_ validateValue inputs
        mapM_ validateSite site
      CoreSystemsEnd _ -> Right ()
      CoreSystemsFatal _ -> Right ()

    validateDecision key =
      require (Map.member key (genericContextDecisions context))
        (GenericLoweringMissingDecision key)

    validateSite key =
      require (Map.member key (genericContextRuntimeSites context))
        (GenericLoweringMissingRuntimeSite key)

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
      blocksByText <- Map.traverseWithKey (lowerBlock function)
        (coreFunctionBlocks function)
      let blocks = Map.mapKeys BlockId blocksByText
      pure SystemsFunction
        { systemsFunctionName = coreFunctionKey function
        , systemsFunctionEntry = BlockId (coreFunctionEntry function)
        , systemsFunctionValues = Map.fromList
            [ (ValueId key, lowerValue value)
            | (key, value) <- Map.toAscList (coreFunctionValues function)
            ]
        , systemsFunctionBlocks = blocks
        }

    lowerBlock _ _ blockValue = do
      operations <- mapM lowerOperation (coreBlockOperations blockValue)
      terminator <- lowerTerminator (coreBlockTerminator blockValue)
      pure SystemsBlock
        { systemsBlockId = BlockId (coreBlockKey blockValue)
        , systemsBlockOps = operations
        , systemsBlockTerminator = terminator
        }

    lowerOperation operation = case operation of
      CoreReceiveFrame decision pending frame transport grammar ->
        OpReceiveFrame
          (ValueId pending) (ValueId frame) (ValueId transport) grammar
          <$> decisionIdFor decision context
      CoreBorrowView decision view owner ->
        OpBorrowView (ValueId view) (ValueId owner)
          <$> decisionIdFor decision context
      CoreCommitIngress decision pending transport ->
        OpCommitIngress (ValueId pending) (ValueId transport)
          <$> decisionIdFor decision context
      CoreDestroyPending decision pending frame ->
        OpDestroyPending (ValueId pending) (ValueId frame)
          <$> decisionIdFor decision context
      CoreReleaseOwner decision owner ->
        OpReleaseOwner (ValueId owner) <$> decisionIdFor decision context
      CoreCleanupPartial decision owner ->
        OpCleanupPartial (ValueId owner) <$> decisionIdFor decision context
      CoreRuntimeCall decision name inputs outputs siteKey -> do
        decisionId <- decisionIdFor decision context
        site <- optionalSiteFor siteKey context
        pure OpRuntimeCall
          { runtimeCallName = name
          , runtimeCallInputs = map ValueId inputs
          , runtimeCallOutputs = map ValueId outputs
          , runtimeCallSite = site
          , runtimeCallDecision = decisionId
          }
      CoreEraseFact decision revision use ->
        OpEraseFact revision use <$> decisionIdFor decision context
      CoreTrace label -> Right (OpTraceEvent label)

    lowerTerminator terminator = case terminator of
      CoreSystemsJump target -> Right (TermJump (BlockId target))
      CoreSystemsBranch value yes no ->
        Right (TermBranch (ValueId value) (BlockId yes) (BlockId no))
      CoreSystemsRecognize siteKey pending raw success failure -> do
        site <- siteFor siteKey context
        pure TermRecognize
          { recognizePending = ValueId pending
          , recognizeRawView = ValueId raw
          , recognizeSite = site
          , recognizeSuccess = BlockId success
          , recognizeFailure = BlockId failure
          }
      CoreSystemsRuntimeCheck siteKey inputs success failure -> do
        site <- siteFor siteKey context
        pure TermRuntimeCheck
          { checkInputs = map ValueId inputs
          , checkSite = site
          , checkSuccess = BlockId success
          , checkFailure = BlockId failure
          }
      CoreSystemsReceiveExact siteKey transport lengthValue owner success failure -> do
        site <- siteFor siteKey context
        pure TermReceiveExact
          { exactTransport = ValueId transport
          , exactLength = ValueId lengthValue
          , exactPayloadOwner = ValueId owner
          , exactSite = site
          , exactSuccess = BlockId success
          , exactFailure = BlockId failure
          }
      CoreSystemsStore siteKey owner result success failure -> do
        site <- siteFor siteKey context
        pure TermStore
          { storeOwner = ValueId owner
          , storeResult = ValueId result
          , storeSite = site
          , storeSuccess = BlockId success
          , storeFailure = BlockId failure
          }
      CoreSystemsRuntimeChoice name inputs siteKey arms -> do
        site <- optionalSiteFor siteKey context
        pure TermRuntimeChoice
          { runtimeChoiceName = name
          , runtimeChoiceInputs = map ValueId inputs
          , runtimeChoiceSite = site
          , runtimeChoiceArms = Map.map
              (SystemsRuntimeChoiceArm Nothing . BlockId) arms
          }
      CoreSystemsEnd outcome -> Right (TermEnd outcome)
      CoreSystemsFatal detail -> Right (TermFatal detail)

lowerValue :: CoreSystemsValue -> SystemsValue
lowerValue value = SystemsValue
  { systemsValueId = ValueId (coreValueKey value)
  , systemsValueRole = case coreValueRole value of
      CoreTransportHandle -> TransportHandle
      CorePendingIngress grammar -> PendingIngress grammar
      CoreFrameOwner grammar -> FrameOwner grammar
      CoreOwnedBuffer semanticType -> OwnedBuffer semanticType
      CoreBorrowedValue owner -> BorrowedSlice (ValueId owner)
      CoreRuntimeScalar scalarType -> RuntimeScalar scalarType
      CoreRuntimeInput inputType -> RuntimeInput inputType
  , systemsStorageIdentity = coreValueStorageIdentity value
  }

lowerDecisionLedger
  :: Digest
  -> Digest
  -> GenericRealizationContext
  -> Either GenericLoweringError (Map DecisionId LoweringDecision)
lowerDecisionLedger sourceDigest targetDigest context =
  go Map.empty (Map.elems (genericContextDecisions context))
  where
    go result [] = Right result
    go result (spec : rest)
      | Map.member (genericDecisionId spec) result =
          Left (GenericLoweringDuplicateDecision (genericDecisionId spec))
      | otherwise = go
          (Map.insert (genericDecisionId spec)
            (renderDecision sourceDigest targetDigest spec) result)
          rest

renderDecision :: Digest -> Digest -> GenericDecisionSpec -> LoweringDecision
renderDecision sourceDigest targetDigest spec =
  provisional { loweringDecisionDigest = deriveLoweringDecisionDigest provisional }
  where
    provisional = LoweringDecision
      { loweringDecisionId = genericDecisionId spec
      , loweringDecisionDigest = digestText "pending"
      , loweringSourceArtifactDigest = sourceDigest
      , loweringTargetArtifactDigest = targetDigest
      , loweringSourceRepresentation = genericDecisionSourceRepresentation spec
      , loweringTargetRepresentation = genericDecisionTargetRepresentation spec
      , loweringSemanticEntities = genericDecisionSemanticEntities spec
      , loweringObligationRevisions = []
      , loweringAssuranceEntries = []
      , loweringAssuranceUses = []
      , loweringAction = genericDecisionAction spec
      , loweringRepresentationBefore = genericDecisionSourceRepresentation spec
      , loweringRepresentationAfter = genericDecisionTargetRepresentation spec
      , loweringInvariantsPreserved = []
      , loweringInvariantsTransferred = []
      , loweringRuntimeResidue = []
      , loweringCostClass = genericDecisionCostClass spec
      , loweringCostShape = genericDecisionCostShape spec
      , loweringTargetPreconditions = genericDecisionTargetPreconditions spec
      , loweringAssumptions = genericDecisionAssumptions spec
      , loweringDerivedObligations = genericDecisionDerivedObligations spec
      , loweringInspectionPlan = []
      }

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
            , factSourceRevision = revision
            , factDisposition = case Map.lookup fact runtimeFacts of
                Just site -> FactRuntimeRetained (runtimeSiteEvidence site)
                Nothing -> FactConsumed
                  "preserved by generic checked-Core to Systems accounting"
            }
        | (fact, revision) <- Map.toAscList (coreProgramFacts program)
        ]
    , stageInvariants = Map.empty
    , stageRequiredEdges = []
    , stageDerivedObligations = Set.toAscList (Set.fromList
        (concatMap loweringDerivedObligations (Map.elems decisions)))
    , stageAssumptions = Set.toAscList (Set.unions
        [ genericContextAssumptions context
        , Set.fromList
            (concatMap loweringAssumptions (Map.elems decisions))
        ])
    , stageTraceRelation =
        [ "architecture-instance="
            <> unInstanceRevision
              (identityInstanceRevision (checkedArchitectureIdentity checked))
        ]
        <> correspondenceTrace program
    , stageResourceFailureRelation =
        [ "checked Core resource/failure structure is lowered constructor-for-constructor; realization metadata may not silently remove it"
        ]
    }
  where
    runtimeFacts = genericContextRuntimeSites context

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
  , ("decisions", SemanticRecord
      (Map.map decisionSemanticForm (genericContextDecisions context)))
  , ("runtime_sites", SemanticRecord
      (Map.map runtimeSiteSemanticForm (genericContextRuntimeSites context)))
  , ("verifier_profile", SemanticAtom (genericContextVerifierProfile context))
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
      (Map.map valueSemanticForm (coreFunctionValues function)))
  , ("blocks", SemanticRecord
      (Map.map blockSemanticForm (coreFunctionBlocks function)))
  ])

valueSemanticForm :: CoreSystemsValue -> SemanticForm
valueSemanticForm value = SemanticRecord (Map.fromList
  [ ("key", SemanticAtom (coreValueKey value))
  , ("role", valueRoleSemanticForm (coreValueRole value))
  , ("storage", SemanticAtom (maybe "" id (coreValueStorageIdentity value)))
  ])

valueRoleSemanticForm :: CoreSystemsValueRole -> SemanticForm
valueRoleSemanticForm role = case role of
  CoreTransportHandle -> tagged "transport" []
  CorePendingIngress grammar -> tagged "pending-ingress" [SemanticAtom grammar]
  CoreFrameOwner grammar -> tagged "frame-owner" [SemanticAtom grammar]
  CoreOwnedBuffer semanticType -> tagged "owned-buffer" [SemanticAtom semanticType]
  CoreBorrowedValue owner -> tagged "borrowed" [SemanticAtom owner]
  CoreRuntimeScalar scalarType -> tagged "runtime-scalar" [SemanticAtom scalarType]
  CoreRuntimeInput inputType -> tagged "runtime-input" [SemanticAtom inputType]

blockSemanticForm :: CoreSystemsBlock -> SemanticForm
blockSemanticForm blockValue = SemanticRecord (Map.fromList
  [ ("key", SemanticAtom (coreBlockKey blockValue))
  , ("operations", SemanticOrdered
      (map operationSemanticForm (coreBlockOperations blockValue)))
  , ("terminator", terminatorSemanticForm (coreBlockTerminator blockValue))
  ])

-- Realization decision/site keys are intentionally omitted from checked-Core
-- semantic identity.  They are represented in realizationSemanticForm instead.
operationSemanticForm :: CoreSystemsOperation -> SemanticForm
operationSemanticForm operation = case operation of
  CoreReceiveFrame _ pending frame transport grammar -> tagged "receive-frame"
    (map SemanticAtom [pending, frame, transport, grammar])
  CoreBorrowView _ view owner -> tagged "borrow-view"
    (map SemanticAtom [view, owner])
  CoreCommitIngress _ pending transport -> tagged "commit-ingress"
    (map SemanticAtom [pending, transport])
  CoreDestroyPending _ pending frame -> tagged "destroy-pending"
    (map SemanticAtom [pending, frame])
  CoreReleaseOwner _ owner -> tagged "release-owner" [SemanticAtom owner]
  CoreCleanupPartial _ owner -> tagged "cleanup-partial" [SemanticAtom owner]
  CoreRuntimeCall _ name inputs outputs _ -> tagged "runtime-call"
    [ SemanticAtom name
    , SemanticOrdered (map SemanticAtom inputs)
    , SemanticOrdered (map SemanticAtom outputs)
    ]
  CoreEraseFact _ revision _ -> tagged "erase-fact"
    [SemanticAtom (showText revision)]
  CoreTrace label -> tagged "trace" [SemanticAtom label]

terminatorSemanticForm :: CoreSystemsTerminator -> SemanticForm
terminatorSemanticForm terminator = case terminator of
  CoreSystemsJump target -> tagged "jump" [SemanticAtom target]
  CoreSystemsBranch value yes no -> tagged "branch"
    (map SemanticAtom [value, yes, no])
  CoreSystemsRecognize _ pending raw success failure -> tagged "recognize"
    (map SemanticAtom [pending, raw, success, failure])
  CoreSystemsRuntimeCheck _ inputs success failure -> tagged "runtime-check"
    [ SemanticOrdered (map SemanticAtom inputs)
    , SemanticAtom success
    , SemanticAtom failure
    ]
  CoreSystemsReceiveExact _ transport lengthValue owner success failure ->
    tagged "receive-exact" (map SemanticAtom
      [transport, lengthValue, owner, success, failure])
  CoreSystemsStore _ owner result success failure -> tagged "store"
    (map SemanticAtom [owner, result, success, failure])
  CoreSystemsRuntimeChoice name inputs _ arms -> tagged "runtime-choice"
    [ SemanticAtom name
    , SemanticOrdered (map SemanticAtom inputs)
    , SemanticRecord (Map.map SemanticAtom arms)
    ]
  CoreSystemsEnd outcome -> tagged "end" [SemanticAtom outcome]
  CoreSystemsFatal detail -> tagged "fatal" [SemanticAtom detail]

factRevisionSemanticForm :: Maybe RevisionId -> SemanticForm
factRevisionSemanticForm revision = SemanticAtom (maybe "" showText revision)

decisionSemanticForm :: GenericDecisionSpec -> SemanticForm
decisionSemanticForm spec = SemanticRecord (Map.fromList
  [ ("id", SemanticAtom (unDecisionId (genericDecisionId spec)))
  , ("source", SemanticAtom (genericDecisionSourceRepresentation spec))
  , ("target", SemanticAtom (genericDecisionTargetRepresentation spec))
  , ("entities", SemanticOrdered
      (map SemanticAtom (genericDecisionSemanticEntities spec)))
  , ("action", SemanticAtom (showText (genericDecisionAction spec)))
  , ("cost_class", SemanticAtom (maybe "" showText (genericDecisionCostClass spec)))
  , ("cost_shape", SemanticAtom (showText (genericDecisionCostShape spec)))
  , ("preconditions", SemanticOrdered
      (map SemanticAtom (genericDecisionTargetPreconditions spec)))
  , ("assumptions", SemanticOrdered
      (map SemanticAtom (genericDecisionAssumptions spec)))
  , ("derived", SemanticOrdered
      (map (SemanticAtom . showText) (genericDecisionDerivedObligations spec)))
  ])

runtimeSiteSemanticForm :: RuntimeSiteRef -> SemanticForm
runtimeSiteSemanticForm site = SemanticRecord (Map.fromList
  [ ("kind", SemanticAtom (showText (runtimeSiteKind site)))
  , ("revision", SemanticAtom (showText (runtimeSiteRevision site)))
  , ("evidence", SemanticAtom (showText (runtimeSiteEvidence site)))
  , ("cost", SemanticAtom (runtimeSiteCostRef site))
  ])

terminatorTargets :: CoreSystemsTerminator -> [Text]
terminatorTargets terminator = case terminator of
  CoreSystemsJump target -> [target]
  CoreSystemsBranch _ yes no -> [yes, no]
  CoreSystemsRecognize _ _ _ success failure -> [success, failure]
  CoreSystemsRuntimeCheck _ _ success failure -> [success, failure]
  CoreSystemsReceiveExact _ _ _ _ success failure -> [success, failure]
  CoreSystemsStore _ _ _ success failure -> [success, failure]
  CoreSystemsRuntimeChoice _ _ _ arms -> Map.elems arms
  CoreSystemsEnd _ -> []
  CoreSystemsFatal _ -> []

decisionIdFor
  :: Text
  -> GenericRealizationContext
  -> Either GenericLoweringError DecisionId
decisionIdFor key context = maybe
  (Left (GenericLoweringMissingDecision key))
  (Right . genericDecisionId)
  (Map.lookup key (genericContextDecisions context))

siteFor
  :: Text
  -> GenericRealizationContext
  -> Either GenericLoweringError RuntimeSiteRef
siteFor key context = maybe
  (Left (GenericLoweringMissingRuntimeSite key))
  Right
  (Map.lookup key (genericContextRuntimeSites context))

optionalSiteFor
  :: Maybe Text
  -> GenericRealizationContext
  -> Either GenericLoweringError (Maybe RuntimeSiteRef)
optionalSiteFor Nothing _ = Right Nothing
optionalSiteFor (Just key) context = Just <$> siteFor key context

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

showText :: Show a => a -> Text
showText = Text.pack . show
