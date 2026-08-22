{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.IR
  ( CompilationProfile (..)
  , ValueId (..)
  , BlockId (..)
  , DecisionId (..)
  , InvariantId (..)
  , ScalarType (..)
  , ScalarLiteral (..)
  , SystemsValueRole (..)
  , SystemsValue (..)
  , RuntimeSiteKind (..)
  , RuntimeSiteRef (..)
  , SystemsOp (..)
  , SystemsChoiceArm (..)
  , SystemsRuntimeChoiceArm (..)
  , SystemsTerminator (..)
  , SystemsBlock (..)
  , SystemsFunction (..)
  , CostClass (..)
  , CostShape (..)
  , LoweringAction (..)
  , LoweringDecision (..)
  , FactDisposition (..)
  , FactTransfer (..)
  , RequiredControlEdge (..)
  , InvariantClaim (..)
  , StageInvariant (..)
  , StageContract (..)
  , SystemsProgram (..)
  , LoweringLedger (..)
  , SystemsArtifact (..)
  , emptyCostShape
  , deriveLoweringDecisionDigest
  , deriveLoweringLedgerRoot
  , systemsProgramDigest
  , stageContractDigest
  , systemsArtifactDigest
  , blockSuccessors
  , runtimeSites
  ) where

import Data.List (sort)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types
  ( AssuranceUseId (..)
  , Digest (..)
  , EvidenceEntryId (..)
  , RevisionId (..)
  , digestText
  )
import Phil.Core.Scalar
  ( ScalarLiteral (..)
  , ScalarType (..)
  , renderScalarLiteral
  , renderScalarType
  )

newtype ValueId = ValueId { unValueId :: Text }
  deriving (Eq, Ord, Show)

newtype BlockId = BlockId { unBlockId :: Text }
  deriving (Eq, Ord, Show)

newtype DecisionId = DecisionId { unDecisionId :: Text }
  deriving (Eq, Ord, Show)

newtype InvariantId = InvariantId { unInvariantId :: Text }
  deriving (Eq, Ord, Show)

data CompilationProfile
  = CheckedRuntime
  | CertifiedRelease
  deriving (Eq, Ord, Show)

data SystemsValueRole
  = TransportHandle
  | PendingIngress Text
  | FrameOwner Text
  | OwnedBuffer Text
  | BorrowedSlice ValueId
  | RuntimeScalar Text
  | TypedScalar ScalarType
  | RuntimeRecord Text
  | DiagnosticState Text
  deriving (Eq, Ord, Show)

data SystemsValue = SystemsValue
  { systemsValueId :: ValueId
  , systemsValueRole :: SystemsValueRole
  , systemsStorageIdentity :: Maybe Text
  }
  deriving (Eq, Ord, Show)

data RuntimeSiteKind
  = RecognitionBoundary Text
  | ValidationBoundary Text
  | BranchRefinementBoundary Text
  | ExactReceiveBoundary
  | ExactSendBoundary
  | DigestBoundary
  | StorageBoundary
  | SourceSemanticRuntime Text
  deriving (Eq, Ord, Show)

data RuntimeSiteRef = RuntimeSiteRef
  { runtimeSiteKind :: RuntimeSiteKind
  , runtimeSiteRevision :: RevisionId
  , runtimeSiteEvidence :: EvidenceEntryId
  , runtimeSiteCostRef :: Text
  }
  deriving (Eq, Ord, Show)

data SystemsOp
  = OpReceiveFrame
      { receivePending :: ValueId
      , receiveFrameOwner :: ValueId
      , receiveTransport :: ValueId
      , receiveGrammar :: Text
      , receiveDecision :: DecisionId
      }
  | OpBorrowView
      { borrowView :: ValueId
      , borrowOwner :: ValueId
      , borrowDecision :: DecisionId
      }
  | OpCommitIngress
      { commitPending :: ValueId
      , commitTransport :: ValueId
      , commitDecision :: DecisionId
      }
  | OpDestroyPending
      { destroyPending :: ValueId
      , destroyFrameOwner :: ValueId
      , destroyDecision :: DecisionId
      }
  | OpReleaseOwner
      { releaseOwner :: ValueId
      , releaseDecision :: DecisionId
      }
  | OpCleanupPartial
      { cleanupOwner :: ValueId
      , cleanupDecision :: DecisionId
      }
  | OpRuntimeCall
      { runtimeCallName :: Text
      , runtimeCallInputs :: [ValueId]
      , runtimeCallOutputs :: [ValueId]
      , runtimeCallSite :: Maybe RuntimeSiteRef
      , runtimeCallDecision :: DecisionId
      }
  | OpSessionSelect
      { sessionSelectTransport :: ValueId
      , sessionSelectLabel :: Text
      , sessionSelectPayload :: Maybe ValueId
      , sessionSelectDecision :: DecisionId
      }
  | OpCopy
      { copySource :: ValueId
      , copyTarget :: ValueId
      , copyDecision :: DecisionId
      }
  | OpEraseFact
      { erasedRevision :: RevisionId
      , erasedByUse :: AssuranceUseId
      , eraseDecision :: DecisionId
      }
  | OpDiagnostic
      { diagnosticName :: Text
      , diagnosticDecision :: DecisionId
      }
  | OpScalarLiteral
      { scalarLiteralOutput :: ValueId
      , scalarLiteralValue :: ScalarLiteral
      }
  | OpTraceEvent Text
  deriving (Eq, Ord, Show)

data SystemsChoiceArm = SystemsChoiceArm
  { choiceArmPayloadBinding :: Maybe ValueId
  , choiceArmTarget :: BlockId
  }
  deriving (Eq, Ord, Show)

data SystemsRuntimeChoiceArm = SystemsRuntimeChoiceArm
  { runtimeChoiceArmPayloadBinding :: Maybe ValueId
  , runtimeChoiceArmTarget :: BlockId
  }
  deriving (Eq, Ord, Show)

data SystemsTerminator
  = TermJump BlockId
  | TermBranch ValueId BlockId BlockId
  | TermRecognize
      { recognizePending :: ValueId
      , recognizeRawView :: ValueId
      , recognizeSite :: RuntimeSiteRef
      , recognizeSuccess :: BlockId
      , recognizeFailure :: BlockId
      }
  | TermRuntimeCheck
      { checkInputs :: [ValueId]
      , checkSite :: RuntimeSiteRef
      , checkSuccess :: BlockId
      , checkFailure :: BlockId
      }
  | TermReceiveExact
      { exactTransport :: ValueId
      , exactLength :: ValueId
      , exactPayloadOwner :: ValueId
      , exactSite :: RuntimeSiteRef
      , exactSuccess :: BlockId
      , exactFailure :: BlockId
      }
  | TermSendExact
      { sendExactTransport :: ValueId
      , sendExactOwner :: ValueId
      , sendExactSite :: RuntimeSiteRef
      , sendExactSuccess :: BlockId
      , sendExactFailure :: BlockId
      }
  | TermStore
      { storeOwner :: ValueId
      , storeResult :: ValueId
      , storeSite :: RuntimeSiteRef
      , storeSuccess :: BlockId
      , storeFailure :: BlockId
      }
  | TermSessionOffer
      { sessionOfferTransport :: ValueId
      , sessionOfferArms :: Map Text SystemsChoiceArm
      }
  | TermRuntimeChoice
      { runtimeChoiceName :: Text
      , runtimeChoiceInputs :: [ValueId]
      , runtimeChoiceSite :: Maybe RuntimeSiteRef
      , runtimeChoiceArms :: Map Text SystemsRuntimeChoiceArm
      }
  | TermReturnScalar ValueId
  | TermEnd Text
  | TermFatal Text
  deriving (Eq, Ord, Show)

data SystemsBlock = SystemsBlock
  { systemsBlockId :: BlockId
  , systemsBlockOps :: [SystemsOp]
  , systemsBlockTerminator :: SystemsTerminator
  }
  deriving (Eq, Ord, Show)

data SystemsFunction = SystemsFunction
  { systemsFunctionName :: Text
  , systemsFunctionEntry :: BlockId
  , systemsFunctionValues :: Map ValueId SystemsValue
  , systemsFunctionBlocks :: Map BlockId SystemsBlock
  }
  deriving (Eq, Show)

data CostClass
  = SemanticRequired
  | RuntimeAssuranceRequired
  | TargetRequired
  | DefensiveProfile
  | ConservativeLowering
  deriving (Eq, Ord, Show)

data CostShape = CostShape
  { costCompileTime :: Maybe Text
  , costCodeSize :: Maybe Text
  , costAllocationCount :: Maybe Text
  , costPeakLiveMemory :: Maybe Text
  , costBytesCopied :: Maybe Text
  , costDynamicCheckCount :: Maybe Text
  , costBranchOrDispatch :: Maybe Text
  , costHashOrCryptoWork :: Maybe Text
  , costSynchronization :: Maybe Text
  , costFrequency :: Maybe Text
  }
  deriving (Eq, Ord, Show)

emptyCostShape :: CostShape
emptyCostShape = CostShape
  { costCompileTime = Nothing
  , costCodeSize = Nothing
  , costAllocationCount = Nothing
  , costPeakLiveMemory = Nothing
  , costBytesCopied = Nothing
  , costDynamicCheckCount = Nothing
  , costBranchOrDispatch = Nothing
  , costHashOrCryptoWork = Nothing
  , costSynchronization = Nothing
  , costFrequency = Nothing
  }

data LoweringAction
  = Retain
  | Materialize
  | Erase
  | Fuse
  | Specialize
  | Copy
  | Borrow
  | ChooseLayout
  | InsertCheck
  | RemoveCheck
  | RepresentAsControlFlow
  | Cleanup
  deriving (Eq, Ord, Show)

data LoweringDecision = LoweringDecision
  { loweringDecisionId :: DecisionId
  , loweringDecisionDigest :: Digest
  , loweringSourceArtifactDigest :: Digest
  , loweringTargetArtifactDigest :: Digest
  , loweringSourceRepresentation :: Text
  , loweringTargetRepresentation :: Text
  , loweringSemanticEntities :: [Text]
  , loweringObligationRevisions :: [RevisionId]
  , loweringAssuranceEntries :: [EvidenceEntryId]
  , loweringAssuranceUses :: [AssuranceUseId]
  , loweringAction :: LoweringAction
  , loweringRepresentationBefore :: Text
  , loweringRepresentationAfter :: Text
  , loweringInvariantsPreserved :: [Text]
  , loweringInvariantsTransferred :: [InvariantId]
  , loweringRuntimeResidue :: [Text]
  , loweringCostClass :: Maybe CostClass
  , loweringCostShape :: CostShape
  , loweringTargetPreconditions :: [Text]
  , loweringAssumptions :: [Text]
  , loweringDerivedObligations :: [RevisionId]
  , loweringInspectionPlan :: [Text]
  }
  deriving (Eq, Ord, Show)

data FactDisposition
  = FactConsumed Text
  | FactTransferred [InvariantId]
  | FactErased AssuranceUseId
  | FactRuntimeRetained EvidenceEntryId
  | FactDerived RevisionId
  deriving (Eq, Ord, Show)

data FactTransfer = FactTransfer
  { factTransferId :: Text
  , factSourceRevision :: Maybe RevisionId
  , factDisposition :: FactDisposition
  }
  deriving (Eq, Ord, Show)

data RequiredControlEdge = RequiredControlEdge
  { requiredEdgeFunction :: Text
  , requiredEdgeFrom :: BlockId
  , requiredEdgeTo :: BlockId
  , requiredEdgeReason :: Text
  }
  deriving (Eq, Ord, Show)

data InvariantClaim
  = InvariantSingleTransportHandle Text ValueId
  | InvariantBorrowAliases Text ValueId ValueId
  | InvariantRecognitionGate Text BlockId ValueId BlockId BlockId
  | InvariantBranchTargets Text BlockId BlockId BlockId
  | InvariantExactReceive Text BlockId ValueId BlockId BlockId
  | InvariantExactSend Text BlockId ValueId BlockId BlockId
  | InvariantRequiredEdge RequiredControlEdge
  | InvariantFatalTerminal Text BlockId
  | InvariantCleanupOwners Text BlockId [ValueId]
  deriving (Eq, Ord, Show)

data StageInvariant = StageInvariant
  { stageInvariantId :: InvariantId
  , stageInvariantClaim :: InvariantClaim
  }
  deriving (Eq, Ord, Show)

data StageContract = StageContract
  { stageContractId :: Text
  , stageSourceArtifactDigest :: Digest
  , stageTargetArtifactDigest :: Digest
  , stageFacts :: [FactTransfer]
  , stageInvariants :: Map InvariantId StageInvariant
  , stageRequiredEdges :: [RequiredControlEdge]
  , stageDerivedObligations :: [RevisionId]
  , stageAssumptions :: [Text]
  , stageTraceRelation :: [Text]
  , stageResourceFailureRelation :: [Text]
  }
  deriving (Eq, Show)

data SystemsProgram = SystemsProgram
  { systemsProgramName :: Text
  , systemsProgramProfile :: CompilationProfile
  , systemsProgramFunctions :: Map Text SystemsFunction
  }
  deriving (Eq, Show)

data LoweringLedger = LoweringLedger
  { loweringLedgerDecisions :: Map DecisionId LoweringDecision
  , loweringLedgerRoot :: Digest
  }
  deriving (Eq, Show)

data SystemsArtifact = SystemsArtifact
  { systemsArtifactProgram :: SystemsProgram
  , systemsArtifactStageContract :: StageContract
  , systemsArtifactLoweringLedger :: LoweringLedger
  }
  deriving (Eq, Show)

deriveLoweringDecisionDigest :: LoweringDecision -> Digest
deriveLoweringDecisionDigest lowering = digestText (Text.intercalate "|"
  [ field "source_artifact" (unDigest (loweringSourceArtifactDigest lowering))
  , field "target_artifact" (unDigest (loweringTargetArtifactDigest lowering))
  , field "source" (loweringSourceRepresentation lowering)
  , field "target" (loweringTargetRepresentation lowering)
  , field "semantic" (renderTexts (loweringSemanticEntities lowering))
  , field "obligations" (renderTexts (map unRevisionId (loweringObligationRevisions lowering)))
  , field "evidence" (renderTexts (map unEvidenceEntryId (loweringAssuranceEntries lowering)))
  , field "uses" (renderTexts (map unAssuranceUseId (loweringAssuranceUses lowering)))
  , field "action" (renderLoweringAction (loweringAction lowering))
  , field "before" (loweringRepresentationBefore lowering)
  , field "after" (loweringRepresentationAfter lowering)
  , field "preserved" (renderTexts (loweringInvariantsPreserved lowering))
  , field "transferred" (renderTexts (map unInvariantId (loweringInvariantsTransferred lowering)))
  , field "residue" (renderTexts (loweringRuntimeResidue lowering))
  , field "cost_class" (maybe "none" renderCostClass (loweringCostClass lowering))
  , field "cost_shape" (renderCostShape (loweringCostShape lowering))
  , field "target_preconditions" (renderTexts (loweringTargetPreconditions lowering))
  , field "assumptions" (renderTexts (loweringAssumptions lowering))
  , field "derived" (renderTexts (map unRevisionId (loweringDerivedObligations lowering)))
  , field "inspection" (renderTexts (loweringInspectionPlan lowering))
  ])

deriveLoweringLedgerRoot :: Map DecisionId LoweringDecision -> Digest
deriveLoweringLedgerRoot decisions = digestText . Text.intercalate "|" $
  [ unDecisionId key <> "=" <> unDigest (loweringDecisionDigest lowering)
  | (key, lowering) <- Map.toAscList decisions
  ]

systemsProgramDigest :: SystemsProgram -> Digest
systemsProgramDigest program = digestText (Text.intercalate "|"
  [ field "name" (systemsProgramName program)
  , field "profile" (renderProfile (systemsProgramProfile program))
  , field "functions" (renderList renderFunction (Map.toAscList (systemsProgramFunctions program)))
  ])
  where
    renderFunction (name, function) = Text.intercalate ";"
      [ field "key" name
      , field "name" (systemsFunctionName function)
      , field "entry" (unBlockId (systemsFunctionEntry function))
      , field "values" (renderList renderValue (Map.toAscList (systemsFunctionValues function)))
      , field "blocks" (renderList renderBlock (Map.toAscList (systemsFunctionBlocks function)))
      ]

    renderValue (key, value) = Text.intercalate ";"
      [ field "key" (unValueId key)
      , field "id" (unValueId (systemsValueId value))
      , field "role" (renderValueRole (systemsValueRole value))
      , field "storage" (maybe "none" id (systemsStorageIdentity value))
      ]

    renderBlock (key, blockValue) = Text.intercalate ";"
      [ field "key" (unBlockId key)
      , field "id" (unBlockId (systemsBlockId blockValue))
      , field "ops" (renderList renderOp (systemsBlockOps blockValue))
      , field "term" (renderTerminator (systemsBlockTerminator blockValue))
      ]

stageContractDigest :: StageContract -> Digest
stageContractDigest contract = digestText (Text.intercalate "|"
  [ field "id" (stageContractId contract)
  , field "source" (unDigest (stageSourceArtifactDigest contract))
  , field "target" (unDigest (stageTargetArtifactDigest contract))
  , field "facts" (renderList renderFactTransfer (stageFacts contract))
  , field "invariants" (renderList renderInvariantEntry (Map.toAscList (stageInvariants contract)))
  , field "edges" (renderList renderEdge (stageRequiredEdges contract))
  , field "derived" (renderTexts (map unRevisionId (stageDerivedObligations contract)))
  , field "assumptions" (renderTexts (stageAssumptions contract))
  , field "trace" (renderTexts (stageTraceRelation contract))
  , field "resource_failure" (renderTexts (stageResourceFailureRelation contract))
  ])
  where
    renderInvariantEntry (key, invariantValue) = Text.intercalate ";"
      [ field "key" (unInvariantId key)
      , field "id" (unInvariantId (stageInvariantId invariantValue))
      , field "claim" (renderInvariantClaim (stageInvariantClaim invariantValue))
      ]

systemsArtifactDigest :: SystemsArtifact -> Digest
systemsArtifactDigest artifact = digestText (Text.intercalate "|"
  [ field "program" (unDigest (systemsProgramDigest (systemsArtifactProgram artifact)))
  , field "stage_contract" (unDigest (stageContractDigest (systemsArtifactStageContract artifact)))
  , field "lowering_ledger" (unDigest (loweringLedgerRoot (systemsArtifactLoweringLedger artifact)))
  ])

blockSuccessors :: SystemsBlock -> [BlockId]
blockSuccessors blockValue = case systemsBlockTerminator blockValue of
  TermJump target -> [target]
  TermBranch _ yes no -> [yes, no]
  TermRecognize { recognizeSuccess = yes, recognizeFailure = no } -> [yes, no]
  TermRuntimeCheck { checkSuccess = yes, checkFailure = no } -> [yes, no]
  TermReceiveExact { exactSuccess = yes, exactFailure = no } -> [yes, no]
  TermSendExact { sendExactSuccess = yes, sendExactFailure = no } -> [yes, no]
  TermStore { storeSuccess = yes, storeFailure = no } -> [yes, no]
  TermSessionOffer { sessionOfferArms = arms } ->
    map (choiceArmTarget . snd) (Map.toAscList arms)
  TermRuntimeChoice { runtimeChoiceArms = arms } ->
    map (runtimeChoiceArmTarget . snd) (Map.toAscList arms)
  TermReturnScalar _ -> []
  TermEnd _ -> []
  TermFatal _ -> []

runtimeSites :: SystemsFunction -> [RuntimeSiteRef]
runtimeSites function = concatMap blockSites (Map.elems (systemsFunctionBlocks function))
  where
    blockSites blockValue = opSites (systemsBlockOps blockValue) <> termSites (systemsBlockTerminator blockValue)

    opSites operations =
      [ site
      | OpRuntimeCall { runtimeCallSite = Just site } <- operations
      ]

    termSites terminator = case terminator of
      TermRecognize { recognizeSite = site } -> [site]
      TermRuntimeCheck { checkSite = site } -> [site]
      TermReceiveExact { exactSite = site } -> [site]
      TermSendExact { sendExactSite = site } -> [site]
      TermStore { storeSite = site } -> [site]
      TermRuntimeChoice { runtimeChoiceSite = Just site } -> [site]
      _ -> []

field :: Text -> Text -> Text
field key value = key <> "=" <> atom value

atom :: Text -> Text
atom value = Text.pack (show (Text.length value)) <> ":" <> value

renderTexts :: [Text] -> Text
renderTexts values = renderList id (sort values)

renderList :: (a -> Text) -> [a] -> Text
renderList render values = "[" <> Text.intercalate "," (map (atom . render) values) <> "]"

renderProfile :: CompilationProfile -> Text
renderProfile profile = case profile of
  CheckedRuntime -> "checked-runtime"
  CertifiedRelease -> "certified-release"

renderValueRole :: SystemsValueRole -> Text
renderValueRole role = case role of
  TransportHandle -> "transport-handle"
  PendingIngress grammar -> "pending(" <> atom grammar <> ")"
  FrameOwner grammar -> "frame-owner(" <> atom grammar <> ")"
  OwnedBuffer description -> "owned-buffer(" <> atom description <> ")"
  BorrowedSlice owner -> "borrowed-slice(" <> atom (unValueId owner) <> ")"
  RuntimeScalar description -> "runtime-scalar(" <> atom description <> ")"
  TypedScalar scalarType -> "typed-scalar(" <> atom (renderScalarType scalarType) <> ")"
  RuntimeRecord description -> "runtime-record(" <> atom description <> ")"
  DiagnosticState description -> "diagnostic-state(" <> atom description <> ")"

renderRuntimeSiteKind :: RuntimeSiteKind -> Text
renderRuntimeSiteKind kind = case kind of
  RecognitionBoundary grammar -> "recognition(" <> atom grammar <> ")"
  ValidationBoundary claim -> "validation(" <> atom claim <> ")"
  BranchRefinementBoundary claim -> "branch-refinement(" <> atom claim <> ")"
  ExactReceiveBoundary -> "exact-receive"
  ExactSendBoundary -> "exact-send"
  DigestBoundary -> "digest"
  StorageBoundary -> "storage"
  SourceSemanticRuntime name -> "source-runtime(" <> atom name <> ")"

renderRuntimeSite :: RuntimeSiteRef -> Text
renderRuntimeSite site = Text.intercalate ";"
  [ field "kind" (renderRuntimeSiteKind (runtimeSiteKind site))
  , field "revision" (unRevisionId (runtimeSiteRevision site))
  , field "evidence" (unEvidenceEntryId (runtimeSiteEvidence site))
  , field "cost" (runtimeSiteCostRef site)
  ]

renderOp :: SystemsOp -> Text
renderOp operation = case operation of
  OpReceiveFrame pending frame transport grammar lowering -> tag "receive-frame"
    [unValueId pending, unValueId frame, unValueId transport, grammar, unDecisionId lowering]
  OpBorrowView view owner lowering -> tag "borrow-view"
    [unValueId view, unValueId owner, unDecisionId lowering]
  OpCommitIngress pending transport lowering -> tag "commit-ingress"
    [unValueId pending, unValueId transport, unDecisionId lowering]
  OpDestroyPending pending frame lowering -> tag "destroy-pending"
    [unValueId pending, unValueId frame, unDecisionId lowering]
  OpReleaseOwner owner lowering -> tag "release-owner"
    [unValueId owner, unDecisionId lowering]
  OpCleanupPartial owner lowering -> tag "cleanup-partial"
    [unValueId owner, unDecisionId lowering]
  OpRuntimeCall name inputs outputs site lowering -> tag "runtime-call"
    [ name
    , renderList unValueId inputs
    , renderList unValueId outputs
    , maybe "none" renderRuntimeSite site
    , unDecisionId lowering
    ]
  OpSessionSelect transport label payload lowering -> tag "session-select"
    [ unValueId transport
    , label
    , maybe "none" unValueId payload
    , unDecisionId lowering
    ]
  OpCopy source target lowering -> tag "copy"
    [unValueId source, unValueId target, unDecisionId lowering]
  OpEraseFact revision useId lowering -> tag "erase-fact"
    [unRevisionId revision, unAssuranceUseId useId, unDecisionId lowering]
  OpDiagnostic name lowering -> tag "diagnostic" [name, unDecisionId lowering]
  OpScalarLiteral output literal -> tag "scalar-literal"
    [unValueId output, renderScalarLiteral literal]
  OpTraceEvent name -> tag "trace" [name]
  where
    tag name fields = name <> renderList id fields

renderTerminator :: SystemsTerminator -> Text
renderTerminator terminator = case terminator of
  TermJump target -> tag "jump" [unBlockId target]
  TermBranch condition yes no -> tag "branch" [unValueId condition, unBlockId yes, unBlockId no]
  TermRecognize pending rawView site yes no -> tag "recognize"
    [unValueId pending, unValueId rawView, renderRuntimeSite site, unBlockId yes, unBlockId no]
  TermRuntimeCheck inputs site yes no -> tag "runtime-check"
    [renderList unValueId inputs, renderRuntimeSite site, unBlockId yes, unBlockId no]
  TermReceiveExact transport lengthValue owner site yes no -> tag "receive-exact"
    [ unValueId transport, unValueId lengthValue, unValueId owner, renderRuntimeSite site
    , unBlockId yes, unBlockId no
    ]
  TermSendExact transport owner site yes no -> tag "send-exact"
    [unValueId transport, unValueId owner, renderRuntimeSite site, unBlockId yes, unBlockId no]
  TermStore owner result site yes no -> tag "store"
    [unValueId owner, unValueId result, renderRuntimeSite site, unBlockId yes, unBlockId no]
  TermSessionOffer transport arms -> tag "session-offer"
    [unValueId transport, renderList renderChoiceArm (Map.toAscList arms)]
  TermRuntimeChoice name inputs site arms -> tag "runtime-choice"
    [ name
    , renderList unValueId inputs
    , maybe "none" renderRuntimeSite site
    , renderList renderRuntimeChoiceArm (Map.toAscList arms)
    ]
  TermReturnScalar value -> tag "return-scalar" [unValueId value]
  TermEnd outcome -> tag "end" [outcome]
  TermFatal failure -> tag "fatal" [failure]
  where
    tag name fields = name <> renderList id fields

renderChoiceArm :: (Text, SystemsChoiceArm) -> Text
renderChoiceArm (label, arm) = Text.intercalate ";"
  [ field "label" label
  , field "payload" (maybe "none" unValueId (choiceArmPayloadBinding arm))
  , field "target" (unBlockId (choiceArmTarget arm))
  ]

renderRuntimeChoiceArm :: (Text, SystemsRuntimeChoiceArm) -> Text
renderRuntimeChoiceArm (label, arm) = Text.intercalate ";"
  [ field "label" label
  , field "payload" (maybe "none" unValueId (runtimeChoiceArmPayloadBinding arm))
  , field "target" (unBlockId (runtimeChoiceArmTarget arm))
  ]

renderLoweringAction :: LoweringAction -> Text
renderLoweringAction action = case action of
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

renderCostClass :: CostClass -> Text
renderCostClass costClass = case costClass of
  SemanticRequired -> "semantic-required"
  RuntimeAssuranceRequired -> "runtime-assurance-required"
  TargetRequired -> "target-required"
  DefensiveProfile -> "defensive-profile"
  ConservativeLowering -> "conservative-lowering"

renderCostShape :: CostShape -> Text
renderCostShape shape = renderTexts
  [ "compile_time=" <> maybeText (costCompileTime shape)
  , "code_size=" <> maybeText (costCodeSize shape)
  , "allocation_count=" <> maybeText (costAllocationCount shape)
  , "peak_live_memory=" <> maybeText (costPeakLiveMemory shape)
  , "bytes_copied=" <> maybeText (costBytesCopied shape)
  , "dynamic_check_count=" <> maybeText (costDynamicCheckCount shape)
  , "branch_or_dispatch=" <> maybeText (costBranchOrDispatch shape)
  , "hash_or_crypto_work=" <> maybeText (costHashOrCryptoWork shape)
  , "synchronization=" <> maybeText (costSynchronization shape)
  , "frequency=" <> maybeText (costFrequency shape)
  ]
  where
    maybeText = maybe "" id

renderFactTransfer :: FactTransfer -> Text
renderFactTransfer transfer = Text.intercalate ";"
  [ field "id" (factTransferId transfer)
  , field "revision" (maybe "none" unRevisionId (factSourceRevision transfer))
  , field "disposition" (renderFactDisposition (factDisposition transfer))
  ]

renderFactDisposition :: FactDisposition -> Text
renderFactDisposition disposition = case disposition of
  FactConsumed reason -> "consumed(" <> atom reason <> ")"
  FactTransferred invariants -> "transferred" <> renderList unInvariantId invariants
  FactErased useId -> "erased(" <> atom (unAssuranceUseId useId) <> ")"
  FactRuntimeRetained entry -> "runtime(" <> atom (unEvidenceEntryId entry) <> ")"
  FactDerived revision -> "derived(" <> atom (unRevisionId revision) <> ")"

renderEdge :: RequiredControlEdge -> Text
renderEdge edge = Text.intercalate ";"
  [ field "function" (requiredEdgeFunction edge)
  , field "from" (unBlockId (requiredEdgeFrom edge))
  , field "to" (unBlockId (requiredEdgeTo edge))
  , field "reason" (requiredEdgeReason edge)
  ]

renderInvariantClaim :: InvariantClaim -> Text
renderInvariantClaim claim = case claim of
  InvariantSingleTransportHandle functionName handle ->
    tag "single-transport" [functionName, unValueId handle]
  InvariantBorrowAliases functionName view owner ->
    tag "borrow-aliases" [functionName, unValueId view, unValueId owner]
  InvariantRecognitionGate functionName blockId pending yes no ->
    tag "recognition-gate" [functionName, unBlockId blockId, unValueId pending, unBlockId yes, unBlockId no]
  InvariantBranchTargets functionName blockId yes no ->
    tag "branch-targets" [functionName, unBlockId blockId, unBlockId yes, unBlockId no]
  InvariantExactReceive functionName blockId owner yes no ->
    tag "exact-receive" [functionName, unBlockId blockId, unValueId owner, unBlockId yes, unBlockId no]
  InvariantExactSend functionName blockId owner yes no ->
    tag "exact-send" [functionName, unBlockId blockId, unValueId owner, unBlockId yes, unBlockId no]
  InvariantRequiredEdge edge -> "required-edge(" <> atom (renderEdge edge) <> ")"
  InvariantFatalTerminal functionName blockId ->
    tag "fatal-terminal" [functionName, unBlockId blockId]
  InvariantCleanupOwners functionName blockId owners ->
    tag "cleanup-owners" [functionName, unBlockId blockId, renderList unValueId owners]
  where
    tag name fields = name <> renderList id fields
