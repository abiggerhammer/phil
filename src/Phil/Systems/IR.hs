{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.IR
  ( CompilationProfile (..)
  , ValueId (..)
  , BlockId (..)
  , DecisionId (..)
  , InvariantId (..)
  , SystemsValueRole (..)
  , SystemsValue (..)
  , RuntimeSiteKind (..)
  , RuntimeSiteRef (..)
  , SystemsOp (..)
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
  , StageContract (..)
  , SystemsProgram (..)
  , LoweringLedger (..)
  , SystemsArtifact (..)
  , emptyCostShape
  , deriveLoweringDecisionDigest
  , deriveLoweringLedgerRoot
  , systemsProgramDigest
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
  | OpTraceEvent Text
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
  | TermStore
      { storeOwner :: ValueId
      , storeResult :: ValueId
      , storeSite :: RuntimeSiteRef
      , storeSuccess :: BlockId
      , storeFailure :: BlockId
      }
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
  | FactTransferred InvariantId
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

data StageContract = StageContract
  { stageContractId :: Text
  , stageSourceArtifactDigest :: Digest
  , stageFacts :: [FactTransfer]
  , stageInvariants :: Map InvariantId Text
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
deriveLoweringDecisionDigest decision = digestText (Text.intercalate "|"
  [ field "source" (loweringSourceRepresentation decision)
  , field "target" (loweringTargetRepresentation decision)
  , field "semantic" (renderTexts (loweringSemanticEntities decision))
  , field "obligations" (renderTexts (map unRevisionId (loweringObligationRevisions decision)))
  , field "evidence" (renderTexts (map unEvidenceEntryId (loweringAssuranceEntries decision)))
  , field "uses" (renderTexts (map unAssuranceUseId (loweringAssuranceUses decision)))
  , field "action" (Text.pack (show (loweringAction decision)))
  , field "before" (loweringRepresentationBefore decision)
  , field "after" (loweringRepresentationAfter decision)
  , field "preserved" (renderTexts (loweringInvariantsPreserved decision))
  , field "transferred" (renderTexts (map unInvariantId (loweringInvariantsTransferred decision)))
  , field "residue" (renderTexts (loweringRuntimeResidue decision))
  , field "cost_class" (maybe "" (Text.pack . show) (loweringCostClass decision))
  , field "cost_shape" (renderCostShape (loweringCostShape decision))
  , field "target_preconditions" (renderTexts (loweringTargetPreconditions decision))
  , field "assumptions" (renderTexts (loweringAssumptions decision))
  , field "derived" (renderTexts (map unRevisionId (loweringDerivedObligations decision)))
  , field "inspection" (renderTexts (loweringInspectionPlan decision))
  ])
  where
    field key value = key <> "=" <> atom value

    atom value = Text.pack (show (Text.length value)) <> ":" <> value

    renderTexts values = "[" <> Text.intercalate "," (map atom (sort values)) <> "]"

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

    maybeText = maybe "" id

deriveLoweringLedgerRoot :: Map DecisionId LoweringDecision -> Digest
deriveLoweringLedgerRoot decisions = digestText . Text.intercalate "|" $
  [ unDecisionId key <> "=" <> unDigest (loweringDecisionDigest decision)
  | (key, decision) <- Map.toAscList decisions
  ]

systemsProgramDigest :: SystemsProgram -> Digest
systemsProgramDigest program = digestText (Text.intercalate "|"
  [ systemsProgramName program
  , Text.pack (show (systemsProgramProfile program))
  , Text.intercalate ";" (map renderFunction (Map.toAscList (systemsProgramFunctions program)))
  ])
  where
    renderFunction (name, function) = Text.intercalate ":"
      [ name
      , unBlockId (systemsFunctionEntry function)
      , Text.intercalate "," (map renderValue (Map.toAscList (systemsFunctionValues function)))
      , Text.intercalate "," (map renderBlock (Map.toAscList (systemsFunctionBlocks function)))
      ]

    renderValue (valueId, value) =
      unValueId valueId <> "=" <> Text.pack (show (systemsValueRole value))
        <> "@" <> maybe "" id (systemsStorageIdentity value)

    renderBlock (blockId, block) =
      unBlockId blockId <> "{" <> Text.pack (show (systemsBlockOps block))
        <> ";" <> Text.pack (show (systemsBlockTerminator block)) <> "}"

blockSuccessors :: SystemsBlock -> [BlockId]
blockSuccessors block = case systemsBlockTerminator block of
  TermJump target -> [target]
  TermBranch _ yes no -> [yes, no]
  TermRecognize { recognizeSuccess = yes, recognizeFailure = no } -> [yes, no]
  TermRuntimeCheck { checkSuccess = yes, checkFailure = no } -> [yes, no]
  TermReceiveExact { exactSuccess = yes, exactFailure = no } -> [yes, no]
  TermStore { storeSuccess = yes, storeFailure = no } -> [yes, no]
  TermEnd _ -> []
  TermFatal _ -> []

runtimeSites :: SystemsFunction -> [RuntimeSiteRef]
runtimeSites function = concatMap blockSites (Map.elems (systemsFunctionBlocks function))
  where
    blockSites block = opSites (systemsBlockOps block) <> termSites (systemsBlockTerminator block)

    opSites operations =
      [ site
      | OpRuntimeCall { runtimeCallSite = Just site } <- operations
      ]

    termSites terminator = case terminator of
      TermRecognize { recognizeSite = site } -> [site]
      TermRuntimeCheck { checkSite = site } -> [site]
      TermReceiveExact { exactSite = site } -> [site]
      TermStore { storeSite = site } -> [site]
      _ -> []
