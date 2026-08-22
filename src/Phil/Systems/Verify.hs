{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.Verify
  ( SystemsVerificationContext (..)
  , SystemsVerificationError (..)
  , verifySystemsArtifact
  ) where

import Control.Monad (forM_, unless, when)
import Data.List (nub)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types
import Phil.Assurance.Verify (ManifestError, verifyManifest)
import Phil.Core.Scalar (scalarLiteralInRange, scalarLiteralType)
import Phil.Systems.IR

data SystemsVerificationContext = SystemsVerificationContext
  { systemsAssuranceLedger :: AssuranceLedger
  , systemsAssuranceManifest :: AssuranceManifest
  , systemsAssuranceVerificationContext :: VerificationContext
  , systemsExpectedSourceArtifactDigest :: Digest
  , systemsExpectedRuntimeKinds :: Map EvidenceEntryId RuntimeSiteKind
  , systemsExpectedSourceFacts :: Set Text
  , systemsFactsRequiringTransfer :: Set Text
  }
  deriving (Eq, Show)

data SystemsVerificationError
  = SystemsAssuranceError ManifestError
  | SourceArtifactDigestMismatch Digest Digest
  | TargetArtifactDigestMismatch Digest Digest
  | ManifestImplementationDigestMismatch Digest Digest
  | LoweringLedgerRootMismatch Digest Digest
  | ManifestLoweringRootMismatch Digest Digest
  | DecisionMapKeyMismatch DecisionId DecisionId
  | DecisionDigestMismatch DecisionId Digest Digest
  | DecisionSourceArtifactMismatch DecisionId Digest Digest
  | DecisionTargetArtifactMismatch DecisionId Digest Digest
  | EmptyDecisionId
  | MissingDecisionCostClass DecisionId
  | DecisionRevisionNotSelected DecisionId RevisionId
  | DecisionEvidenceNotSelected DecisionId EvidenceEntryId
  | DecisionUseNotSelected DecisionId AssuranceUseId
  | DecisionInvariantMissing DecisionId InvariantId
  | DecisionDerivedObligationNotSelected DecisionId RevisionId
  | RuntimeAssuranceDecisionMissingEvidence DecisionId
  | CopyDecisionMissingByteCost DecisionId
  | ErasureDecisionMissingUse DecisionId
  | ErasureWithoutFactTransfer DecisionId
  | RemoveCheckDropsRuntimeEvidence DecisionId EvidenceEntryId
  | FunctionMapKeyMismatch Text Text
  | MissingEntryBlock Text BlockId
  | BlockMapKeyMismatch Text BlockId BlockId
  | UnknownControlTarget Text BlockId BlockId
  | ValueMapKeyMismatch Text ValueId ValueId
  | BorrowedViewUnknownOwner Text ValueId ValueId
  | BorrowedViewOwnerNotOwning Text ValueId ValueId
  | DuplicateOwningStorage Text Text [ValueId]
  | ScalarLiteralOutputMissing Text BlockId ValueId
  | ScalarLiteralOutputNotScalar Text BlockId ValueId
  | ScalarLiteralTypeMismatch Text BlockId ValueId ScalarType ScalarType
  | ScalarLiteralOutOfRange Text BlockId ScalarLiteral
  | ScalarReturnUnknownValue Text BlockId ValueId
  | ScalarReturnValueNotScalar Text BlockId ValueId
  | ScalarReturnTypeMismatch Text ScalarType ScalarType
  | CopyWithoutCopyDecision Text BlockId DecisionId
  | BorrowWithoutBorrowDecision Text BlockId DecisionId
  | OperationReferencesUnknownDecision Text BlockId DecisionId
  | DiagnosticInCertifiedRelease Text BlockId
  | DiagnosticDecisionNotDefensive Text BlockId DecisionId
  | ReceivePendingRoleMismatch Text BlockId ValueId
  | ReceiveFrameOwnerRoleMismatch Text BlockId ValueId
  | RecognitionPendingUnknown Text BlockId ValueId
  | RecognitionReceiveMissing Text BlockId ValueId
  | RecognitionBorrowMissing Text BlockId ValueId
  | RecognitionRawViewMismatch Text BlockId ValueId ValueId
  | RecognitionSuccessMissingCommit Text BlockId ValueId BlockId
  | RecognitionCommitNotFirstUse Text BlockId ValueId BlockId
  | RecognitionFailureMissingDestroy Text BlockId ValueId BlockId
  | OrphanCommitIngress Text BlockId ValueId
  | OrphanDestroyPending Text BlockId ValueId
  | RuntimeSiteEvidenceNotSelected EvidenceEntryId
  | RuntimeSiteEvidenceMissing EvidenceEntryId
  | RuntimeSiteNotRuntimeEnforced EvidenceEntryId AssuranceKind
  | RuntimeSiteRevisionMismatch EvidenceEntryId RevisionId RevisionId
  | RuntimeSiteCostMismatch EvidenceEntryId Text [Text]
  | RuntimeSiteKindMismatch EvidenceEntryId RuntimeSiteKind RuntimeSiteKind
  | RetainedRuntimeUseMissingSite AssuranceUseId EvidenceEntryId
  | DuplicateRetainedRuntimeSite AssuranceUseId Int
  | ErasureUseMissing AssuranceUseId
  | ErasureUseWrongKind AssuranceUseId
  | ErasureUseRevisionMismatch AssuranceUseId RevisionId RevisionId
  | ErasureOperationMissingUse Text BlockId AssuranceUseId
  | StageFactSetMismatch (Set Text) (Set Text)
  | DuplicateStageFact Text
  | EmptyStageFactId
  | StageFactIllegallyConsumed Text
  | EmptyTransferredInvariantSet Text
  | StageInvariantMissing Text InvariantId
  | StageInvariantMapKeyMismatch InvariantId InvariantId
  | StageInvariantFunctionMissing InvariantId Text
  | StageInvariantValueMismatch InvariantId
  | StageInvariantControlMismatch InvariantId
  | StageInvariantCopyViolation InvariantId ValueId
  | StageInvariantCleanupMissing InvariantId ValueId
  | StageErasureUseNotSelected Text AssuranceUseId
  | StageErasureDecisionMissing Text AssuranceUseId
  | StageErasureOperationMissing Text AssuranceUseId
  | StageRuntimeEvidenceNotSelected Text EvidenceEntryId
  | StageFactRevisionMismatch Text RevisionId RevisionId
  | StageDerivedObligationNotSelected Text RevisionId
  | StageRequiredFunctionMissing Text
  | StageRequiredBlockMissing Text BlockId
  | StageRequiredEdgeMissing Text BlockId BlockId
  | StageDerivedObligationMissing RevisionId
  deriving (Eq, Show)

verifySystemsArtifact
  :: SystemsVerificationContext
  -> SystemsArtifact
  -> Either SystemsVerificationError ()
verifySystemsArtifact context artifact = do
  mapLeft SystemsAssuranceError $
    verifyManifest
      (systemsAssuranceVerificationContext context)
      (systemsAssuranceLedger context)
      (systemsAssuranceManifest context)
  verifyArtifactIdentity context artifact
  verifyLoweringLedger context artifact
  verifyProgram artifact
  verifyStageContract context artifact
  verifyRuntimeCoverage context artifact
  verifyErasureCoverage context artifact

verifyArtifactIdentity
  :: SystemsVerificationContext
  -> SystemsArtifact
  -> Either SystemsVerificationError ()
verifyArtifactIdentity context artifact = do
  let contract = systemsArtifactStageContract artifact
      expectedSource = systemsExpectedSourceArtifactDigest context
      actualSource = stageSourceArtifactDigest contract
      expectedTarget = systemsProgramDigest (systemsArtifactProgram artifact)
      actualTarget = stageTargetArtifactDigest contract
      expectedImplementation = systemsArtifactDigest artifact
      actualImplementation = manifestImplementationDigest (systemsAssuranceManifest context)
  unless (actualSource == expectedSource) $
    Left (SourceArtifactDigestMismatch expectedSource actualSource)
  unless (actualTarget == expectedTarget) $
    Left (TargetArtifactDigestMismatch expectedTarget actualTarget)
  unless (actualImplementation == expectedImplementation) $
    Left (ManifestImplementationDigestMismatch expectedImplementation actualImplementation)

verifyLoweringLedger
  :: SystemsVerificationContext
  -> SystemsArtifact
  -> Either SystemsVerificationError ()
verifyLoweringLedger context artifact = do
  let ledger = systemsArtifactLoweringLedger artifact
      decisions = loweringLedgerDecisions ledger
      expectedRoot = deriveLoweringLedgerRoot decisions
      actualRoot = loweringLedgerRoot ledger
      manifestRoot = manifestLoweringLedgerRoot (systemsAssuranceManifest context)
      contract = systemsArtifactStageContract artifact
      sourceDigest = stageSourceArtifactDigest contract
      targetDigest = stageTargetArtifactDigest contract
  unless (actualRoot == expectedRoot) $
    Left (LoweringLedgerRootMismatch expectedRoot actualRoot)
  unless (manifestRoot == actualRoot) $
    Left (ManifestLoweringRootMismatch actualRoot manifestRoot)
  forM_ (Map.toAscList decisions) $ \(key, lowering) -> do
    unless (key == loweringDecisionId lowering) $
      Left (DecisionMapKeyMismatch key (loweringDecisionId lowering))
    when (Text.null (unDecisionId key)) $
      Left EmptyDecisionId
    let expectedDigest = deriveLoweringDecisionDigest lowering
    unless (loweringDecisionDigest lowering == expectedDigest) $
      Left (DecisionDigestMismatch key expectedDigest (loweringDecisionDigest lowering))
    unless (loweringSourceArtifactDigest lowering == sourceDigest) $
      Left (DecisionSourceArtifactMismatch key sourceDigest (loweringSourceArtifactDigest lowering))
    unless (loweringTargetArtifactDigest lowering == targetDigest) $
      Left (DecisionTargetArtifactMismatch key targetDigest (loweringTargetArtifactDigest lowering))
    case loweringCostClass lowering of
      Nothing -> Left (MissingDecisionCostClass key)
      Just RuntimeAssuranceRequired ->
        when (null (loweringAssuranceEntries lowering) || null (loweringObligationRevisions lowering)) $
          Left (RuntimeAssuranceDecisionMissingEvidence key)
      Just _ -> pure ()
    forM_ (loweringObligationRevisions lowering) $ \revision ->
      unless (Set.member revision (manifestObligationRevisions (systemsAssuranceManifest context))) $
        Left (DecisionRevisionNotSelected key revision)
    forM_ (loweringAssuranceEntries lowering) $ \entry ->
      unless (Set.member entry (manifestEvidenceEntries (systemsAssuranceManifest context))) $
        Left (DecisionEvidenceNotSelected key entry)
    forM_ (loweringAssuranceUses lowering) $ \use ->
      unless (Set.member use (manifestAssuranceUses (systemsAssuranceManifest context))) $
        Left (DecisionUseNotSelected key use)
    forM_ (loweringInvariantsTransferred lowering) $ \invariantId ->
      unless (Map.member invariantId (stageInvariants contract)) $
        Left (DecisionInvariantMissing key invariantId)
    forM_ (loweringDerivedObligations lowering) $ \revision ->
      unless (Set.member revision (manifestObligationRevisions (systemsAssuranceManifest context))) $
        Left (DecisionDerivedObligationNotSelected key revision)
    when (loweringAction lowering == Copy && costBytesCopied (loweringCostShape lowering) == Nothing) $
      Left (CopyDecisionMissingByteCost key)
    when (loweringAction lowering == Erase && null (loweringAssuranceUses lowering)) $
      Left (ErasureDecisionMissingUse key)
    when
      ( loweringAction lowering == Erase
      && null (loweringInvariantsTransferred lowering)
      && null (loweringDerivedObligations lowering)
      ) $
      Left (ErasureWithoutFactTransfer key)
    when (loweringAction lowering == RemoveCheck) $
      forM_ (loweringAssuranceEntries lowering) $ \entryId ->
        case Map.lookup entryId (ledgerEvidence (systemsAssuranceLedger context)) of
          Just entry | evidenceAssuranceKind entry == RuntimeEnforced ->
            Left (RemoveCheckDropsRuntimeEvidence key entryId)
          _ -> pure ()

verifyProgram :: SystemsArtifact -> Either SystemsVerificationError ()
verifyProgram artifact = do
  let program = systemsArtifactProgram artifact
      decisions = loweringLedgerDecisions (systemsArtifactLoweringLedger artifact)
  forM_ (Map.toAscList (systemsProgramFunctions program)) $ \(functionKey, function) -> do
    unless (functionKey == systemsFunctionName function) $
      Left (FunctionMapKeyMismatch functionKey (systemsFunctionName function))
    unless (Map.member (systemsFunctionEntry function) (systemsFunctionBlocks function)) $
      Left (MissingEntryBlock functionKey (systemsFunctionEntry function))
    verifyValues functionKey function
    verifyOwningStorage functionKey function
    let recognitionTargets = collectRecognitionTargets function
    forM_ (Map.toAscList (systemsFunctionBlocks function)) $ \(blockKey, blockValue) -> do
      unless (blockKey == systemsBlockId blockValue) $
        Left (BlockMapKeyMismatch functionKey blockKey (systemsBlockId blockValue))
      forM_ (blockSuccessors blockValue) $ \target ->
        unless (Map.member target (systemsFunctionBlocks function)) $
          Left (UnknownControlTarget functionKey blockKey target)
      forM_ (systemsBlockOps blockValue) $ \operation -> do
        verifyOperationDecision functionKey blockKey decisions operation
        verifyOperationShape program functionKey function blockKey recognitionTargets operation
      verifyTerminatorShape functionKey function blockKey (systemsBlockTerminator blockValue)
    verifyScalarReturnTypes functionKey function

verifyValues :: Text -> SystemsFunction -> Either SystemsVerificationError ()
verifyValues functionKey function =
  forM_ (Map.toAscList (systemsFunctionValues function)) $ \(key, value) -> do
    unless (key == systemsValueId value) $
      Left (ValueMapKeyMismatch functionKey key (systemsValueId value))
    case systemsValueRole value of
      BorrowedSlice owner ->
        case Map.lookup owner (systemsFunctionValues function) of
          Nothing -> Left (BorrowedViewUnknownOwner functionKey key owner)
          Just ownerValue ->
            unless (isOwningRole (systemsValueRole ownerValue)) $
              Left (BorrowedViewOwnerNotOwning functionKey key owner)
      _ -> pure ()

verifyOwningStorage :: Text -> SystemsFunction -> Either SystemsVerificationError ()
verifyOwningStorage functionKey function =
  forM_ (Map.toAscList ownersByStorage) $ \(storage, owners) ->
    when (length owners > 1) $
      Left (DuplicateOwningStorage functionKey storage owners)
  where
    ownersByStorage = Map.fromListWith (<>)
      [ (storage, [systemsValueId value])
      | value <- Map.elems (systemsFunctionValues function)
      , isOwningRole (systemsValueRole value)
      , Just storage <- [systemsStorageIdentity value]
      ]

isOwningRole :: SystemsValueRole -> Bool
isOwningRole role = case role of
  TransportHandle -> True
  PendingIngress _ -> True
  FrameOwner _ -> True
  OwnedBuffer _ -> True
  _ -> False

verifyOperationDecision
  :: Text
  -> BlockId
  -> Map DecisionId LoweringDecision
  -> SystemsOp
  -> Either SystemsVerificationError ()
verifyOperationDecision functionKey blockKey decisions operation =
  case operationDecision operation of
    Nothing -> pure ()
    Just decisionId ->
      case Map.lookup decisionId decisions of
        Nothing -> Left (OperationReferencesUnknownDecision functionKey blockKey decisionId)
        Just lowering -> case operation of
          OpCopy {}
            | loweringAction lowering /= Copy ->
                Left (CopyWithoutCopyDecision functionKey blockKey decisionId)
          OpBorrowView {}
            | loweringAction lowering /= Borrow ->
                Left (BorrowWithoutBorrowDecision functionKey blockKey decisionId)
          _ -> pure ()

operationDecision :: SystemsOp -> Maybe DecisionId
operationDecision operation = case operation of
  OpReceiveFrame { receiveDecision = lowering } -> Just lowering
  OpBorrowView { borrowDecision = lowering } -> Just lowering
  OpCommitIngress { commitDecision = lowering } -> Just lowering
  OpDestroyPending { destroyDecision = lowering } -> Just lowering
  OpReleaseOwner { releaseDecision = lowering } -> Just lowering
  OpCleanupPartial { cleanupDecision = lowering } -> Just lowering
  OpRuntimeCall { runtimeCallDecision = lowering } -> Just lowering
  OpCopy { copyDecision = lowering } -> Just lowering
  OpEraseFact { eraseDecision = lowering } -> Just lowering
  OpDiagnostic { diagnosticDecision = lowering } -> Just lowering
  OpScalarLiteral {} -> Nothing
  OpTraceEvent _ -> Nothing

verifyOperationShape
  :: SystemsProgram
  -> Text
  -> SystemsFunction
  -> BlockId
  -> Map ValueId (BlockId, BlockId)
  -> SystemsOp
  -> Either SystemsVerificationError ()
verifyOperationShape program functionKey function blockKey recognitionTargets operation =
  case operation of
    OpReceiveFrame pending frame _ grammar _ -> do
      case Map.lookup pending (systemsFunctionValues function) of
        Just SystemsValue { systemsValueRole = PendingIngress pendingGrammar }
          | pendingGrammar == grammar -> pure ()
        _ -> Left (ReceivePendingRoleMismatch functionKey blockKey pending)
      case Map.lookup frame (systemsFunctionValues function) of
        Just SystemsValue { systemsValueRole = FrameOwner frameGrammar }
          | frameGrammar == grammar -> pure ()
        _ -> Left (ReceiveFrameOwnerRoleMismatch functionKey blockKey frame)
    OpCommitIngress pending _ _ ->
      case Map.lookup pending recognitionTargets of
        Just (successBlock, _) | successBlock == blockKey -> pure ()
        _ -> Left (OrphanCommitIngress functionKey blockKey pending)
    OpDestroyPending pending _ _ ->
      case Map.lookup pending recognitionTargets of
        Just (_, failureBlock) | failureBlock == blockKey -> pure ()
        _ -> Left (OrphanDestroyPending functionKey blockKey pending)
    OpDiagnostic _ _ ->
      when (systemsProgramProfile program == CertifiedRelease) $
        Left (DiagnosticInCertifiedRelease functionKey blockKey)
    OpScalarLiteral output literal -> do
      unless (scalarLiteralInRange literal) $
        Left (ScalarLiteralOutOfRange functionKey blockKey literal)
      case Map.lookup output (systemsFunctionValues function) of
        Nothing -> Left (ScalarLiteralOutputMissing functionKey blockKey output)
        Just SystemsValue { systemsValueRole = TypedScalar actualType } ->
          let expectedType = scalarLiteralType literal
          in unless (actualType == expectedType) $
              Left (ScalarLiteralTypeMismatch functionKey blockKey output expectedType actualType)
        Just _ -> Left (ScalarLiteralOutputNotScalar functionKey blockKey output)
    _ -> pure ()

verifyTerminatorShape
  :: Text
  -> SystemsFunction
  -> BlockId
  -> SystemsTerminator
  -> Either SystemsVerificationError ()
verifyTerminatorShape functionKey function blockKey terminator =
  case terminator of
    TermRecognize pending rawView _ success failure -> do
      case Map.lookup pending (systemsFunctionValues function) of
        Just SystemsValue { systemsValueRole = PendingIngress _ } -> pure ()
        _ -> Left (RecognitionPendingUnknown functionKey blockKey pending)
      blockValue <- case Map.lookup blockKey (systemsFunctionBlocks function) of
        Nothing -> Left (StageRequiredBlockMissing functionKey blockKey)
        Just value -> Right value
      unless (any (receivesPending pending) (systemsBlockOps blockValue)) $
        Left (RecognitionReceiveMissing functionKey blockKey pending)
      frameOwner <- findFrameOwnerForPending function pending
      case Map.lookup rawView (systemsFunctionValues function) of
        Just SystemsValue { systemsValueRole = BorrowedSlice owner }
          | owner == frameOwner -> pure ()
        _ -> Left (RecognitionRawViewMismatch functionKey blockKey rawView frameOwner)
      unless (any (borrowsView rawView frameOwner) (systemsBlockOps blockValue)) $
        Left (RecognitionBorrowMissing functionKey blockKey rawView)
      unless (blockContainsCommit function success pending) $
        Left (RecognitionSuccessMissingCommit functionKey blockKey pending success)
      unless (commitPrecedesTransportUse function success pending) $
        Left (RecognitionCommitNotFirstUse functionKey blockKey pending success)
      unless (blockContainsDestroy function failure pending) $
        Left (RecognitionFailureMissingDestroy functionKey blockKey pending failure)
    TermReturnScalar valueId ->
      case Map.lookup valueId (systemsFunctionValues function) of
        Nothing -> Left (ScalarReturnUnknownValue functionKey blockKey valueId)
        Just SystemsValue { systemsValueRole = TypedScalar _ } -> pure ()
        Just _ -> Left (ScalarReturnValueNotScalar functionKey blockKey valueId)
    _ -> pure ()
  where
    receivesPending pending OpReceiveFrame { receivePending = candidate } = candidate == pending
    receivesPending _ _ = False
    borrowsView view owner OpBorrowView { borrowView = candidateView, borrowOwner = candidateOwner } =
      view == candidateView && owner == candidateOwner
    borrowsView _ _ _ = False

verifyScalarReturnTypes :: Text -> SystemsFunction -> Either SystemsVerificationError ()
verifyScalarReturnTypes functionKey function =
  case scalarTypes of
    [] -> pure ()
    firstType : rest ->
      case filter (/= firstType) rest of
        [] -> pure ()
        mismatched : _ -> Left (ScalarReturnTypeMismatch functionKey firstType mismatched)
  where
    scalarTypes =
      [ scalarType
      | blockValue <- Map.elems (systemsFunctionBlocks function)
      , TermReturnScalar valueId <- [systemsBlockTerminator blockValue]
      , Just SystemsValue { systemsValueRole = TypedScalar scalarType } <-
          [Map.lookup valueId (systemsFunctionValues function)]
      ]

findFrameOwnerForPending
  :: SystemsFunction
  -> ValueId
  -> Either SystemsVerificationError ValueId
findFrameOwnerForPending function pending =
  case
    [ frame
    | blockValue <- Map.elems (systemsFunctionBlocks function)
    , OpReceiveFrame { receivePending = pendingId, receiveFrameOwner = frame } <- systemsBlockOps blockValue
    , pendingId == pending
    ] of
      frame : _ -> Right frame
      [] -> Left (RecognitionPendingUnknown (systemsFunctionName function) (systemsFunctionEntry function) pending)

blockContainsCommit :: SystemsFunction -> BlockId -> ValueId -> Bool
blockContainsCommit function blockId pending =
  case Map.lookup blockId (systemsFunctionBlocks function) of
    Nothing -> False
    Just blockValue -> any isCommit (systemsBlockOps blockValue)
  where
    isCommit OpCommitIngress { commitPending = candidate } = candidate == pending
    isCommit _ = False

commitPrecedesTransportUse :: SystemsFunction -> BlockId -> ValueId -> Bool
commitPrecedesTransportUse function blockId pending =
  case Map.lookup blockId (systemsFunctionBlocks function) of
    Nothing -> False
    Just blockValue -> go False (systemsBlockOps blockValue)
      where
        go seenCommit [] = seenCommit
        go seenCommit (operation : rest) = case operation of
          OpCommitIngress { commitPending = candidate }
            | candidate == pending -> go True rest
          _ | operationUsesTransport operation && not seenCommit -> False
          _ -> go seenCommit rest

operationUsesTransport :: SystemsOp -> Bool
operationUsesTransport operation = case operation of
  OpReceiveFrame {} -> True
  OpCommitIngress {} -> True
  OpRuntimeCall { runtimeCallInputs = inputs } -> not (null inputs)
  _ -> False

blockContainsDestroy :: SystemsFunction -> BlockId -> ValueId -> Bool
blockContainsDestroy function blockId pending =
  case Map.lookup blockId (systemsFunctionBlocks function) of
    Nothing -> False
    Just blockValue -> any isDestroy (systemsBlockOps blockValue)
  where
    isDestroy OpDestroyPending { destroyPending = candidate } = candidate == pending
    isDestroy _ = False

collectRecognitionTargets :: SystemsFunction -> Map ValueId (BlockId, BlockId)
collectRecognitionTargets function = Map.fromList
  [ (recognizePending terminator, (recognizeSuccess terminator, recognizeFailure terminator))
  | blockValue <- Map.elems (systemsFunctionBlocks function)
  , let terminator = systemsBlockTerminator blockValue
  , TermRecognize {} <- [terminator]
  ]

verifyRuntimeCoverage
  :: SystemsVerificationContext
  -> SystemsArtifact
  -> Either SystemsVerificationError ()
verifyRuntimeCoverage context artifact = do
  let programSites = concatMap runtimeSites (Map.elems (systemsProgramFunctions (systemsArtifactProgram artifact)))
      manifest = systemsAssuranceManifest context
      ledger = systemsAssuranceLedger context
  forM_ programSites $ \site -> verifyRuntimeSite context site
  forM_ (Set.toAscList (manifestAssuranceUses manifest)) $ \useId ->
    case Map.lookup useId (ledgerUses ledger) of
      Just RetainedRuntimeUse
        { useObligationRevision = revision
        , useRuntimeEvidence = evidenceId
        , useCostRef = costRef
        } -> do
          let matches =
                [ site
                | site <- programSites
                , runtimeSiteEvidence site == evidenceId
                , runtimeSiteRevision site == revision
                , runtimeSiteCostRef site == costRef
                ]
          case length matches of
            0 -> Left (RetainedRuntimeUseMissingSite useId evidenceId)
            1 -> pure ()
            count -> Left (DuplicateRetainedRuntimeSite useId count)
      _ -> pure ()

verifyRuntimeSite
  :: SystemsVerificationContext
  -> RuntimeSiteRef
  -> Either SystemsVerificationError ()
verifyRuntimeSite context site = do
  let manifest = systemsAssuranceManifest context
      ledger = systemsAssuranceLedger context
      evidenceId = runtimeSiteEvidence site
  unless (Set.member evidenceId (manifestEvidenceEntries manifest)) $
    Left (RuntimeSiteEvidenceNotSelected evidenceId)
  entry <- case Map.lookup evidenceId (ledgerEvidence ledger) of
    Nothing -> Left (RuntimeSiteEvidenceMissing evidenceId)
    Just value -> Right value
  unless (evidenceAssuranceKind entry == RuntimeEnforced) $
    Left (RuntimeSiteNotRuntimeEnforced evidenceId (evidenceAssuranceKind entry))
  unless (evidenceObligationRevision entry == runtimeSiteRevision site) $
    Left (RuntimeSiteRevisionMismatch evidenceId (evidenceObligationRevision entry) (runtimeSiteRevision site))
  unless (runtimeSiteCostRef site `elem` evidenceCostRefs entry) $
    Left (RuntimeSiteCostMismatch evidenceId (runtimeSiteCostRef site) (evidenceCostRefs entry))
  case Map.lookup evidenceId (systemsExpectedRuntimeKinds context) of
    Nothing -> pure ()
    Just expectedKind ->
      unless (expectedKind == runtimeSiteKind site) $
        Left (RuntimeSiteKindMismatch evidenceId expectedKind (runtimeSiteKind site))

verifyErasureCoverage
  :: SystemsVerificationContext
  -> SystemsArtifact
  -> Either SystemsVerificationError ()
verifyErasureCoverage context artifact = do
  let ledger = systemsAssuranceLedger context
      manifest = systemsAssuranceManifest context
  forM_ (Map.elems (systemsProgramFunctions (systemsArtifactProgram artifact))) $ \function ->
    forM_ (Map.elems (systemsFunctionBlocks function)) $ \blockValue ->
      forM_ (systemsBlockOps blockValue) $ \operation -> case operation of
        OpEraseFact revision useId _ -> do
          unless (Set.member useId (manifestAssuranceUses manifest)) $
            Left (ErasureOperationMissingUse (systemsFunctionName function) (systemsBlockId blockValue) useId)
          verifyErasureUse ledger useId revision
        _ -> pure ()

verifyErasureUse
  :: AssuranceLedger
  -> AssuranceUseId
  -> RevisionId
  -> Either SystemsVerificationError ()
verifyErasureUse ledger useId expectedRevision =
  case Map.lookup useId (ledgerUses ledger) of
    Nothing -> Left (ErasureUseMissing useId)
    Just ErasureUse { useObligationRevision = actualRevision }
      | actualRevision == expectedRevision -> pure ()
      | otherwise -> Left (ErasureUseRevisionMismatch useId expectedRevision actualRevision)
    Just _ -> Left (ErasureUseWrongKind useId)

verifyStageContract
  :: SystemsVerificationContext
  -> SystemsArtifact
  -> Either SystemsVerificationError ()
verifyStageContract context artifact = do
  let contract = systemsArtifactStageContract artifact
      facts = stageFacts contract
      actualFacts = Set.fromList (map factTransferId facts)
      expectedFacts = systemsExpectedSourceFacts context
      manifest = systemsAssuranceManifest context
      ledger = systemsAssuranceLedger context
      program = systemsArtifactProgram artifact
      decisions = loweringLedgerDecisions (systemsArtifactLoweringLedger artifact)
  unless (actualFacts == expectedFacts) $
    Left (StageFactSetMismatch expectedFacts actualFacts)
  when (length (map factTransferId facts) /= length (nub (map factTransferId facts))) $
    case firstDuplicate (map factTransferId facts) of
      Just duplicate -> Left (DuplicateStageFact duplicate)
      Nothing -> pure ()
  verifyStageInvariants artifact
  forM_ facts $ \fact -> do
    when (Text.null (factTransferId fact)) $
      Left EmptyStageFactId
    case factDisposition fact of
      FactConsumed _ ->
        when (Set.member (factTransferId fact) (systemsFactsRequiringTransfer context)) $
          Left (StageFactIllegallyConsumed (factTransferId fact))
      FactTransferred invariantIds -> do
        when (null invariantIds) $
          Left (EmptyTransferredInvariantSet (factTransferId fact))
        forM_ invariantIds $ \invariantId ->
          unless (Map.member invariantId (stageInvariants contract)) $
            Left (StageInvariantMissing (factTransferId fact) invariantId)
      FactErased useId -> do
        unless (Set.member useId (manifestAssuranceUses manifest)) $
          Left (StageErasureUseNotSelected (factTransferId fact) useId)
        revision <- case factSourceRevision fact of
          Nothing -> Left (StageErasureUseNotSelected (factTransferId fact) useId)
          Just value -> Right value
        verifyErasureUse ledger useId revision
        unless (any (decisionErasesUse useId) (Map.elems decisions)) $
          Left (StageErasureDecisionMissing (factTransferId fact) useId)
        unless (programErasesUse program revision useId) $
          Left (StageErasureOperationMissing (factTransferId fact) useId)
      FactRuntimeRetained evidenceId -> do
        unless (Set.member evidenceId (manifestEvidenceEntries manifest)) $
          Left (StageRuntimeEvidenceNotSelected (factTransferId fact) evidenceId)
        entry <- case Map.lookup evidenceId (ledgerEvidence ledger) of
          Nothing -> Left (RuntimeSiteEvidenceMissing evidenceId)
          Just value -> Right value
        case factSourceRevision fact of
          Just revision | evidenceObligationRevision entry /= revision ->
            Left (StageFactRevisionMismatch (factTransferId fact) revision (evidenceObligationRevision entry))
          _ -> pure ()
      FactDerived revision ->
        unless (Set.member revision (manifestObligationRevisions manifest)) $
          Left (StageDerivedObligationNotSelected (factTransferId fact) revision)
  forM_ (stageRequiredEdges contract) $ verifyRequiredEdge program
  forM_ (stageDerivedObligations contract) $ \revision ->
    unless (Set.member revision (manifestObligationRevisions manifest)) $
      Left (StageDerivedObligationMissing revision)
  verifyDiagnosticCosts artifact
  where
    decisionErasesUse useId lowering =
      loweringAction lowering == Erase && useId `elem` loweringAssuranceUses lowering

verifyStageInvariants :: SystemsArtifact -> Either SystemsVerificationError ()
verifyStageInvariants artifact = do
  let contract = systemsArtifactStageContract artifact
      program = systemsArtifactProgram artifact
  forM_ (Map.toAscList (stageInvariants contract)) $ \(key, invariantValue) -> do
    unless (key == stageInvariantId invariantValue) $
      Left (StageInvariantMapKeyMismatch key (stageInvariantId invariantValue))
    verifyInvariantClaim program key (stageInvariantClaim invariantValue)

verifyInvariantClaim
  :: SystemsProgram
  -> InvariantId
  -> InvariantClaim
  -> Either SystemsVerificationError ()
verifyInvariantClaim program invariantId claim = case claim of
  InvariantSingleTransportHandle functionName handle -> do
    function <- requireFunction invariantId functionName program
    let handles =
          [ systemsValueId value
          | value <- Map.elems (systemsFunctionValues function)
          , systemsValueRole value == TransportHandle
          ]
    unless (handles == [handle]) $
      Left (StageInvariantValueMismatch invariantId)
  InvariantBorrowAliases functionName view owner -> do
    function <- requireFunction invariantId functionName program
    case Map.lookup view (systemsFunctionValues function) of
      Just SystemsValue { systemsValueRole = BorrowedSlice actualOwner }
        | actualOwner == owner -> pure ()
      _ -> Left (StageInvariantValueMismatch invariantId)
    when (functionCopiesFrom function owner) $
      Left (StageInvariantCopyViolation invariantId owner)
  InvariantRecognitionGate functionName blockId pending yes no -> do
    function <- requireFunction invariantId functionName program
    blockValue <- requireInvariantBlock invariantId function blockId
    case systemsBlockTerminator blockValue of
      TermRecognize { recognizePending = actual, recognizeSuccess = actualYes, recognizeFailure = actualNo }
        | actual == pending && actualYes == yes && actualNo == no
        , blockContainsCommit function yes pending
        , blockContainsDestroy function no pending -> pure ()
      _ -> Left (StageInvariantControlMismatch invariantId)
  InvariantBranchTargets functionName blockId yes no -> do
    function <- requireFunction invariantId functionName program
    blockValue <- requireInvariantBlock invariantId function blockId
    case systemsBlockTerminator blockValue of
      TermBranch _ actualYes actualNo | actualYes == yes && actualNo == no -> pure ()
      _ -> Left (StageInvariantControlMismatch invariantId)
  InvariantExactReceive functionName blockId owner yes no -> do
    function <- requireFunction invariantId functionName program
    blockValue <- requireInvariantBlock invariantId function blockId
    case systemsBlockTerminator blockValue of
      TermReceiveExact { exactPayloadOwner = actualOwner, exactSuccess = actualYes, exactFailure = actualNo }
        | actualOwner == owner && actualYes == yes && actualNo == no -> pure ()
      _ -> Left (StageInvariantControlMismatch invariantId)
  InvariantExactSend functionName blockId owner yes no -> do
    function <- requireFunction invariantId functionName program
    blockValue <- requireInvariantBlock invariantId function blockId
    case systemsBlockTerminator blockValue of
      TermSendExact { sendExactOwner = actualOwner, sendExactSuccess = actualYes, sendExactFailure = actualNo }
        | actualOwner == owner && actualYes == yes && actualNo == no -> pure ()
      _ -> Left (StageInvariantControlMismatch invariantId)
  InvariantRequiredEdge edge -> verifyRequiredEdge program edge
  InvariantFatalTerminal functionName blockId -> do
    function <- requireFunction invariantId functionName program
    blockValue <- requireInvariantBlock invariantId function blockId
    case systemsBlockTerminator blockValue of
      TermFatal _ -> pure ()
      _ -> Left (StageInvariantControlMismatch invariantId)
  InvariantCleanupOwners functionName blockId owners -> do
    function <- requireFunction invariantId functionName program
    blockValue <- requireInvariantBlock invariantId function blockId
    forM_ owners $ \owner ->
      unless (any (operationCleans owner) (systemsBlockOps blockValue)) $
        Left (StageInvariantCleanupMissing invariantId owner)

requireFunction
  :: InvariantId
  -> Text
  -> SystemsProgram
  -> Either SystemsVerificationError SystemsFunction
requireFunction invariantId functionName program =
  case Map.lookup functionName (systemsProgramFunctions program) of
    Nothing -> Left (StageInvariantFunctionMissing invariantId functionName)
    Just function -> Right function

requireInvariantBlock
  :: InvariantId
  -> SystemsFunction
  -> BlockId
  -> Either SystemsVerificationError SystemsBlock
requireInvariantBlock invariantId function blockId =
  case Map.lookup blockId (systemsFunctionBlocks function) of
    Nothing -> Left (StageInvariantControlMismatch invariantId)
    Just blockValue -> Right blockValue

functionCopiesFrom :: SystemsFunction -> ValueId -> Bool
functionCopiesFrom function owner = any blockCopies (Map.elems (systemsFunctionBlocks function))
  where
    blockCopies blockValue = any isCopy (systemsBlockOps blockValue)
    isCopy OpCopy { copySource = source } = source == owner
    isCopy _ = False

operationCleans :: ValueId -> SystemsOp -> Bool
operationCleans owner operation = case operation of
  OpDestroyPending { destroyPending = pending, destroyFrameOwner = frame } ->
    owner == pending || owner == frame
  OpReleaseOwner { releaseOwner = released } -> owner == released
  OpCleanupPartial { cleanupOwner = cleaned } -> owner == cleaned
  _ -> False

verifyRequiredEdge
  :: SystemsProgram
  -> RequiredControlEdge
  -> Either SystemsVerificationError ()
verifyRequiredEdge program edge = do
  function <- case Map.lookup (requiredEdgeFunction edge) (systemsProgramFunctions program) of
    Nothing -> Left (StageRequiredFunctionMissing (requiredEdgeFunction edge))
    Just value -> Right value
  blockValue <- case Map.lookup (requiredEdgeFrom edge) (systemsFunctionBlocks function) of
    Nothing -> Left (StageRequiredBlockMissing (requiredEdgeFunction edge) (requiredEdgeFrom edge))
    Just value -> Right value
  unless (requiredEdgeTo edge `elem` blockSuccessors blockValue) $
    Left (StageRequiredEdgeMissing (requiredEdgeFunction edge) (requiredEdgeFrom edge) (requiredEdgeTo edge))

programErasesUse :: SystemsProgram -> RevisionId -> AssuranceUseId -> Bool
programErasesUse program revision useId = any functionErases (Map.elems (systemsProgramFunctions program))
  where
    functionErases function = any blockErases (Map.elems (systemsFunctionBlocks function))
    blockErases blockValue = any matches (systemsBlockOps blockValue)
    matches OpEraseFact { erasedRevision = actualRevision, erasedByUse = actualUse } =
      actualRevision == revision && actualUse == useId
    matches _ = False

verifyDiagnosticCosts :: SystemsArtifact -> Either SystemsVerificationError ()
verifyDiagnosticCosts artifact = do
  let program = systemsArtifactProgram artifact
      decisions = loweringLedgerDecisions (systemsArtifactLoweringLedger artifact)
  forM_ (Map.elems (systemsProgramFunctions program)) $ \function ->
    forM_ (Map.elems (systemsFunctionBlocks function)) $ \blockValue ->
      forM_ (systemsBlockOps blockValue) $ \operation -> case operation of
        OpDiagnostic _ decisionId ->
          case Map.lookup decisionId decisions of
            Just lowering
              | loweringCostClass lowering == Just DefensiveProfile
              , systemsProgramProfile program == CheckedRuntime -> pure ()
              | otherwise -> Left (DiagnosticDecisionNotDefensive
                  (systemsFunctionName function) (systemsBlockId blockValue) decisionId)
            Nothing -> Left (OperationReferencesUnknownDecision
                (systemsFunctionName function) (systemsBlockId blockValue) decisionId)
        _ -> pure ()

firstDuplicate :: Ord a => [a] -> Maybe a
firstDuplicate = go Set.empty
  where
    go _ [] = Nothing
    go seen (value : rest)
      | Set.member value seen = Just value
      | otherwise = go (Set.insert value seen) rest

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform = either (Left . transform) Right
