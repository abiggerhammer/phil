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
import Phil.Assurance.Verify (VerificationError, verifyManifest)
import Phil.Systems.IR

data SystemsVerificationContext = SystemsVerificationContext
  { systemsAssuranceLedger :: AssuranceLedger
  , systemsAssuranceManifest :: AssuranceManifest
  , systemsAssuranceVerificationContext :: VerificationContext
  , systemsExpectedRuntimeKinds :: Map EvidenceEntryId RuntimeSiteKind
  , systemsExpectedSourceFacts :: Set Text
  }
  deriving (Eq, Show)

data SystemsVerificationError
  = SystemsAssuranceError VerificationError
  | LoweringLedgerRootMismatch Digest Digest
  | ManifestLoweringRootMismatch Digest Digest
  | DecisionMapKeyMismatch DecisionId DecisionId
  | DecisionDigestMismatch DecisionId Digest Digest
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
  | RemoveCheckDropsRuntimeEvidence DecisionId EvidenceEntryId
  | FunctionMapKeyMismatch Text Text
  | MissingEntryBlock Text BlockId
  | BlockMapKeyMismatch Text BlockId BlockId
  | UnknownControlTarget Text BlockId BlockId
  | ValueMapKeyMismatch Text ValueId ValueId
  | BorrowedViewUnknownOwner Text ValueId ValueId
  | BorrowedViewOwnerNotOwning Text ValueId ValueId
  | DuplicateOwningStorage Text Text [ValueId]
  | CopyWithoutCopyDecision Text BlockId DecisionId
  | BorrowWithoutBorrowDecision Text BlockId DecisionId
  | OperationReferencesUnknownDecision Text BlockId DecisionId
  | DiagnosticInCertifiedRelease Text BlockId
  | DiagnosticDecisionNotDefensive Text BlockId DecisionId
  | ReceivePendingRoleMismatch Text BlockId ValueId
  | ReceiveFrameOwnerRoleMismatch Text BlockId ValueId
  | RecognitionPendingUnknown Text BlockId ValueId
  | RecognitionRawViewMismatch Text BlockId ValueId ValueId
  | RecognitionSuccessMissingCommit Text BlockId ValueId BlockId
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
  | RetainedRuntimeUseSiteMismatch AssuranceUseId
  | DuplicateRetainedRuntimeSite AssuranceUseId Int
  | ErasureUseMissing AssuranceUseId
  | ErasureUseWrongKind AssuranceUseId
  | ErasureUseRevisionMismatch AssuranceUseId RevisionId RevisionId
  | ErasureOperationMissingUse Text BlockId AssuranceUseId
  | StageFactSetMismatch (Set Text) (Set Text)
  | DuplicateStageFact Text
  | EmptyStageFactId
  | StageInvariantMissing Text InvariantId
  | StageErasureUseNotSelected Text AssuranceUseId
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
  verifyLoweringLedger context artifact
  verifyProgram context artifact
  verifyStageContract context artifact
  verifyRuntimeCoverage context artifact
  verifyErasureCoverage context artifact

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
  unless (actualRoot == expectedRoot) $
    Left (LoweringLedgerRootMismatch expectedRoot actualRoot)
  unless (manifestRoot == actualRoot) $
    Left (ManifestLoweringRootMismatch actualRoot manifestRoot)
  forM_ (Map.toAscList decisions) $ \(key, decision) -> do
    unless (key == loweringDecisionId decision) $
      Left (DecisionMapKeyMismatch key (loweringDecisionId decision))
    when (Text.null (unDecisionId key)) $
      Left EmptyDecisionId
    let expectedDigest = deriveLoweringDecisionDigest decision
    unless (loweringDecisionDigest decision == expectedDigest) $
      Left (DecisionDigestMismatch key expectedDigest (loweringDecisionDigest decision))
    case loweringCostClass decision of
      Nothing -> Left (MissingDecisionCostClass key)
      Just RuntimeAssuranceRequired ->
        when (null (loweringAssuranceEntries decision) || null (loweringObligationRevisions decision)) $
          Left (RuntimeAssuranceDecisionMissingEvidence key)
      Just _ -> pure ()
    forM_ (loweringObligationRevisions decision) $ \revision ->
      unless (Set.member revision (manifestObligationRevisions (systemsAssuranceManifest context))) $
        Left (DecisionRevisionNotSelected key revision)
    forM_ (loweringAssuranceEntries decision) $ \entry ->
      unless (Set.member entry (manifestEvidenceEntries (systemsAssuranceManifest context))) $
        Left (DecisionEvidenceNotSelected key entry)
    forM_ (loweringAssuranceUses decision) $ \use ->
      unless (Set.member use (manifestAssuranceUses (systemsAssuranceManifest context))) $
        Left (DecisionUseNotSelected key use)
    forM_ (loweringInvariantsTransferred decision) $ \invariantId ->
      unless (Map.member invariantId (stageInvariants (systemsArtifactStageContract artifact))) $
        Left (DecisionInvariantMissing key invariantId)
    forM_ (loweringDerivedObligations decision) $ \revision ->
      unless (Set.member revision (manifestObligationRevisions (systemsAssuranceManifest context))) $
        Left (DecisionDerivedObligationNotSelected key revision)
    when (loweringAction decision == Copy && costBytesCopied (loweringCostShape decision) == Nothing) $
      Left (CopyDecisionMissingByteCost key)
    when (loweringAction decision == Erase && null (loweringAssuranceUses decision)) $
      Left (ErasureDecisionMissingUse key)
    when (loweringAction decision == RemoveCheck) $
      forM_ (loweringAssuranceEntries decision) $ \entryId ->
        case Map.lookup entryId (ledgerEvidence (systemsAssuranceLedger context)) of
          Just entry | evidenceAssuranceKind entry == RuntimeEnforced ->
            Left (RemoveCheckDropsRuntimeEvidence key entryId)
          _ -> pure ()

verifyProgram
  :: SystemsVerificationContext
  -> SystemsArtifact
  -> Either SystemsVerificationError ()
verifyProgram context artifact = do
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
    forM_ (Map.toAscList (systemsFunctionBlocks function)) $ \(blockKey, block) -> do
      unless (blockKey == systemsBlockId block) $
        Left (BlockMapKeyMismatch functionKey blockKey (systemsBlockId block))
      forM_ (blockSuccessors block) $ \target ->
        unless (Map.member target (systemsFunctionBlocks function)) $
          Left (UnknownControlTarget functionKey blockKey target)
      forM_ (systemsBlockOps block) $ \operation -> do
        verifyOperationDecision functionKey blockKey decisions operation
        verifyOperationShape program functionKey function blockKey recognitionTargets operation
      verifyTerminatorShape functionKey function blockKey recognitionTargets (systemsBlockTerminator block)

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
        Just decision -> case operation of
          OpCopy {}
            | loweringAction decision /= Copy ->
                Left (CopyWithoutCopyDecision functionKey blockKey decisionId)
          OpBorrowView {}
            | loweringAction decision /= Borrow ->
                Left (BorrowWithoutBorrowDecision functionKey blockKey decisionId)
          _ -> pure ()

operationDecision :: SystemsOp -> Maybe DecisionId
operationDecision operation = case operation of
  OpReceiveFrame { receiveDecision = decision } -> Just decision
  OpBorrowView { borrowDecision = decision } -> Just decision
  OpCommitIngress { commitDecision = decision } -> Just decision
  OpDestroyPending { destroyDecision = decision } -> Just decision
  OpReleaseOwner { releaseDecision = decision } -> Just decision
  OpCleanupPartial { cleanupDecision = decision } -> Just decision
  OpRuntimeCall { runtimeCallDecision = decision } -> Just decision
  OpCopy { copyDecision = decision } -> Just decision
  OpEraseFact { eraseDecision = decision } -> Just decision
  OpDiagnostic { diagnosticDecision = decision } -> Just decision
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
    OpDiagnostic _ decisionId -> do
      when (systemsProgramProfile program == CertifiedRelease) $
        Left (DiagnosticInCertifiedRelease functionKey blockKey)
      case Map.lookup decisionId (loweringLedgerDecisions placeholderLedger) of
        _ -> pure ()
    _ -> pure ()
  where
    -- The real decision/profile check for diagnostics is performed in
    -- verifyProgramWithDiagnosticCosts below via the artifact ledger.  This
    -- placeholder keeps operation-shape checking independent of that map.
    placeholderLedger = LoweringLedger Map.empty (Digest "")

verifyTerminatorShape
  :: Text
  -> SystemsFunction
  -> BlockId
  -> Map ValueId (BlockId, BlockId)
  -> SystemsTerminator
  -> Either SystemsVerificationError ()
verifyTerminatorShape functionKey function blockKey _ terminator =
  case terminator of
    TermRecognize pending rawView _ success failure -> do
      case Map.lookup pending (systemsFunctionValues function) of
        Just SystemsValue { systemsValueRole = PendingIngress _ } -> pure ()
        _ -> Left (RecognitionPendingUnknown functionKey blockKey pending)
      frameOwner <- findFrameOwnerForPending function pending
      case Map.lookup rawView (systemsFunctionValues function) of
        Just SystemsValue { systemsValueRole = BorrowedSlice owner }
          | owner == frameOwner -> pure ()
        _ -> Left (RecognitionRawViewMismatch functionKey blockKey rawView frameOwner)
      unless (blockContainsCommit function success pending) $
        Left (RecognitionSuccessMissingCommit functionKey blockKey pending success)
      unless (blockContainsDestroy function failure pending) $
        Left (RecognitionFailureMissingDestroy functionKey blockKey pending failure)
    _ -> pure ()

findFrameOwnerForPending
  :: SystemsFunction
  -> ValueId
  -> Either SystemsVerificationError ValueId
findFrameOwnerForPending function pending =
  case
    [ frame
    | block <- Map.elems (systemsFunctionBlocks function)
    , OpReceiveFrame { receivePending = pendingId, receiveFrameOwner = frame } <- systemsBlockOps block
    , pendingId == pending
    ] of
      frame : _ -> Right frame
      [] -> Left (RecognitionPendingUnknown (systemsFunctionName function) (systemsFunctionEntry function) pending)

blockContainsCommit :: SystemsFunction -> BlockId -> ValueId -> Bool
blockContainsCommit function blockId pending =
  case Map.lookup blockId (systemsFunctionBlocks function) of
    Nothing -> False
    Just block -> any isCommit (systemsBlockOps block)
  where
    isCommit OpCommitIngress { commitPending = candidate } = candidate == pending
    isCommit _ = False

blockContainsDestroy :: SystemsFunction -> BlockId -> ValueId -> Bool
blockContainsDestroy function blockId pending =
  case Map.lookup blockId (systemsFunctionBlocks function) of
    Nothing -> False
    Just block -> any isDestroy (systemsBlockOps block)
  where
    isDestroy OpDestroyPending { destroyPending = candidate } = candidate == pending
    isDestroy _ = False

collectRecognitionTargets :: SystemsFunction -> Map ValueId (BlockId, BlockId)
collectRecognitionTargets function = Map.fromList
  [ (recognizePending terminator, (recognizeSuccess terminator, recognizeFailure terminator))
  | block <- Map.elems (systemsFunctionBlocks function)
  , let terminator = systemsBlockTerminator block
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
    forM_ (Map.elems (systemsFunctionBlocks function)) $ \block ->
      forM_ (systemsBlockOps block) $ \operation -> case operation of
        OpEraseFact revision useId _ -> do
          unless (Set.member useId (manifestAssuranceUses manifest)) $
            Left (ErasureOperationMissingUse (systemsFunctionName function) (systemsBlockId block) useId)
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
  unless (actualFacts == expectedFacts) $
    Left (StageFactSetMismatch expectedFacts actualFacts)
  when (length (map factTransferId facts) /= length (nub (map factTransferId facts))) $
    case firstDuplicate (map factTransferId facts) of
      Just duplicate -> Left (DuplicateStageFact duplicate)
      Nothing -> pure ()
  forM_ facts $ \fact -> do
    when (Text.null (factTransferId fact)) $
      Left EmptyStageFactId
    case factDisposition fact of
      FactConsumed _ -> pure ()
      FactTransferred invariantId ->
        unless (Map.member invariantId (stageInvariants contract)) $
          Left (StageInvariantMissing (factTransferId fact) invariantId)
      FactErased useId -> do
        unless (Set.member useId (manifestAssuranceUses manifest)) $
          Left (StageErasureUseNotSelected (factTransferId fact) useId)
        case factSourceRevision fact of
          Nothing -> Left (StageErasureUseNotSelected (factTransferId fact) useId)
          Just revision -> verifyErasureUse ledger useId revision
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
  forM_ (stageRequiredEdges contract) $ \edge -> do
    function <- case Map.lookup (requiredEdgeFunction edge) (systemsProgramFunctions program) of
      Nothing -> Left (StageRequiredFunctionMissing (requiredEdgeFunction edge))
      Just value -> Right value
    block <- case Map.lookup (requiredEdgeFrom edge) (systemsFunctionBlocks function) of
      Nothing -> Left (StageRequiredBlockMissing (requiredEdgeFunction edge) (requiredEdgeFrom edge))
      Just value -> Right value
    unless (requiredEdgeTo edge `elem` blockSuccessors block) $
      Left (StageRequiredEdgeMissing (requiredEdgeFunction edge) (requiredEdgeFrom edge) (requiredEdgeTo edge))
  forM_ (stageDerivedObligations contract) $ \revision ->
    unless (Set.member revision (manifestObligationRevisions manifest)) $
      Left (StageDerivedObligationMissing revision)
  verifyDiagnosticCosts artifact

verifyDiagnosticCosts :: SystemsArtifact -> Either SystemsVerificationError ()
verifyDiagnosticCosts artifact = do
  let program = systemsArtifactProgram artifact
      decisions = loweringLedgerDecisions (systemsArtifactLoweringLedger artifact)
  forM_ (Map.elems (systemsProgramFunctions program)) $ \function ->
    forM_ (Map.elems (systemsFunctionBlocks function)) $ \block ->
      forM_ (systemsBlockOps block) $ \operation -> case operation of
        OpDiagnostic _ decisionId ->
          case Map.lookup decisionId decisions of
            Just decision
              | loweringCostClass decision == Just DefensiveProfile
              , systemsProgramProfile program == CheckedRuntime -> pure ()
              | otherwise -> Left (DiagnosticDecisionNotDefensive
                  (systemsFunctionName function) (systemsBlockId block) decisionId)
            Nothing -> Left (OperationReferencesUnknownDecision
                (systemsFunctionName function) (systemsBlockId block) decisionId)
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
