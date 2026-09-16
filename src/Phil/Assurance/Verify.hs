{-# LANGUAGE OverloadedStrings #-}

module Phil.Assurance.Verify
  ( GraphNode (..)
  , ManifestError (..)
  , verifyLedgerExtension
  , verifyManifest
  ) where

import qualified AssuranceValidityScopeKernel as AssuranceValidityScopeKernel
import Control.Monad (foldM, unless, when)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.EvidenceAuthorityKernelBridge
  ( artifactAuthorityKernelAccepts
  , runtimeAuthorityKernelAccepts
  )
import Phil.Assurance.Types
import Phil.Core.Syntax (ObligationId (..))


data GraphNode
  = ObligationNode RevisionId
  | EvidenceNode EvidenceEntryId
  deriving (Eq, Ord, Show)

data ManifestError
  = ManifestIdentityMismatch Digest Digest
  | BuildIdentityMismatch Text
  | LoweringLedgerRootMismatch Digest Digest
  | ValidityContextMismatch
  | ExpectedObligationSetMismatch (Set RevisionId) (Set RevisionId)
  | CertificationScopeOutsideManifest RevisionId
  | EmptyStableId Text
  | MissingRevision RevisionId
  | RevisionMapKeyMismatch RevisionId RevisionId
  | RevisionStatementDigestMismatch RevisionId Digest Digest
  | RevisionIdentityMismatch RevisionId RevisionId
  | InvalidAcceptanceRule RevisionId
  | MissingEvidenceEntry EvidenceEntryId
  | EvidenceMapKeyMismatch EvidenceEntryId EvidenceEntryId
  | EvidenceDigestMismatch EvidenceEntryId Digest Digest
  | EvidenceOutsideManifestObligation EvidenceEntryId RevisionId
  | SelectedRejectedEvidence EvidenceEntryId Text
  | MissingAssumption AssumptionId
  | AssumptionMapKeyMismatch AssumptionId AssumptionId
  | AssumptionDigestMismatch AssumptionId Digest Digest
  | UnpermittedAssumption AssumptionId
  | UnselectedAssumptionDependency EvidenceEntryId AssumptionId
  | MissingExport ExportId
  | ExportMapKeyMismatch ExportId ExportId
  | ExportDigestMismatch ExportId Digest Digest
  | UnpermittedExportBoundary ExportId Text
  | InScopeObligationExported RevisionId
  | OutOfScopeObligationNotExported RevisionId
  | MultipleExportsForObligation RevisionId
  | ExportOutsideManifestObligation ExportId RevisionId
  | MissingEvidenceDependency EvidenceEntryId EvidenceEntryId
  | MissingObligationDependency EvidenceEntryId RevisionId
  | DependencyOnExportedObligation EvidenceEntryId RevisionId
  | EvidenceValidityScopeMismatch EvidenceEntryId
  | AssumptionValidityScopeMismatch AssumptionId
  | ExportValidityScopeMismatch ExportId
  | MissingArtifact ArtifactIdentity
  | ArtifactDigestMismatch ArtifactRef Digest Digest
  | EvidenceKindRequiresArtifact EvidenceEntryId AssuranceKind
  | RuntimeEvidenceMissingMechanism EvidenceEntryId
  | RuntimeEvidenceMissingResidue EvidenceEntryId
  | RuntimeEvidenceMissingCostRef EvidenceEntryId
  | RuntimeMechanismIncomplete EvidenceEntryId
  | AssumedEvidenceMissingBoundary EvidenceEntryId
  | MissingCostReference EvidenceEntryId Text
  | EvidenceAuthorityKernelDisagreement EvidenceEntryId AssuranceKind
  | JustificationCycle [GraphNode]
  | ProvenanceCycle [RevisionId]
  | AcceptanceRuleUnsatisfied RevisionId
  | MissingAssuranceUse AssuranceUseId
  | AssuranceUseMapKeyMismatch AssuranceUseId AssuranceUseId
  | AssuranceUseDigestMismatch AssuranceUseId Digest Digest
  | AssuranceUseOutsideScope AssuranceUseId RevisionId
  | ErasureWithoutEvidence AssuranceUseId
  | AssuranceUseMissingEvidence AssuranceUseId EvidenceEntryId
  | AssuranceUseEvidenceMismatch AssuranceUseId EvidenceEntryId RevisionId
  | RuntimeUseRequiresRuntimeEvidence AssuranceUseId EvidenceEntryId
  | RuntimeUseCostMismatch AssuranceUseId Text
  | LedgerHistoryMutation Text
  deriving (Eq, Show)

verifyLedgerExtension :: AssuranceLedger -> AssuranceLedger -> Either ManifestError ()
verifyLedgerExtension oldLedger newLedger = do
  preserve "obligation revision" ledgerRevisions oldLedger newLedger
  preserve "evidence entry" ledgerEvidence oldLedger newLedger
  preserve "assumption" ledgerAssumptions oldLedger newLedger
  preserve "export" ledgerExports oldLedger newLedger
  preserve "assurance use" ledgerUses oldLedger newLedger
  where
    preserve
      :: (Ord key, Eq value)
      => Text
      -> (AssuranceLedger -> Map key value)
      -> AssuranceLedger
      -> AssuranceLedger
      -> Either ManifestError ()
    preserve label project before after =
      mapM_ check (Map.toList (project before))
      where
        current = project after
        check (key, value) =
          case Map.lookup key current of
            Just same | same == value -> Right ()
            _ -> Left (LedgerHistoryMutation label)

verifyManifest
  :: VerificationContext
  -> AssuranceLedger
  -> AssuranceManifest
  -> Either ManifestError ()
verifyManifest context ledger manifest = do
  verifyBuildIdentity
  verifyManifestSets
  revisions <- loadRevisions
  evidence <- loadEvidence
  assumptions <- loadAssumptions
  exports <- loadExports
  uses <- loadUses
  verifyManifestIdentity
  mapM_ verifyRevision (Map.toList revisions)
  mapM_ (verifyEvidence assumptions) (Map.toList evidence)
  mapM_ verifyAssumption (Map.toList assumptions)
  mapM_ verifyExport (Map.toList exports)
  mapM_ verifyUseDigest (Map.toList uses)
  verifyDependencies evidence
  verifyProvenanceAcyclic revisions
  verifyAcyclic evidence
  mapM_ (verifyObligationClosure evidence exports) (Set.toAscList (manifestObligationRevisions manifest))
  mapM_ (verifyUse evidence) (Map.toList uses)
  where
    effectiveValidity :: Map Text Text
    effectiveValidity = Map.insert "target" (manifestTarget manifest)
      . Map.insert "compilation_profile" (manifestCompilationProfile manifest)
      $ manifestValidityContext manifest

    verifyBuildIdentity = do
      unless (manifestArchitectureDigest manifest == verificationArchitectureDigest context) $
        Left (BuildIdentityMismatch "architecture digest")
      unless (manifestPhilCoreDigest manifest == verificationPhilCoreDigest context) $
        Left (BuildIdentityMismatch "Phil Core digest")
      unless (manifestImplementationDigest manifest == verificationImplementationDigest context) $
        Left (BuildIdentityMismatch "implementation digest")
      unless (manifestTarget manifest == verificationTarget context) $
        Left (BuildIdentityMismatch "target")
      unless (manifestCompilationProfile manifest == verificationCompilationProfile context) $
        Left (BuildIdentityMismatch "compilation profile")
      unless (manifestLoweringLedgerRoot manifest == verificationLoweringLedgerRoot context) $
        Left (LoweringLedgerRootMismatch
          (verificationLoweringLedgerRoot context)
          (manifestLoweringLedgerRoot manifest))
      unless (manifestValidityContext manifest == verificationValidityContext context) $
        Left ValidityContextMismatch

    verifyManifestIdentity =
      let expected = deriveManifestId ledger manifest
      in unless (manifestId manifest == expected) $
          Left (ManifestIdentityMismatch expected (manifestId manifest))

    verifyManifestSets = do
      unless (manifestObligationRevisions manifest == verificationExpectedObligations context) $
        Left (ExpectedObligationSetMismatch
          (verificationExpectedObligations context)
          (manifestObligationRevisions manifest))
      mapM_ ensureScopeSubset (Set.toList (manifestCertificationScope manifest))
      where
        ensureScopeSubset revision =
          unless (Set.member revision (manifestObligationRevisions manifest)) $
            Left (CertificationScopeOutsideManifest revision)

    loadRevisions = fmap Map.fromList $ mapM load (Set.toAscList (manifestObligationRevisions manifest))
      where
        load key = case Map.lookup key (ledgerRevisions ledger) of
          Nothing -> Left (MissingRevision key)
          Just value -> Right (key, value)

    loadEvidence = fmap Map.fromList $ mapM load (Set.toAscList (manifestEvidenceEntries manifest))
      where
        load key = case Map.lookup key (ledgerEvidence ledger) of
          Nothing -> Left (MissingEvidenceEntry key)
          Just value -> Right (key, value)

    loadAssumptions = fmap Map.fromList $ mapM load (Set.toAscList (manifestAssumptionNodes manifest))
      where
        load key = case Map.lookup key (ledgerAssumptions ledger) of
          Nothing -> Left (MissingAssumption key)
          Just value -> Right (key, value)

    loadExports = fmap Map.fromList $ mapM load (Set.toAscList (manifestExports manifest))
      where
        load key = case Map.lookup key (ledgerExports ledger) of
          Nothing -> Left (MissingExport key)
          Just value -> Right (key, value)

    loadUses = fmap Map.fromList $ mapM load (Set.toAscList (manifestAssuranceUses manifest))
      where
        load key = case Map.lookup key (ledgerUses ledger) of
          Nothing -> Left (MissingAssuranceUse key)
          Just value -> Right (key, value)

    verifyRevision (key, revision) = do
      requireTextId "obligation" (unObligationId (revisionObligationId revision))
      requireTextId "revision" (unRevisionId key)
      unless (key == revisionId revision) $
        Left (RevisionMapKeyMismatch key (revisionId revision))
      let expectedDigest = digestText (revisionStatement revision)
      unless (revisionStatementDigest revision == expectedDigest) $
        Left (RevisionStatementDigestMismatch key expectedDigest (revisionStatementDigest revision))
      let expectedId = deriveRevisionId revision
      unless (revisionId revision == expectedId) $
        Left (RevisionIdentityMismatch expectedId (revisionId revision))
      unless (validAcceptanceRule (revisionAcceptanceRule revision)) $
        Left (InvalidAcceptanceRule key)
      mapM_ ensureGeneratedRevision (revisionGeneratedFrom revision)
      where
        ensureGeneratedRevision parent =
          unless (Set.member parent (manifestObligationRevisions manifest)) $
            Left (MissingObligationDependency (EvidenceEntryId "<revision-lineage>") parent)

    verifyEvidence assumptions (key, entry) = do
      requireTextId "evidence" (unEvidenceEntryId key)
      unless (key == evidenceEntryId entry) $
        Left (EvidenceMapKeyMismatch key (evidenceEntryId entry))
      let expectedDigest = deriveEvidenceEntryDigest entry
      unless (evidenceEntryDigest entry == expectedDigest) $
        Left (EvidenceDigestMismatch key expectedDigest (evidenceEntryDigest entry))
      unless (Set.member (evidenceObligationRevision entry) (manifestObligationRevisions manifest)) $
        Left (EvidenceOutsideManifestObligation key (evidenceObligationRevision entry))
      case evidenceResult entry of
        EvidenceAccepted -> Right ()
        EvidenceRejected reason -> Left (SelectedRejectedEvidence key reason)
      unless (scopeMatches (evidenceValidityScope entry)) $
        Left (EvidenceValidityScopeMismatch key)
      mapM_ (verifyEvidenceAssumption assumptions key) (evidenceAssumptions entry)
      mapM_ verifyArtifact (evidenceArtifact entry)
      verifyKindRequirements entry
      mapM_ (verifyCostRef key) (evidenceCostRefs entry)
      verifyEvidenceAuthorityKernel entry

    verifyEvidenceAssumption assumptions entryId assumptionKey = do
      unless (Set.member assumptionKey (manifestAssumptionNodes manifest)) $
        Left (UnselectedAssumptionDependency entryId assumptionKey)
      unless (Map.member assumptionKey assumptions) $
        Left (MissingAssumption assumptionKey)
      unless (Set.member assumptionKey (verificationPermittedAssumptions context)) $
        Left (UnpermittedAssumption assumptionKey)

    verifyAssumption (key, assumption) = do
      requireTextId "assumption" (unAssumptionId key)
      unless (key == assumptionId assumption) $
        Left (AssumptionMapKeyMismatch key (assumptionId assumption))
      let expectedDigest = deriveAssumptionDigest assumption
      unless (assumptionDigest assumption == expectedDigest) $
        Left (AssumptionDigestMismatch key expectedDigest (assumptionDigest assumption))
      unless (Set.member key (verificationPermittedAssumptions context)) $
        Left (UnpermittedAssumption key)
      unless (scopeMatches (assumptionValidityScope assumption)) $
        Left (AssumptionValidityScopeMismatch key)

    verifyExport (key, export) = do
      requireTextId "export" (unExportId key)
      unless (key == exportId export) $
        Left (ExportMapKeyMismatch key (exportId export))
      let expectedDigest = deriveExportDigest export
      unless (exportDigest export == expectedDigest) $
        Left (ExportDigestMismatch key expectedDigest (exportDigest export))
      unless (Set.member (exportObligationRevision export) (manifestObligationRevisions manifest)) $
        Left (ExportOutsideManifestObligation key (exportObligationRevision export))
      when (Set.member (exportObligationRevision export) (manifestCertificationScope manifest)) $
        Left (InScopeObligationExported (exportObligationRevision export))
      unless (Set.member (exportDestinationBoundary export) (verificationPermittedExportBoundaries context)) $
        Left (UnpermittedExportBoundary key (exportDestinationBoundary export))
      unless (scopeMatches (exportValidityScope export)) $
        Left (ExportValidityScopeMismatch key)

    verifyUseDigest (key, assuranceUse) = do
      requireTextId "assurance use" (unAssuranceUseId key)
      unless (key == assuranceUseId assuranceUse) $
        Left (AssuranceUseMapKeyMismatch key (assuranceUseId assuranceUse))
      let expectedDigest = deriveAssuranceUseDigest assuranceUse
      unless (assuranceUseDigest assuranceUse == expectedDigest) $
        Left (AssuranceUseDigestMismatch key expectedDigest (assuranceUseDigest assuranceUse))

    verifyDependencies evidence = mapM_ checkEntry (Map.elems evidence)
      where
        checkEntry entry = mapM_ (checkDependency (evidenceEntryId entry)) (evidenceDependsOn entry)
        checkDependency owner dependency = case dependency of
          DependsOnEvidence required ->
            unless (Map.member required evidence) $
              Left (MissingEvidenceDependency owner required)
          DependsOnObligation required -> do
            unless (Set.member required (manifestObligationRevisions manifest)) $
              Left (MissingObligationDependency owner required)
            unless (Set.member required (manifestCertificationScope manifest)) $
              Left (DependencyOnExportedObligation owner required)

    verifyProvenanceAcyclic revisions =
      case findCycle (provenanceEdges revisions) of
        Nothing -> Right ()
        Just cyclePath -> Left (ProvenanceCycle cyclePath)

    verifyAcyclic evidence =
      case findCycle (graphEdges ledger evidence manifest) of
        Nothing -> Right ()
        Just cyclePath -> Left (JustificationCycle cyclePath)

    verifyObligationClosure evidence exports revision
      | Set.member revision (manifestCertificationScope manifest) = do
          when (any ((== revision) . exportObligationRevision) (Map.elems exports)) $
            Left (InScopeObligationExported revision)
          accepted <- obligationAccepted evidence Set.empty revision
          unless accepted (Left (AcceptanceRuleUnsatisfied revision))
      | otherwise =
          case filter ((== revision) . exportObligationRevision) (Map.elems exports) of
            [] -> Left (OutOfScopeObligationNotExported revision)
            [_] -> Right ()
            _ -> Left (MultipleExportsForObligation revision)

    verifyUse evidence (key, assuranceUse) = do
      let revision = useObligationRevision assuranceUse
      unless (Set.member revision (manifestCertificationScope manifest)) $
        Left (AssuranceUseOutsideScope key revision)
      accepted <- obligationAccepted evidence Set.empty revision
      unless accepted (Left (AcceptanceRuleUnsatisfied revision))
      case assuranceUse of
        ErasureUse _ _ _ entries -> do
          when (null entries) (Left (ErasureWithoutEvidence key))
          mapM_ (verifyUseEvidence key revision evidence) entries
        RetainedRuntimeUse _ _ _ entryId costRef -> do
          verifyUseEvidence key revision evidence entryId
          entry <- case Map.lookup entryId evidence of
            Nothing -> Left (AssuranceUseMissingEvidence key entryId)
            Just value -> Right value
          unless (evidenceAssuranceKind entry == RuntimeEnforced) $
            Left (RuntimeUseRequiresRuntimeEvidence key entryId)
          unless (costRef `elem` evidenceCostRefs entry) $
            Left (RuntimeUseCostMismatch key costRef)
          unless (Set.member costRef (verificationKnownCostRefs context)) $
            Left (RuntimeUseCostMismatch key costRef)

    verifyUseEvidence useId revision evidence entryId =
      case Map.lookup entryId evidence of
        Nothing -> Left (AssuranceUseMissingEvidence useId entryId)
        Just entry -> do
          unless (evidenceObligationRevision entry == revision) $
            Left (AssuranceUseEvidenceMismatch useId entryId revision)
          usable <- evidenceUsable evidence Set.empty entryId
          unless usable (Left (AssuranceUseEvidenceMismatch useId entryId revision))

    obligationAccepted evidence visiting revision
      | Set.member (ObligationNode revision) visiting = Right False
      | otherwise = case Map.lookup revision (ledgerRevisions ledger) of
          Nothing -> Left (MissingRevision revision)
          Just obligationRevision ->
            evaluateRule evidence
              (Set.insert (ObligationNode revision) visiting)
              revision
              (revisionAcceptanceRule obligationRevision)

    evaluateRule evidence visiting revision rule = case rule of
      AcceptEntry kind expectedRole -> do
        candidates <- mapM candidate
          [ entryId
          | entryId <- Set.toAscList (manifestEvidenceEntries manifest)
          , Just entry <- [Map.lookup entryId evidence]
          , evidenceObligationRevision entry == revision
          , evidenceAssuranceKind entry == kind
          , evidenceRole entry == expectedRole
          ]
        Right (or candidates)
      AcceptAll rules -> and <$> mapM (evaluateRule evidence visiting revision) rules
      AcceptAny rules -> or <$> mapM (evaluateRule evidence visiting revision) rules
      where
        candidate entryId = evidenceUsable evidence visiting entryId

    evidenceUsable evidence visiting entryId
      | Set.member (EvidenceNode entryId) visiting = Right False
      | otherwise = case Map.lookup entryId evidence of
          Nothing -> Left (MissingEvidenceEntry entryId)
          Just entry -> do
            let visiting' = Set.insert (EvidenceNode entryId) visiting
            dependencies <- mapM (dependencyUsable evidence visiting' entryId) (evidenceDependsOn entry)
            Right (evidenceResult entry == EvidenceAccepted && and dependencies)

    dependencyUsable evidence visiting owner dependency = case dependency of
      DependsOnEvidence required ->
        case Map.lookup required evidence of
          Nothing -> Left (MissingEvidenceDependency owner required)
          Just _ -> evidenceUsable evidence visiting required
      DependsOnObligation required -> do
        unless (Set.member required (manifestCertificationScope manifest)) $
          Left (DependencyOnExportedObligation owner required)
        obligationAccepted evidence visiting required

    scopeMatches (ValidityScope dimensions) =
      case AssuranceValidityScopeKernel.decideValidityScope facts of
        AssuranceValidityScopeKernel.ValidityScopeAccepted -> all id facts
        AssuranceValidityScopeKernel.ValidityScopeRejected -> False
      where
        facts =
          [ Map.lookup key effectiveValidity == Just expected
          | (key, expected) <- Map.toList dimensions
          ]

    verifyArtifact artifact =
      case Map.lookup (artifactReference artifact) (verificationAvailableArtifacts context) of
        Nothing -> Left (MissingArtifact artifact)
        Just digest
          | digest == artifactDigest artifact -> Right ()
          | otherwise -> Left (ArtifactDigestMismatch
              (artifactReference artifact)
              digest
              (artifactDigest artifact))

    verifyKindRequirements entry = case evidenceAssuranceKind entry of
      ProofAssistantTheorem -> requireArtifact entry
      CertificateChecked -> requireArtifact entry
      TranslationValidated -> requireArtifact entry
      DifferentialTested -> requireArtifact entry
      PropertyTested -> requireArtifact entry
      RuntimeEnforced -> verifyRuntime entry
      Assumed -> verifyAssumed entry
      KernelChecked -> Right ()

    verifyEvidenceAuthorityKernel entry = case evidenceAssuranceKind entry of
      ProofAssistantTheorem -> verifyArtifactAuthorityKernel entry
      CertificateChecked -> verifyArtifactAuthorityKernel entry
      TranslationValidated -> verifyArtifactAuthorityKernel entry
      DifferentialTested -> verifyArtifactAuthorityKernel entry
      PropertyTested -> verifyArtifactAuthorityKernel entry
      RuntimeEnforced -> verifyRuntimeAuthorityKernel entry
      Assumed -> Right ()
      KernelChecked -> Right ()

    verifyArtifactAuthorityKernel entry =
      unless (artifactAuthorityKernelAccepts declared identityMatches digestMatches) $
        Left (EvidenceAuthorityKernelDisagreement
          (evidenceEntryId entry)
          (evidenceAssuranceKind entry))
      where
        declared = case evidenceArtifact entry of
          Nothing -> False
          Just _ -> True
        available = case evidenceArtifact entry of
          Nothing -> Nothing
          Just artifact -> Map.lookup
            (artifactReference artifact)
            (verificationAvailableArtifacts context)
        identityMatches = case available of
          Nothing -> False
          Just _ -> True
        digestMatches = case (evidenceArtifact entry, available) of
          (Just artifact, Just digest) -> digest == artifactDigest artifact
          _ -> False

    verifyRuntimeAuthorityKernel entry =
      unless (runtimeAuthorityKernelAccepts
        mechanismPresent
        mechanismComplete
        residuePresent
        costReferencePresent
        costReferenceKnown) $
          Left (EvidenceAuthorityKernelDisagreement
            (evidenceEntryId entry)
            (evidenceAssuranceKind entry))
      where
        mechanismPresent = case evidenceRuntimeMechanism entry of
          Nothing -> False
          Just _ -> True
        mechanismComplete = case evidenceRuntimeMechanism entry of
          Nothing -> False
          Just mechanism -> runtimeComplete mechanism
        residuePresent = not (null (evidenceRuntimeResidue entry))
        costReferencePresent = not (null (evidenceCostRefs entry))
        costReferenceKnown = all
          (\costRef -> Set.member costRef (verificationKnownCostRefs context))
          (evidenceCostRefs entry)

    requireArtifact entry = case evidenceArtifact entry of
      Nothing -> Left (EvidenceKindRequiresArtifact
        (evidenceEntryId entry)
        (evidenceAssuranceKind entry))
      Just _ -> Right ()

    verifyRuntime entry = do
      runtimeMechanism <- case evidenceRuntimeMechanism entry of
        Nothing -> Left (RuntimeEvidenceMissingMechanism (evidenceEntryId entry))
        Just value -> Right value
      when (null (evidenceRuntimeResidue entry)) $
        Left (RuntimeEvidenceMissingResidue (evidenceEntryId entry))
      when (null (evidenceCostRefs entry)) $
        Left (RuntimeEvidenceMissingCostRef (evidenceEntryId entry))
      unless (runtimeComplete runtimeMechanism) $
        Left (RuntimeMechanismIncomplete (evidenceEntryId entry))
      mapM_ verifyArtifact (runtimeImplementation runtimeMechanism)

    verifyAssumed entry = do
      when (null (evidenceAssumptions entry)) $
        Left (AssumedEvidenceMissingBoundary (evidenceEntryId entry))
      unless (evidenceRole entry == EvidenceRole "assumption_boundary") $
        Left (AssumedEvidenceMissingBoundary (evidenceEntryId entry))

    runtimeComplete runtimeMechanism = all (not . Text.null)
      [ runtimeMechanismName runtimeMechanism
      , runtimeExecutionPoint runtimeMechanism
      , runtimeSuccessEvidenceType runtimeMechanism
      , runtimeFailureContract runtimeMechanism
      ]

    verifyCostRef entryId costRef =
      unless (Set.member costRef (verificationKnownCostRefs context)) $
        Left (MissingCostReference entryId costRef)

    requireTextId label value =
      when (Text.null value) (Left (EmptyStableId label))

validAcceptanceRule :: AcceptanceRule -> Bool
validAcceptanceRule rule = case rule of
  AcceptEntry _ (EvidenceRole roleName) -> not (Text.null roleName)
  AcceptAll rules -> not (null rules) && all validAcceptanceRule rules
  AcceptAny rules -> not (null rules) && all validAcceptanceRule rules

provenanceEdges
  :: Map RevisionId ObligationRevision
  -> Map RevisionId [RevisionId]
provenanceEdges revisions = Map.fromList
  [ (revision, revisionGeneratedFrom obligationRevision)
  | (revision, obligationRevision) <- Map.toList revisions
  ]

graphEdges
  :: AssuranceLedger
  -> Map EvidenceEntryId EvidenceEntry
  -> AssuranceManifest
  -> Map GraphNode [GraphNode]
graphEdges _ledger evidence manifest = Map.fromListWith (<>)
  (obligationEvidenceEdges <> evidenceEdges)
  where
    obligationEvidenceEdges =
      [ (ObligationNode revision, [EvidenceNode entryId])
      | revision <- Set.toList (manifestObligationRevisions manifest)
      , (entryId, entry) <- Map.toList evidence
      , evidenceObligationRevision entry == revision
      ]

    evidenceEdges =
      [ (EvidenceNode entryId, map dependencyNode (evidenceDependsOn entry))
      | (entryId, entry) <- Map.toList evidence
      ]

    dependencyNode dependency = case dependency of
      DependsOnEvidence entryId -> EvidenceNode entryId
      DependsOnObligation revision -> ObligationNode revision

findCycle :: Ord node => Map node [node] -> Maybe [node]
findCycle edges = go Set.empty (Map.keys edges)
  where
    go _ [] = Nothing
    go permanent (node : rest)
      | Set.member node permanent = go permanent rest
      | otherwise = case visit permanent [] Set.empty node of
          Left cyclePath -> Just cyclePath
          Right permanent' -> go permanent' rest

    visit permanent path temporary node
      | Set.member node temporary = Left (reverse (node : takeUntil node path))
      | Set.member node permanent = Right permanent
      | otherwise = do
          let temporary' = Set.insert node temporary
              path' = node : path
          permanent' <- foldM
            (\current child -> visit current path' temporary' child)
            permanent
            (Map.findWithDefault [] node edges)
          Right (Set.insert node permanent')

    takeUntil _ [] = []
    takeUntil target (node : rest)
      | node == target = [node]
      | otherwise = node : takeUntil target rest
