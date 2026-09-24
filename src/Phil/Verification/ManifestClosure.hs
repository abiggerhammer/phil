{-# LANGUAGE OverloadedStrings #-}

module Phil.Verification.ManifestClosure
  ( ManifestClosureSelection (..)
  , ManifestClosureHandoff (..)
  , ManifestClosureError (..)
  , verificationDispositionForAssuranceKind
  , closeVerificationBundle
  , closeVerificationBundleWithHandoff
  ) where

import Control.Monad (foldM, unless)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Phil.Assurance.Handoff as Handoff
import Phil.Assurance.Types
import Phil.Assurance.Verify (ManifestError, verifyManifest)
import qualified Phil.Core.Discharge as Discharge
import Phil.Verification
  ( ApplicationAssurancePolicy (..)
  , AssurancePolicyRevision
  , VerificationDisposition (..)
  , VerificationObligationGraph (..)
  )
import Phil.Verification.Bundle
  ( AcceptedEvidenceReference (..)
  , VerificationBundle (..)
  , verificationBundleArchitectureDigest
  )

-- | Exact assurance artifacts selected to close one VerificationBundle.
-- Export disposition is explicit because ordinary and deployment export are
-- distinct ADR-025 policy choices even though both are represented by an
-- Assurance ExportEntry at the manifest layer.
data ManifestClosureSelection = ManifestClosureSelection
  { manifestClosureEvidence :: Set EvidenceEntryId
  , manifestClosureAssumptions :: Set AssumptionId
  , manifestClosureExports :: Map ExportId VerificationDisposition
  , manifestClosureUses :: Set AssuranceUseId
  }
  deriving (Eq, Show)

-- | Exact checker-to-assurance correspondence required when INT-002 closes
-- evidence produced from 'Phil.Assurance.Handoff'.  Every certificate or
-- direct named-evidence handoff in the supplied set must name the concrete
-- immutable evidence entry selected for that revision.  The closure path
-- checks the handoff revisions, semantic support graph, and finalized evidence
-- record rather than accepting a parallel reconstruction of checker support.
data ManifestClosureHandoff = ManifestClosureHandoff
  { manifestClosureHandoffEntries :: [Handoff.LedgerHandoff]
  , manifestClosureCertificateEvidence :: Map RevisionId EvidenceEntryId
  , manifestClosureDirectEvidence :: Map RevisionId EvidenceEntryId
  }
  deriving (Eq, Show)

data ManifestClosureError
  = ManifestClosurePolicyRevisionMismatch AssurancePolicyRevision AssurancePolicyRevision
  | ManifestClosureArchitectureDigestMismatch Digest Digest
  | ManifestClosureExpectedObligationsMismatch (Set RevisionId) (Set RevisionId)
  | ManifestClosureRevisionMissing RevisionId
  | ManifestClosureRevisionMismatch RevisionId
  | ManifestClosureAcceptedEvidenceMissing EvidenceEntryId
  | ManifestClosureAcceptedEvidenceMismatch EvidenceEntryId
  | ManifestClosureSelectedEvidenceMissing EvidenceEntryId
  | ManifestClosureSelectedAssumptionMissing AssumptionId
  | ManifestClosureSelectedExportMissing ExportId
  | ManifestClosureSelectedUseMissing AssuranceUseId
  | ManifestClosureMissingSelectedAssumptionDependency EvidenceEntryId AssumptionId
  | ManifestClosureUnusedAssumption AssumptionId
  | ManifestClosureInvalidExportDisposition ExportId VerificationDisposition
  | ManifestClosureUnpermittedDisposition VerificationDisposition
  | ManifestClosureHandoffDuplicateRevision RevisionId
  | ManifestClosureHandoffRevisionMissing RevisionId
  | ManifestClosureHandoffRevisionMismatch RevisionId
  | ManifestClosureHandoffSupportMismatch
      (Set (RevisionId, RevisionId))
      (Set (RevisionId, RevisionId))
  | ManifestClosureHandoffRequiredSupportOutOfScope RevisionId RevisionId
  | ManifestClosureHandoffEvidenceDomainMismatch
      (Set RevisionId)
      (Set RevisionId)
  | ManifestClosureHandoffDirectEvidenceDomainMismatch
      (Set RevisionId)
      (Set RevisionId)
  | ManifestClosureHandoffEvidenceNotSelected RevisionId EvidenceEntryId
  | ManifestClosureHandoffEvidenceMissing RevisionId EvidenceEntryId
  | ManifestClosureHandoffEvidenceRejected RevisionId EvidenceEntryId Handoff.HandoffError
  | ManifestClosureHandoffEvidenceMismatch RevisionId EvidenceEntryId
  | ManifestClosureManifestRejected ManifestError
  deriving (Eq, Show)

verificationDispositionForAssuranceKind
  :: AssuranceKind
  -> VerificationDisposition
verificationDispositionForAssuranceKind kind = case kind of
  KernelChecked -> StaticallyDischarged
  ProofAssistantTheorem -> ExternallyDischarged
  CertificateChecked -> ExternallyDischarged
  TranslationValidated -> ExternallyDischarged
  DifferentialTested -> ExternallyDischarged
  PropertyTested -> ExternallyDischarged
  RuntimeEnforced -> RuntimeBound
  Assumed -> AssumptionDependent

-- | Close an intrinsically accepted, canonical VerificationBundle through the
-- ordinary ADR-025 assurance machinery.  Witness identity is deliberately not
-- an input.  The bundle owns the exact obligation graph and policy revision;
-- the caller supplies only already-checked assurance artifacts and exact build
-- context.  Final acceptance is delegated to the existing manifest verifier.
closeVerificationBundle
  :: VerificationBundle
  -> ApplicationAssurancePolicy
  -> VerificationContext
  -> AssuranceLedger
  -> ManifestClosureSelection
  -> Either ManifestClosureError AssuranceManifest
closeVerificationBundle bundle policy context ledger selection = do
  verifyPolicyRevision
  verifyArchitectureDigest
  verifyContextObligations
  verifyBundleRevisions
  verifyBundleEvidenceReferences
  selectedEvidence <- loadSelectedEvidence
  verifySelectedEvidenceMembership
  selectedAssumptions <- loadSelectedAssumptions
  _selectedExports <- loadSelectedExports
  _selectedUses <- loadSelectedUses
  verifyAssumptionDependencies selectedEvidence
  verifyNoUnusedAssumptions selectedEvidence selectedAssumptions
  requiredDispositions <- selectedDispositions selectedEvidence
  mapM_ requirePermitted (Set.toAscList requiredDispositions)
  let provisional = emptyManifest
        { manifestArchitectureDigest = verificationArchitectureDigest context
        , manifestPhilCoreDigest = verificationPhilCoreDigest context
        , manifestImplementationDigest = verificationImplementationDigest context
        , manifestTarget = verificationTarget context
        , manifestCompilationProfile = verificationCompilationProfile context
        , manifestObligationRevisions = bundleObligations
        , manifestCertificationScope = verificationGraphCertificationScope graph
        , manifestEvidenceEntries = manifestClosureEvidence selection
        , manifestAssumptionNodes = manifestClosureAssumptions selection
        , manifestExports = Map.keysSet (manifestClosureExports selection)
        , manifestAssuranceUses = manifestClosureUses selection
        , manifestLoweringLedgerRoot = verificationLoweringLedgerRoot context
        , manifestValidityContext = verificationValidityContext context
        }
      manifest = provisional
        { manifestId = deriveManifestId ledger provisional }
  case verifyManifest context ledger manifest of
    Left err -> Left (ManifestClosureManifestRejected err)
    Right () -> Right manifest
  where
    graph = verificationBundleObligationGraph bundle
    bundleObligations = Map.keysSet (verificationGraphNodes graph)

    verifyPolicyRevision =
      let bundleRevision = verificationBundlePolicyRevision bundle
          selectedRevision = applicationAssurancePolicyRevision policy
      in if bundleRevision == selectedRevision
          then Right ()
          else Left
            (ManifestClosurePolicyRevisionMismatch bundleRevision selectedRevision)

    verifyArchitectureDigest =
      let expected = verificationBundleArchitectureDigest bundle
          actual = verificationArchitectureDigest context
      in if actual == expected
          then Right ()
          else Left (ManifestClosureArchitectureDigestMismatch expected actual)

    verifyContextObligations =
      let expected = verificationExpectedObligations context
      in if expected == bundleObligations
          then Right ()
          else Left
            (ManifestClosureExpectedObligationsMismatch bundleObligations expected)

    verifyBundleRevisions = mapM_ verifyOneRevision
      (Map.toAscList (verificationGraphNodes graph))

    verifyOneRevision (revisionKey, bundleRevision) =
      case Map.lookup revisionKey (ledgerRevisions ledger) of
        Nothing -> Left (ManifestClosureRevisionMissing revisionKey)
        Just ledgerRevision
          | ledgerRevision == bundleRevision -> Right ()
          | otherwise -> Left (ManifestClosureRevisionMismatch revisionKey)

    verifyBundleEvidenceReferences = mapM_ verifyOneReference
      (Map.toAscList (verificationBundleAcceptedEvidence bundle))

    verifySelectedEvidenceMembership = mapM_ verifySelected
      (Set.toAscList (manifestClosureEvidence selection))
      where
        accepted = verificationBundleAcceptedEvidence bundle
        verifySelected entryId =
          if Map.member entryId accepted
            then Right ()
            else Left (ManifestClosureAcceptedEvidenceMissing entryId)

    verifyOneReference (entryId, reference) =
      case Map.lookup entryId (ledgerEvidence ledger) of
        Nothing -> Left (ManifestClosureAcceptedEvidenceMissing entryId)
        Just entry
          | acceptedEvidenceEntryId reference /= entryId -> mismatch
          | acceptedEvidenceDigest reference /= evidenceEntryDigest entry -> mismatch
          | acceptedEvidenceObligationRevision reference /= evidenceObligationRevision entry -> mismatch
          | evidenceResult entry /= EvidenceAccepted -> mismatch
          | otherwise -> Right ()
      where
        mismatch = Left (ManifestClosureAcceptedEvidenceMismatch entryId)

    loadSelectedEvidence = fmap Map.fromList $ mapM load
      (Set.toAscList (manifestClosureEvidence selection))
      where
        load entryId = case Map.lookup entryId (ledgerEvidence ledger) of
          Nothing -> Left (ManifestClosureSelectedEvidenceMissing entryId)
          Just entry -> Right (entryId, entry)

    loadSelectedAssumptions = fmap Map.fromList $ mapM load
      (Set.toAscList (manifestClosureAssumptions selection))
      where
        load assumptionKey = case Map.lookup assumptionKey (ledgerAssumptions ledger) of
          Nothing -> Left (ManifestClosureSelectedAssumptionMissing assumptionKey)
          Just assumption -> Right (assumptionKey, assumption)

    loadSelectedExports = fmap Map.fromList $ mapM load
      (Map.toAscList (manifestClosureExports selection))
      where
        load (exportKey, disposition) = do
          if disposition `elem` [Exported, DeploymentExported]
            then Right ()
            else Left (ManifestClosureInvalidExportDisposition exportKey disposition)
          export <- case Map.lookup exportKey (ledgerExports ledger) of
            Nothing -> Left (ManifestClosureSelectedExportMissing exportKey)
            Just value -> Right value
          Right (exportKey, export)

    loadSelectedUses = fmap Map.fromList $ mapM load
      (Set.toAscList (manifestClosureUses selection)
      )
      where
        load useKey = case Map.lookup useKey (ledgerUses ledger) of
          Nothing -> Left (ManifestClosureSelectedUseMissing useKey)
          Just useValue -> Right (useKey, useValue)

    verifyAssumptionDependencies selectedEvidence = mapM_ verifyEntry
      (Map.toAscList selectedEvidence)
      where
        selectedAssumptionIds = manifestClosureAssumptions selection
        verifyEntry (entryId, entry) = mapM_ (verifyAssumption entryId)
          (evidenceAssumptions entry)
        verifyAssumption entryId assumptionKey =
          if Set.member assumptionKey selectedAssumptionIds
            then Right ()
            else Left
              (ManifestClosureMissingSelectedAssumptionDependency entryId assumptionKey)

    verifyNoUnusedAssumptions selectedEvidence selectedAssumptions = mapM_ verifyUsed
      (Map.keys selectedAssumptions)
      where
        used = Set.fromList
          [ assumptionKey
          | entry <- Map.elems selectedEvidence
          , assumptionKey <- evidenceAssumptions entry
          ]
        verifyUsed assumptionKey =
          if Set.member assumptionKey used
            then Right ()
            else Left (ManifestClosureUnusedAssumption assumptionKey)

    selectedDispositions selectedEvidence = do
      exportDispositions <- mapM validateExportDisposition
        (Map.toAscList (manifestClosureExports selection))
      let evidenceDispositions = concatMap evidenceDisposition
            (Map.elems selectedEvidence)
          assumptionDispositions =
            [ AssumptionDependent
            | not (Set.null (manifestClosureAssumptions selection))
            ]
      Right (Set.fromList
        (evidenceDispositions <> assumptionDispositions <> exportDispositions))

    validateExportDisposition (exportKey, disposition)
      | disposition `elem` [Exported, DeploymentExported] = Right disposition
      | otherwise = Left (ManifestClosureInvalidExportDisposition exportKey disposition)

    evidenceDisposition entry =
      verificationDispositionForAssuranceKind (evidenceAssuranceKind entry)
        : [AssumptionDependent | not (null (evidenceAssumptions entry))]

    requirePermitted disposition =
      if Set.member disposition
          (applicationAssurancePolicyPermittedDispositions policy)
        then Right ()
        else Left (ManifestClosureUnpermittedDisposition disposition)

-- | Close a bundle produced from checker handoff records.  This is the
-- INT-002 path for Core static evidence: it proves that the bundle graph and
-- selected ledger entries are the exact immutable projection of the supplied
-- handoff, then delegates all ordinary manifest checks to
-- 'closeVerificationBundle'.
--
-- Exactness is intentionally per support-bearing consumer. Resolver-required
-- prerequisite support is checked even when a parent closes by definition and
-- therefore has no static evidence record. A definitionally discharged parent
-- credited in the local certification scope must keep every retained
-- prerequisite in that scope; exporting a required child while retaining the
-- local parent would otherwise discard the operation-support contract.
-- Certificate and direct named-evidence consumers remain in the checked domain
-- even when their obligation support set is empty. Generation lineage is not
-- support; precise evidence dependencies stay in the evidence entry; and
-- unrelated evidence may remain selected for the same manifest.
closeVerificationBundleWithHandoff
  :: VerificationBundle
  -> ApplicationAssurancePolicy
  -> VerificationContext
  -> AssuranceLedger
  -> ManifestClosureSelection
  -> ManifestClosureHandoff
  -> Either ManifestClosureError AssuranceManifest
closeVerificationBundleWithHandoff bundle policy context ledger selection handoff = do
  entriesByRevision <- foldM insertHandoff Map.empty
    (manifestClosureHandoffEntries handoff)
  mapM_ verifyHandoffRevision (Map.toAscList entriesByRevision)
  let certificateEntries = Map.filter isCertificateHandoff entriesByRevision
      directEntries = Map.filter isDirectHandoff entriesByRevision
      definitionEntries = Map.filter isDefinitionHandoff entriesByRevision
      certificateRevisions = Map.keysSet certificateEntries
      directRevisions = Map.keysSet directEntries
      definitionRevisions = Map.keysSet definitionEntries
      suppliedEvidenceDomain = Map.keysSet
        (manifestClosureCertificateEvidence handoff)
      suppliedDirectEvidenceDomain = Map.keysSet
        (manifestClosureDirectEvidence handoff)
      handoffSupport = Handoff.handoffSupportEdges (Map.elems entriesByRevision)
      supportConsumers = certificateRevisions
        `Set.union` directRevisions
        `Set.union` Set.fromList
          [ consumer
          | (consumer, _) <- Set.toAscList handoffSupport
          ]
      expectedSupport = supportFor supportConsumers handoffSupport
      actualSupport = supportFor supportConsumers
        (verificationGraphDependencies graph)
  unless (expectedSupport == actualSupport) $
    Left (ManifestClosureHandoffSupportMismatch expectedSupport actualSupport)
  mapM_ (verifyDefinitionSupportClosure definitionRevisions)
    (Set.toAscList expectedSupport)
  unless (certificateRevisions == suppliedEvidenceDomain) $
    Left (ManifestClosureHandoffEvidenceDomainMismatch
      certificateRevisions suppliedEvidenceDomain)
  unless (directRevisions == suppliedDirectEvidenceDomain) $
    Left (ManifestClosureHandoffDirectEvidenceDomainMismatch
      directRevisions suppliedDirectEvidenceDomain)
  mapM_ (verifyCertificateEvidence certificateEntries)
    (Map.toAscList (manifestClosureCertificateEvidence handoff))
  mapM_ (verifyDirectEvidence directEntries)
    (Map.toAscList (manifestClosureDirectEvidence handoff))
  closeVerificationBundle bundle policy context ledger selection
  where
    graph = verificationBundleObligationGraph bundle

    insertHandoff entries entry =
      let revision = Handoff.handoffRevision entry
          revisionKey = revisionId revision
      in case Map.lookup revisionKey entries of
          Nothing -> Right (Map.insert revisionKey entry entries)
          Just _ -> Left (ManifestClosureHandoffDuplicateRevision revisionKey)

    verifyHandoffRevision (revisionKey, entry) =
      case Map.lookup revisionKey (verificationGraphNodes graph) of
        Nothing -> Left (ManifestClosureHandoffRevisionMissing revisionKey)
        Just graphRevision
          | graphRevision == Handoff.handoffRevision entry -> Right ()
          | otherwise -> Left (ManifestClosureHandoffRevisionMismatch revisionKey)

    isCertificateHandoff entry =
      case Handoff.handoffDisposition entry of
        Discharge.StaticallyDischarged Discharge.StaticByCertificate {} -> True
        _ -> False

    isDirectHandoff entry =
      case Handoff.handoffDisposition entry of
        Discharge.StaticallyDischarged (Discharge.StaticByEvidence _) -> True
        _ -> False

    isDefinitionHandoff entry =
      case Handoff.handoffDisposition entry of
        Discharge.StaticallyDischarged Discharge.StaticByDefinition -> True
        _ -> False

    verifyDefinitionSupportClosure definitionRevisions (consumer, required)
      | Set.member consumer definitionRevisions
      , Set.member consumer (verificationGraphCertificationScope graph)
      , not (Set.member required (verificationGraphCertificationScope graph)) =
          Left (ManifestClosureHandoffRequiredSupportOutOfScope consumer required)
      | otherwise = Right ()

    supportFor consumers = Set.filter
      (\(consumer, _) -> Set.member consumer consumers)

    verifyCertificateEvidence certificateEntries (revisionKey, entryId) = do
      unless (Set.member entryId (manifestClosureEvidence selection)) $
        Left (ManifestClosureHandoffEvidenceNotSelected revisionKey entryId)
      entry <- case Map.lookup entryId (ledgerEvidence ledger) of
        Nothing -> Left (ManifestClosureHandoffEvidenceMissing revisionKey entryId)
        Just value -> Right value
      certificateHandoff <- case Map.lookup revisionKey certificateEntries of
        Nothing -> Left (ManifestClosureHandoffEvidenceDomainMismatch
          (Map.keysSet certificateEntries)
          (Map.keysSet (manifestClosureCertificateEvidence handoff)))
        Just value -> Right value
      finalized <- case Handoff.bindHandoffCertificateEvidence certificateHandoff entry of
        Left err -> Left
          (ManifestClosureHandoffEvidenceRejected revisionKey entryId err)
        Right value -> Right value
      unless (finalized == entry) $
        Left (ManifestClosureHandoffEvidenceMismatch revisionKey entryId)

    verifyDirectEvidence directEntries (revisionKey, entryId) = do
      unless (Set.member entryId (manifestClosureEvidence selection)) $
        Left (ManifestClosureHandoffEvidenceNotSelected revisionKey entryId)
      entry <- case Map.lookup entryId (ledgerEvidence ledger) of
        Nothing -> Left (ManifestClosureHandoffEvidenceMissing revisionKey entryId)
        Just value -> Right value
      directHandoff <- case Map.lookup revisionKey directEntries of
        Nothing -> Left (ManifestClosureHandoffDirectEvidenceDomainMismatch
          (Map.keysSet directEntries)
          (Map.keysSet (manifestClosureDirectEvidence handoff)))
        Just value -> Right value
      finalized <- case Handoff.bindHandoffDirectEvidence directHandoff entry of
        Left err -> Left
          (ManifestClosureHandoffEvidenceRejected revisionKey entryId err)
        Right value -> Right value
      unless (finalized == entry) $
        Left (ManifestClosureHandoffEvidenceMismatch revisionKey entryId)
