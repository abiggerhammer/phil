{-# LANGUAGE OverloadedStrings #-}

module Phil.Verification.ManifestClosure
  ( ManifestClosureSelection (..)
  , ManifestClosureError (..)
  , closeVerificationBundle
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Phil.Assurance.Types
import Phil.Assurance.Verify (ManifestError, verifyManifest)
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
  | ManifestClosureManifestRejected ManifestError
  deriving (Eq, Show)

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
      (Set.toAscList (manifestClosureUses selection))
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
      primaryDisposition (evidenceAssuranceKind entry)
        : [AssumptionDependent | not (null (evidenceAssumptions entry))]

    primaryDisposition kind = case kind of
      KernelChecked -> StaticallyDischarged
      ProofAssistantTheorem -> ExternallyDischarged
      CertificateChecked -> ExternallyDischarged
      TranslationValidated -> ExternallyDischarged
      DifferentialTested -> ExternallyDischarged
      PropertyTested -> ExternallyDischarged
      RuntimeEnforced -> RuntimeBound
      Assumed -> AssumptionDependent

    requirePermitted disposition =
      if Set.member disposition
          (applicationAssurancePolicyPermittedDispositions policy)
        then Right ()
        else Left (ManifestClosureUnpermittedDisposition disposition)
