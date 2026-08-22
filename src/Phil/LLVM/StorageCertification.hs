{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.StorageCertification
  ( StorageCertificationError (..)
  , StorageCertificationBundle (..)
  , phase0StorageLLVMCertification
  , verifyPhase0StorageLLVMCertification
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Assurance.Types
import Phil.Assurance.Verify (ManifestError, verifyManifest)
import Phil.Core.Syntax (ObligationId (..))
import Phil.LLVM.IR
import Phil.LLVM.Lower (lowerSystemsStorage)
import Phil.LLVM.Storage
import Phil.Systems.Storage
import Phil.Systems.Verify (SystemsVerificationContext (..))

data StorageCertificationError
  = StorageCertificationSystemsError StorageError
  | StorageCertificationTranslationError StorageLLVMError
  | StorageCertificationManifestError ManifestError
  deriving (Eq, Show)

data StorageCertificationBundle = StorageCertificationBundle
  { storageCertificationSystems :: StorageBundle
  , storageCertificationLLVM :: LLVMArtifact
  , storageCertificationArtifact :: ArtifactIdentity
  , storageCertificationLedger :: AssuranceLedger
  , storageCertificationManifest :: AssuranceManifest
  , storageCertificationContext :: VerificationContext
  }
  deriving (Eq, Show)

-- PHIL-LLVM-CERT-005
--
-- Content-bound to storage-v1. Runtime provider conformance, persistence
-- behavior, LLVM 18 acceptance, linking, and execution remain independent
-- external gates rather than claims of this pure translation certificate.
phase0StorageLLVMCertification
  :: Either StorageCertificationError StorageCertificationBundle
phase0StorageLLVMCertification = do
  systemsBundle <- mapLeft StorageCertificationSystemsError phase0StorageBundle
  let systemsArtifact = storageArtifact systemsBundle
      llvmArtifact = lowerSystemsStorage phase0StorageLLVMTarget systemsArtifact
  mapLeft StorageCertificationTranslationError $
    verifyStorageTranslation systemsBundle llvmArtifact
  let systemsManifest = systemsAssuranceManifest (storageContext systemsBundle)
      moduleValue = llvmArtifactModule llvmArtifact
      sourceDigest = llvmContractSourceDigest (llvmArtifactContract llvmArtifact)
      targetDigest = llvmContractTargetDigest (llvmArtifactContract llvmArtifact)
      targetTextDigest = digestText (llvmArtifactText llvmArtifact)
      abiDigest = llvmRuntimeABIDigest moduleValue
      certificationTarget = "preopt-llvm:" <> llvmTargetTriple moduleValue
      sourceCompilationProfile = Text.pack (show (llvmCompilationProfile moduleValue))
      certificationProfile =
        "translation-validation/" <> sourceCompilationProfile <> "/storage-v1"
      validityContext = Map.fromList
        [ ("source_digest", unDigest sourceDigest)
        , ("target_digest", unDigest targetDigest)
        , ("target_text_digest", unDigest targetTextDigest)
        , ("llvm_language", llvmLanguageVersion moduleValue)
        , ("llvm_tool_profile", llvmToolVersion moduleValue)
        , ("target_triple", llvmTargetTriple moduleValue)
        , ("data_layout", llvmDataLayout moduleValue)
        , ("runtime_abi_digest", unDigest abiDigest)
        , ("runtime_abi_profile", llvmRuntimeABIProfile moduleValue)
        , ("systems_compilation_profile", sourceCompilationProfile)
        , ("storage_abi", "phil_runtime_store(ptr)->{i8,ptr}")
        , ("storage_owner", "exact receive payload owner is transferred to store")
        , ("storage_ownership", "store consumes payload on success and failure")
        , ("storage_status", "only i8 status 1 is success; all other values fail closed")
        , ("upload_id_representation", "opaque runtime-managed nonowning ptr; no generated layout access/release")
        , ("upload_id_lifetime", "valid through calling component return")
        , ("storage_failure_upload_id", "null for conforming provider")
        , ("ambient_storage_state", "forbidden")
        , ("runtime_symbol_identity", "physical primitive/signature")
        , ("external_runtime_gate", "provider signatures, persistence bytes, ownership consumption, failure and reserved-status execution are checked independently in CI")
        , ("external_llvm_gate", "canonical target text must be accepted by LLVM 18 in CI")
        ]
      evidenceScope = ValidityScope $
        Map.insert "target" certificationTarget $
        Map.insert "compilation_profile" certificationProfile validityContext
      revisionStatement =
        "The canonical Phase 0 storage Systems -> pre-optimization LLVM pair is certified only for the exact source, target, target text, target profile, and phil-runtime/phase0/storage-v1 ABI bound by this revision; independent Phil translation validation establishes exact payload-owner transfer, opaque UploadId result identity and bounded lifetime, fail-closed storage status, and absence of post-transfer release or ambient storage state, while provider conformance, persistence behavior, LLVM 18 acceptance, linking, and execution remain external certification gates."
      provisionalRevision = ObligationRevision
        { revisionObligationId = ObligationId "PHIL-LLVM-CERT-005"
        , revisionId = RevisionId ""
        , revisionStatement = revisionStatement
        , revisionStatementDigest = digestText revisionStatement
        , revisionKind = "LLVMStorageTranslationCertification"
        , revisionOrigin = "storage ABI v1 / PHIL-LLVM-CERT-005"
        , revisionScope = "llvm.phase0.preopt.storage.translation"
        , revisionRequiredAt = "certification"
        , revisionRepresentation =
            "digest-validated SystemsArtifact -> owner-consuming storage canonical pre-optimization LLVMArtifact"
        , revisionSubjectIds =
            [ "systems:" <> unDigest sourceDigest
            , "llvm:" <> unDigest targetDigest
            , "llvm-text:" <> unDigest targetTextDigest
            , "runtime-abi:" <> unDigest abiDigest
            ]
        , revisionContextIds =
            [ "language:" <> llvmLanguageVersion moduleValue
            , "tool-profile:" <> llvmToolVersion moduleValue
            , "target:" <> llvmTargetTriple moduleValue
            , "layout:" <> llvmDataLayout moduleValue
            , "runtime-abi-profile:" <> llvmRuntimeABIProfile moduleValue
            , "compilation-profile:" <> sourceCompilationProfile
            ]
        , revisionAcceptanceRule = AcceptEntry
            TranslationValidated
            (EvidenceRole "translation_validated")
        , revisionGeneratedFrom = []
        }
      certificationRevision = provisionalRevision
        { revisionId = deriveRevisionId provisionalRevision }
      certificationRevisionId = revisionId certificationRevision
      translationArtifactRecord = Text.unlines
        [ "phil-llvm-phase0-storage-translation-validation-v1"
        , "source-digest=" <> unDigest sourceDigest
        , "target-digest=" <> unDigest targetDigest
        , "target-text-digest=" <> unDigest targetTextDigest
        , "llvm-language=" <> llvmLanguageVersion moduleValue
        , "llvm-tool-profile=" <> llvmToolVersion moduleValue
        , "target-triple=" <> llvmTargetTriple moduleValue
        , "data-layout=" <> llvmDataLayout moduleValue
        , "runtime-abi-digest=" <> unDigest abiDigest
        , "runtime-abi-profile=" <> llvmRuntimeABIProfile moduleValue
        , "translation-validator=Phil.LLVM.Storage.verifyStorageTranslation"
        , "assurance-checker=Phil.Assurance.Verify.verifyManifest"
        ]
      translationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef
            "artifact:phil:llvm:phase0:storage:translation-validation:v1"
        , artifactDigest = digestText translationArtifactRecord
        }
      evidenceId = EvidenceEntryId
        "evidence.llvm.phase0.storage.translation.validated"
      provisionalEvidence = EvidenceEntry
        { evidenceEntryId = evidenceId
        , evidenceEntryDigest = Digest ""
        , evidenceObligationRevision = certificationRevisionId
        , evidenceAssuranceKind = TranslationValidated
        , evidenceRole = EvidenceRole "translation_validated"
        , evidenceProducer = "Phil.LLVM.Storage.verifyStorageTranslation"
        , evidenceChecker = "Phil.Assurance.Verify.verifyManifest"
        , evidenceArtifact = Just translationArtifact
        , evidenceInputDigests =
            [ sourceDigest
            , targetDigest
            , targetTextDigest
            , abiDigest
            ]
        , evidenceAssumptions = []
        , evidenceDependsOn = []
        , evidenceValidityScope = evidenceScope
        , evidenceResult = EvidenceAccepted
        , evidenceJustifies =
            [ "exact storage payload-owner SSA identity"
            , "exact semantic UploadId result SSA identity"
            , "payload ownership transfers to store on all outcomes"
            , "only status 1 selects storage success"
            , "storage success/failure edges are exact"
            , "no generated post-transfer payload release"
            , "opaque UploadId has no generated layout access or release and is only relied on through component return"
            , "absence of ambient storage payload/UploadId state"
            , "physical runtime symbol identity"
            ]
        , evidenceRuntimeMechanism = Nothing
        , evidenceRuntimeResidue = []
        , evidenceCostRefs = []
        }
      translationEvidence = provisionalEvidence
        { evidenceEntryDigest = deriveEvidenceEntryDigest provisionalEvidence }
      ledger = emptyLedger
        { ledgerRevisions = Map.singleton certificationRevisionId certificationRevision
        , ledgerEvidence = Map.singleton evidenceId translationEvidence
        }
      certificationRoot = digestText $ Text.intercalate "|"
        [ "phil-llvm-phase0-storage-certification-root-v1"
        , unDigest sourceDigest
        , unDigest targetDigest
        , unDigest targetTextDigest
        , unDigest abiDigest
        ]
      provisionalManifest = emptyManifest
        { manifestArchitectureDigest = manifestArchitectureDigest systemsManifest
        , manifestPhilCoreDigest = manifestPhilCoreDigest systemsManifest
        , manifestImplementationDigest = artifactDigest translationArtifact
        , manifestTarget = certificationTarget
        , manifestCompilationProfile = certificationProfile
        , manifestObligationRevisions = Set.singleton certificationRevisionId
        , manifestCertificationScope = Set.singleton certificationRevisionId
        , manifestEvidenceEntries = Set.singleton evidenceId
        , manifestLoweringLedgerRoot = certificationRoot
        , manifestValidityContext = validityContext
        }
      manifest = provisionalManifest
        { manifestId = deriveManifestId ledger provisionalManifest }
      verificationContext = emptyVerificationContext
        { verificationArchitectureDigest = manifestArchitectureDigest systemsManifest
        , verificationPhilCoreDigest = manifestPhilCoreDigest systemsManifest
        , verificationImplementationDigest = artifactDigest translationArtifact
        , verificationTarget = certificationTarget
        , verificationCompilationProfile = certificationProfile
        , verificationExpectedObligations = Set.singleton certificationRevisionId
        , verificationAvailableArtifacts = Map.singleton
            (artifactReference translationArtifact)
            (artifactDigest translationArtifact)
        , verificationLoweringLedgerRoot = certificationRoot
        , verificationValidityContext = validityContext
        }
  pure StorageCertificationBundle
    { storageCertificationSystems = systemsBundle
    , storageCertificationLLVM = llvmArtifact
    , storageCertificationArtifact = translationArtifact
    , storageCertificationLedger = ledger
    , storageCertificationManifest = manifest
    , storageCertificationContext = verificationContext
    }

verifyPhase0StorageLLVMCertification :: Either StorageCertificationError ()
verifyPhase0StorageLLVMCertification = do
  bundle <- phase0StorageLLVMCertification
  mapLeft StorageCertificationManifestError $
    verifyManifest
      (storageCertificationContext bundle)
      (storageCertificationLedger bundle)
      (storageCertificationManifest bundle)

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
