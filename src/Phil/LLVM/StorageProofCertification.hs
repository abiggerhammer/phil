{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.StorageProofCertification
  ( StorageProofCertificationError (..)
  , StorageProofCertificationBundle (..)
  , phase0StorageProofCertification
  , verifyPhase0StorageProofCertification
  , renderStorageProofCertification
  ) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Rocq
import Phil.Assurance.RocqDigestValidation
import Phil.Assurance.RocqExactReceive
import Phil.Assurance.RocqRecognizedRecord
import Phil.Assurance.RocqStorage
import Phil.Assurance.Types
import Phil.Assurance.Verify (ManifestError, verifyManifest)
import Phil.Core.Syntax (ObligationId (..))
import Phil.LLVM.DigestValidationProofCertification
import Phil.LLVM.IR
import Phil.LLVM.StorageCertification
import Phil.Systems.IR
import Phil.Systems.Storage
import Phil.Systems.Verify (SystemsVerificationContext (..))

data StorageProofCertificationError
  = StorageProofCertificationBaseError StorageCertificationError
  | StorageProofCertificationPredecessorError DigestValidationProofCertificationError
  | StorageProofCertificationWrongProof Text ObligationId ObligationId
  | StorageProofCertificationProofManifestError Text ManifestError
  | StorageProofCertificationManifestError ManifestError
  deriving (Eq, Show)

data StorageProofCertificationBundle = StorageProofCertificationBundle
  { storageProofCertificationBase :: StorageCertificationBundle
  , storageProofCertificationPredecessor :: DigestValidationProofCertificationBundle
  , storageProofCertificationArtifact :: ArtifactIdentity
  , storageProofCertificationRecord :: Text
  , storageProofCertificationLedger :: AssuranceLedger
  , storageProofCertificationManifest :: AssuranceManifest
  , storageProofCertificationContext :: VerificationContext
  }
  deriving (Eq, Show)

phase0StorageProofCertification
  :: RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> Either StorageProofCertificationError StorageProofCertificationBundle
phase0StorageProofCertification
    systemsStorageProof llvmStorageProof
    systemsDigestProof llvmDigestProof systemsRecordProof exactProof abiProof symbolProof = do
  verifyProof "systems-storage" systemsStorageCertificationSpec systemsStorageProof
  verifyProof "llvm-storage" llvmStorageCertificationSpec llvmStorageProof
  verifyProof "systems-digest-validation" systemsDigestValidationCertificationSpec systemsDigestProof
  verifyProof "llvm-digest-validation" llvmDigestValidationCertificationSpec llvmDigestProof
  verifyProof "systems-recognized-record" systemsRecognizedRecordCertificationSpec systemsRecordProof
  verifyProof "llvm-exact-receive" llvmExactReceiveCertificationSpec exactProof
  verifyProof "llvm-recognized-record-abi" llvmRecognizedRecordABICertificationSpec abiProof
  verifyProof "llvm-runtime-symbol-identity" llvmRuntimeSymbolCertificationSpec symbolProof

  -- Reproduce proof-bound CERT-004 from the exact selected predecessor proof
  -- inputs, but do not import its digest-validation TranslationValidated
  -- evidence into the storage-v1 manifest.  The predecessor certificate digest
  -- is content-bound below while compatible proof authorities are selected
  -- directly in the new validity context.
  predecessor <- mapLeft StorageProofCertificationPredecessorError $
    phase0DigestValidationProofCertification
      systemsDigestProof llvmDigestProof systemsRecordProof exactProof abiProof symbolProof
  base <- mapLeft StorageProofCertificationBaseError phase0StorageLLVMCertification

  let explicitProofBundles =
        [ systemsStorageProof
        , llvmStorageProof
        , systemsDigestProof
        , llvmDigestProof
        , systemsRecordProof
        , exactProof
        , abiProof
        , symbolProof
        ]
      proofLedgers = map rocqBundleLedger explicitProofBundles
      semanticRevisions = Map.unions (map ledgerRevisions proofLedgers)
      semanticEvidence = Map.unions (map ledgerEvidence proofLedgers)
      semanticRevisionIds = Map.keysSet semanticRevisions
      semanticEvidenceIds = Map.keysSet semanticEvidence
      proofArtifacts = map rocqBundleCertificateArtifact explicitProofBundles
      proofDigests = map artifactDigest proofArtifacts
      predecessorArtifact = digestValidationProofCertificationArtifact predecessor

      systemsBundle = storageCertificationSystems base
      systemsArtifact = storageArtifact systemsBundle
      systemsManifest = systemsAssuranceManifest (storageContext systemsBundle)
      llvmArtifact = storageCertificationLLVM base
      moduleValue = llvmArtifactModule llvmArtifact
      translationArtifact = storageCertificationArtifact base
      sourceDigest = llvmContractSourceDigest (llvmArtifactContract llvmArtifact)
      targetDigest = llvmContractTargetDigest (llvmArtifactContract llvmArtifact)
      targetTextDigest = digestText (llvmArtifactText llvmArtifact)
      abiDigest = llvmRuntimeABIDigest moduleValue
      systemsLoweringRoot = loweringLedgerRoot (systemsArtifactLoweringLedger systemsArtifact)
      certificationTarget = "preopt-llvm:" <> llvmTargetTriple moduleValue
      sourceCompilationProfile = Text.pack (show (llvmCompilationProfile moduleValue))
      certificationProfile =
        "translation-validation/" <> sourceCompilationProfile <> "/storage-v1/proof-bound"
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
        , ("systems_lowering_ledger_root", unDigest systemsLoweringRoot)
        , ("storage_abi", "phil_runtime_store(ptr)->{i8,ptr}")
        , ("storage_owner", "exact digest/exact-receive payload owner is transferred to store")
        , ("storage_ownership", "store consumes payload ownership on success and failure; generated code performs no post-transfer release")
        , ("storage_status", "only exact i8 status 1 is success; every other status fails closed independently of UploadId pointer contents")
        , ("upload_id_representation", "opaque runtime-managed nonowning ptr; no generated layout access/release/strengthening")
        , ("upload_id_lifetime", "valid by identity through calling component return")
        , ("failure_upload_id_provider_rule", "conforming provider returns null on failure; external ABI/runtime conformance, not theorem premise")
        , ("predecessor_certification", unDigest (artifactDigest predecessorArtifact))
        , ("proof_assistant", "Rocq")
        , ("rocq_version", "9.2.0")
        , ("certificate_profile", "proof-assistant-theorem/v1")
        , ("external_llvm_gate", "canonical target text must be accepted by LLVM 18 in CI")
        , ("external_runtime_abi_gate", "provider signature and failure/null convention conformance must pass independently in CI")
        , ("external_persistence_gate", "persistence bytes, payload ownership consumption, ordinary failure, and reserved-status execution must pass independently in CI")
        ]
      evidenceScope = ValidityScope $
        Map.insert "target" certificationTarget $
        Map.insert "compilation_profile" certificationProfile validityContext
      revisionStatement =
        "The storage-v1 Systems -> canonical pre-optimization LLVM pair may be labeled Certified only when its exact source/target/text digests, lowering root, target/runtime-ABI/tool identities, exact Systems storage ownership proof, exact LLVM storage/UploadId proof, compatible predecessor semantic proof authorities, and translation-validation result are content-bound; proof-bound CERT-004 is exactly reproducible from the selected predecessor proofs and its certificate digest is bound without importing evidence outside its digest-validation validity scope; generated code accepts only exact status 1 and does not rely on failure UploadId pointer contents, while LLVM 18, provider ABI conformance including the conforming failure/null convention, persistence behavior, and payload ownership consumption remain explicit external gates; and the assurance manifest closes over all selected evidence."
      provisionalRevision = ObligationRevision
        { revisionObligationId = ObligationId "PHIL-LLVM-CERT-005"
        , revisionId = RevisionId ""
        , revisionStatement = revisionStatement
        , revisionStatementDigest = digestText revisionStatement
        , revisionKind = "LLVMStorageProofBoundCertification"
        , revisionOrigin = "storage ABI v1 / proof-bound PHIL-LLVM-CERT-005"
        , revisionScope = "llvm.phase0.preopt.storage.proof-bound"
        , revisionRequiredAt = "certification"
        , revisionRepresentation =
            "digest-validated owner-transferring SystemsArtifact -> storage-v1 canonical pre-optimization LLVMArtifact + proof authority"
        , revisionSubjectIds =
            [ "systems:" <> unDigest sourceDigest
            , "systems-lowering-root:" <> unDigest systemsLoweringRoot
            , "llvm:" <> unDigest targetDigest
            , "llvm-text:" <> unDigest targetTextDigest
            , "runtime-abi:" <> unDigest abiDigest
            , "predecessor-certification:" <> unDigest (artifactDigest predecessorArtifact)
            ] <> map ("proof-certificate:" <>) (map unDigest proofDigests)
        , revisionContextIds =
            [ "language:" <> llvmLanguageVersion moduleValue
            , "tool-profile:" <> llvmToolVersion moduleValue
            , "target:" <> llvmTargetTriple moduleValue
            , "layout:" <> llvmDataLayout moduleValue
            , "runtime-abi-profile:" <> llvmRuntimeABIProfile moduleValue
            , "compilation-profile:" <> sourceCompilationProfile
            , "rocq:9.2.0"
            ]
        , revisionAcceptanceRule = AcceptEntry
            TranslationValidated
            (EvidenceRole "translation_validated")
        , revisionGeneratedFrom = Set.toAscList semanticRevisionIds
        }
      certificationRevision = provisionalRevision
        { revisionId = deriveRevisionId provisionalRevision }
      certificationRevisionId = revisionId certificationRevision
      translationEvidenceId = EvidenceEntryId
        "evidence.llvm.phase0.storage.proof-bound.translation.validated"
      provisionalTranslationEvidence = EvidenceEntry
        { evidenceEntryId = translationEvidenceId
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
            , systemsLoweringRoot
            , artifactDigest predecessorArtifact
            ] <> proofDigests
        , evidenceAssumptions = []
        , evidenceDependsOn = map DependsOnObligation (Set.toAscList semanticRevisionIds)
        , evidenceValidityScope = evidenceScope
        , evidenceResult = EvidenceAccepted
        , evidenceJustifies =
            [ "exact digest-success -> storage boundary"
            , "exact payload-owner identity and one-way ownership transfer"
            , "exact semantic UploadId result identity"
            , "exact status==1 fail-closed storage branch"
            , "exact storage success/failure edges"
            , "no generated post-transfer payload release"
            , "opaque runtime-managed non-owning UploadId with bounded lifetime"
            , "absence of UploadId layout/release/unauthorized strengthening"
            , "absence of ambient storage payload/UploadId recovery"
            , "physical runtime symbol identity"
            , "content-bound reproduction of proof-bound digest predecessor authority"
            ]
        , evidenceRuntimeMechanism = Nothing
        , evidenceRuntimeResidue = []
        , evidenceCostRefs = []
        }
      translationEvidence = provisionalTranslationEvidence
        { evidenceEntryDigest = deriveEvidenceEntryDigest provisionalTranslationEvidence }
      certificationRecord = Text.unlines $
        [ "phil-llvm-phase0-storage-certification/v1"
        , "obligation=PHIL-LLVM-CERT-005"
        , "revision=" <> unRevisionId certificationRevisionId
        , "source-digest=" <> unDigest sourceDigest
        , "systems-lowering-root=" <> unDigest systemsLoweringRoot
        , "target-digest=" <> unDigest targetDigest
        , "target-text-digest=" <> unDigest targetTextDigest
        , "runtime-abi-profile=" <> llvmRuntimeABIProfile moduleValue
        , "runtime-abi-digest=" <> unDigest abiDigest
        , "translation-artifact=" <> renderArtifact translationArtifact
        , "predecessor-certification=" <> renderArtifact predecessorArtifact
        ] <> map renderProofArtifact explicitProofBundles <>
        [ "external-llvm-gate=LLVM 18 assembler acceptance required"
        , "external-runtime-abi-gate=provider signature and conforming failure/null convention required"
        , "external-persistence-gate=persistence bytes, owner consumption, failure and reserved-status execution required"
        ]
      certificationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef "certificate:phil:llvm:PHIL-LLVM-CERT-005:v1"
        , artifactDigest = digestText certificationRecord
        }
      revisions = Map.insert certificationRevisionId certificationRevision semanticRevisions
      evidence = Map.insert translationEvidenceId translationEvidence semanticEvidence
      ledger = emptyLedger
        { ledgerRevisions = revisions
        , ledgerEvidence = evidence
        }
      obligationIds = Set.insert certificationRevisionId semanticRevisionIds
      evidenceIds = Set.insert translationEvidenceId semanticEvidenceIds
      certificationRoot = digestText $ Text.intercalate "|" $
        [ "phil-llvm-phase0-storage-proof-bound-certification-root-v1"
        , unDigest sourceDigest
        , unDigest systemsLoweringRoot
        , unDigest targetDigest
        , unDigest targetTextDigest
        , unDigest abiDigest
        , unDigest (artifactDigest predecessorArtifact)
        ] <> map unDigest proofDigests
      provisionalManifest = emptyManifest
        { manifestArchitectureDigest = manifestArchitectureDigest systemsManifest
        , manifestPhilCoreDigest = manifestPhilCoreDigest systemsManifest
        , manifestImplementationDigest = artifactDigest certificationArtifact
        , manifestTarget = certificationTarget
        , manifestCompilationProfile = certificationProfile
        , manifestObligationRevisions = obligationIds
        , manifestCertificationScope = obligationIds
        , manifestEvidenceEntries = evidenceIds
        , manifestLoweringLedgerRoot = certificationRoot
        , manifestValidityContext = validityContext
        }
      manifest = provisionalManifest
        { manifestId = deriveManifestId ledger provisionalManifest }
      explicitArtifacts = translationArtifact : certificationArtifact : predecessorArtifact : proofArtifacts
      availableArtifacts = Map.fromList
        [ (artifactReference artifact, artifactDigest artifact)
        | artifact <- explicitArtifacts
        ]
      verificationContext = emptyVerificationContext
        { verificationArchitectureDigest = manifestArchitectureDigest systemsManifest
        , verificationPhilCoreDigest = manifestPhilCoreDigest systemsManifest
        , verificationImplementationDigest = artifactDigest certificationArtifact
        , verificationTarget = certificationTarget
        , verificationCompilationProfile = certificationProfile
        , verificationExpectedObligations = obligationIds
        , verificationAvailableArtifacts = availableArtifacts
        , verificationLoweringLedgerRoot = certificationRoot
        , verificationValidityContext = validityContext
        }
      bundle = StorageProofCertificationBundle
        { storageProofCertificationBase = base
        , storageProofCertificationPredecessor = predecessor
        , storageProofCertificationArtifact = certificationArtifact
        , storageProofCertificationRecord = certificationRecord
        , storageProofCertificationLedger = ledger
        , storageProofCertificationManifest = manifest
        , storageProofCertificationContext = verificationContext
        }

  mapLeft StorageProofCertificationManifestError $
    verifyManifest verificationContext ledger manifest
  pure bundle

verifyPhase0StorageProofCertification
  :: RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> Either StorageProofCertificationError ()
verifyPhase0StorageProofCertification
    systemsStorageProof llvmStorageProof
    systemsDigestProof llvmDigestProof systemsRecordProof exactProof abiProof symbolProof = do
  bundle <- phase0StorageProofCertification
    systemsStorageProof llvmStorageProof
    systemsDigestProof llvmDigestProof systemsRecordProof exactProof abiProof symbolProof
  mapLeft StorageProofCertificationManifestError $
    verifyManifest
      (storageProofCertificationContext bundle)
      (storageProofCertificationLedger bundle)
      (storageProofCertificationManifest bundle)

renderStorageProofCertification :: StorageProofCertificationBundle -> Text
renderStorageProofCertification = storageProofCertificationRecord

verifyProof
  :: Text
  -> RocqCertificationSpec
  -> RocqCertificationBundle
  -> Either StorageProofCertificationError ()
verifyProof label spec bundle = do
  let expected = rocqSpecObligation spec
      actual = rocqCertificateObligation (rocqBundleCertificate bundle)
  unless (actual == expected) $
    Left (StorageProofCertificationWrongProof label expected actual)
  mapLeft (StorageProofCertificationProofManifestError label) $
    verifyManifest
      (rocqBundleVerificationContext bundle)
      (rocqBundleLedger bundle)
      (rocqBundleManifest bundle)

renderArtifact :: ArtifactIdentity -> Text
renderArtifact artifact =
  unArtifactRef (artifactReference artifact) <> ";sha256=" <> unDigest (artifactDigest artifact)

renderProofArtifact :: RocqCertificationBundle -> Text
renderProofArtifact bundle =
  let certificate = rocqBundleCertificate bundle
      artifact = rocqBundleCertificateArtifact bundle
  in "proof=" <> unObligationId (rocqCertificateObligation certificate)
      <> ";artifact=" <> unArtifactRef (artifactReference artifact)
      <> ";sha256=" <> unDigest (artifactDigest artifact)

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
