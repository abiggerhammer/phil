{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.StorageFailureDetailProofCertification
  ( llvmStorageFailureDetailCertificationSpec
  , StorageFailureDetailProofCertificationError (..)
  , StorageFailureDetailProofCertificationBundle (..)
  , phase0StorageFailureDetailProofCertification
  , verifyPhase0StorageFailureDetailProofCertification
  , renderStorageFailureDetailProofCertification
  ) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Rocq
import Phil.Assurance.Types
import Phil.Assurance.Verify (ManifestError, verifyManifest)
import Phil.Core.Syntax (ObligationId (..), unObligationId)
import Phil.LLVM.IR
import Phil.LLVM.StorageFailureDetail
import Phil.Systems.IR
import Phil.Systems.StorageFailure
import Phil.Systems.Verify (SystemsVerificationContext (..))

llvmStorageFailureDetailCertificationSpec :: RocqCertificationSpec
llvmStorageFailureDetailCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "llvm-storage-failure-detail"
  , rocqSpecObligation = ObligationId "PHIL-LLVM-STORAGE-FAIL-DETAIL-001"
  , rocqSpecClaim =
      "For storage-failure-detail-v1 over the certified storage-failure-detail-v1 Systems source, verified lowering preserves the proof-bound Server Framed Ingress predecessor; replaces storage with exactly one explicit phil_runtime_store_with_error call carrying the exact payload owner and exact UploadId/StorageError output identities on the exact source-derived branches; null-initializes both result slots before the provider call; forwards the exact provider-produced StorageError with the exact server transport into the terminal storage-failure effect; preserves the fatal StorageFailure outcome; introduces no generated post-transfer payload observation or cleanup; eliminates the legacy store/error-materialization/failure-effect forms and ambient storage state; and claims no provider-side payload-consumption theorem, provider status/output correctness, concrete StorageError layout/lifetime, physical I/O, or wire codec."
  , rocqSpecKind = "LLVM storage-failure detail ABI v1"
  , rocqSpecOrigin =
      "src/Phil/LLVM/StorageFailureDetail.hs; docs/phase-0/storage-failure-detail-abi-v1.md; proof/Phil/LLVM/StorageFailureDetail.v"
  , rocqSpecScope = "Phil.LLVM storage-failure-detail-v1 over storage-failure-detail-v1 Systems authority"
  , rocqSpecRepresentation =
      "explicit payload/upload-id/storage-error store operands and output slots + exact terminal storage-error forwarding after ownership transfer"
  , rocqSpecSubjects =
      [ "phil_runtime_store_with_error(ptr,ptr,ptr)->i8"
      , "exact server.payload.owner"
      , "exact server.upload_id output slot"
      , "exact server.storage_error output slot"
      , "compiler null initialization of both output slots"
      , "phil_runtime_fail_storage(ptr,ptr)->void"
      ]
  , rocqSpecTheorems =
      [ "verified_llvm_storage_failure_detail_reuses_source_and_predecessor_authority"
      , "verified_llvm_storage_failure_detail_preserves_exact_store_operands_and_edges"
      , "verified_llvm_storage_failure_detail_initializes_both_output_slots"
      , "verified_llvm_storage_failure_detail_forwards_exact_error_on_exact_transport"
      , "verified_llvm_storage_failure_detail_does_not_reobserve_transferred_payload"
      , "verified_llvm_storage_failure_detail_eliminates_legacy_and_ambient_state"
      , "verified_llvm_storage_failure_detail_claims_no_provider_or_wire_semantics"
      , "llvm_storage_failure_detail_identity_or_slot_drift_is_rejected"
      , "llvm_storage_failure_detail_payload_reuse_or_ambient_drift_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/LLVM/StorageFailureDetail.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/LLVM/StorageFailureDetail.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-LLVM-STORAGE-FAIL-DETAIL-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-LLVM-STORAGE-FAIL-DETAIL-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness; reviewed storage-failure Systems/LLVM-to-normalized-proof correspondence; provider correctness for store status/output-slot semantics and payload consumption; opaque UploadId/StorageError representation and lifetime; terminal fail-storage runtime behavior; physical I/O; target calling convention; LLVM 18; linking/native execution; and wire framing remain explicit trust boundaries or external gates."
  }

data StorageFailureDetailProofCertificationError
  = StorageFailureDetailProofSystemsError StorageFailureError
  | StorageFailureDetailProofTranslationError StorageFailureDetailLLVMError
  | StorageFailureDetailProofWrongProof ObligationId ObligationId
  | StorageFailureDetailProofManifestError Text ManifestError
  | StorageFailureDetailProofFinalManifestError ManifestError
  deriving (Eq, Show)

data StorageFailureDetailProofCertificationBundle = StorageFailureDetailProofCertificationBundle
  { storageFailureDetailProofSystems :: StorageFailureBundle
  , storageFailureDetailProofLLVM :: LLVMArtifact
  , storageFailureDetailProofArtifact :: ArtifactIdentity
  , storageFailureDetailProofRecord :: Text
  , storageFailureDetailProofLedger :: AssuranceLedger
  , storageFailureDetailProofManifest :: AssuranceManifest
  , storageFailureDetailProofContext :: VerificationContext
  }
  deriving (Eq, Show)

proofBoundCert015 :: ArtifactIdentity
proofBoundCert015 = ArtifactIdentity
  { artifactReference = ArtifactRef "certificate:phil:llvm:PHIL-LLVM-CERT-015:v1"
  , artifactDigest = Digest "cbf94a07d57e44d35db8270e423d077c9ccca5695d304595fd2b41b04f5e1d73"
  }

phase0StorageFailureDetailProofCertification
  :: RocqCertificationBundle
  -> Either StorageFailureDetailProofCertificationError StorageFailureDetailProofCertificationBundle
phase0StorageFailureDetailProofCertification llvmProof = do
  verifyProof llvmStorageFailureDetailCertificationSpec llvmProof
  systemsBundle <- mapLeft StorageFailureDetailProofSystemsError phase0StorageFailureBundle
  let systemsArtifact = storageFailureArtifact systemsBundle
      llvmArtifact = lowerSystemsStorageFailureDetail
        phase0StorageFailureDetailLLVMTarget
        systemsArtifact
  mapLeft StorageFailureDetailProofTranslationError $
    verifyStorageFailureDetailTranslation systemsBundle llvmArtifact

  let proofLedger = rocqBundleLedger llvmProof
      proofRevisionId = rocqCertificateRevision (rocqBundleCertificate llvmProof)
      proofArtifact = rocqBundleCertificateArtifact llvmProof
      proofDigest = artifactDigest proofArtifact
      systemsManifest = systemsAssuranceManifest (storageFailureContext systemsBundle)
      moduleValue = llvmArtifactModule llvmArtifact
      sourceDigest = llvmContractSourceDigest (llvmArtifactContract llvmArtifact)
      targetDigest = llvmContractTargetDigest (llvmArtifactContract llvmArtifact)
      targetTextDigest = digestText (llvmArtifactText llvmArtifact)
      abiDigest = llvmRuntimeABIDigest moduleValue
      systemsLoweringRoot = loweringLedgerRoot (systemsArtifactLoweringLedger systemsArtifact)
      certificationTarget = "preopt-llvm:" <> llvmTargetTriple moduleValue
      sourceCompilationProfile = Text.pack (show (llvmCompilationProfile moduleValue))
      certificationProfile =
        "translation-validation/" <> sourceCompilationProfile <>
        "/storage-failure-detail-v1/storage-failure-detail-v1/proof-bound"
      validityContext = Map.fromList
        [ ("source_successor", "storage-failure-detail-v1")
        , ("source_digest", unDigest sourceDigest)
        , ("systems_lowering_ledger_root", unDigest systemsLoweringRoot)
        , ("target_digest", unDigest targetDigest)
        , ("target_text_digest", unDigest targetTextDigest)
        , ("llvm_language", llvmLanguageVersion moduleValue)
        , ("llvm_tool_profile", llvmToolVersion moduleValue)
        , ("target_triple", llvmTargetTriple moduleValue)
        , ("data_layout", llvmDataLayout moduleValue)
        , ("runtime_abi_digest", unDigest abiDigest)
        , ("runtime_abi_profile", llvmRuntimeABIProfile moduleValue)
        , ("systems_compilation_profile", sourceCompilationProfile)
        , ("predecessor_cert015", unDigest (artifactDigest proofBoundCert015))
        , ("proof_certificate", unDigest proofDigest)
        , ("proof_assistant", "Rocq")
        , ("rocq_version", "9.2.0")
        , ("certificate_profile", "proof-assistant-theorem/v1")
        , ("store_identity", "exact payload owner + UploadId output + StorageError output")
        , ("slot_initialization", "compiler writes null to both output slots before provider call")
        , ("failure_effect", "exact server transport + exact provider-produced StorageError")
        , ("payload_after_store", "no generated observation/release/cleanup")
        , ("provider_store_semantics", "external runtime ABI gate")
        , ("wire_codec", "outside this target scope")
        ]
      evidenceScope = ValidityScope $
        Map.insert "target" certificationTarget $
        Map.insert "compilation_profile" certificationProfile validityContext
      revisionStatement =
        "The storage-failure-detail-v1 lowering over the storage-failure-detail-v1 Systems source may be labeled Certified only when the exact source/target/text digests, Systems lowering root, target/runtime-ABI/tool identities, proof-bound PHIL-LLVM-CERT-015 predecessor artifact, PHIL-LLVM-STORAGE-FAIL-DETAIL-001 proof authority, and exact translation-validation result are content-bound. The target passes the exact transferred payload owner into the explicit store-with-error ABI, preserves exact UploadId and StorageError output identities and exact source-derived branches, null-initializes both output slots before the provider call, forwards the exact StorageError with the exact server transport into the terminal StorageFailure effect, introduces no generated post-transfer payload observation, and preserves the proof-bound server-framed-ingress predecessor. Provider-side payload consumption, status/output-slot correctness, opaque handle representation/lifetime, physical I/O, LLVM implementation correctness, linking/native execution, and wire framing remain external gates or TCB components."
      provisionalRevision = ObligationRevision
        { revisionObligationId = ObligationId "PHIL-LLVM-CERT-016"
        , revisionId = RevisionId ""
        , revisionStatement = revisionStatement
        , revisionStatementDigest = digestText revisionStatement
        , revisionKind = "LLVMStorageFailureDetailProofBoundCertification"
        , revisionOrigin = "storage-failure-detail ABI v1 / proof-bound PHIL-LLVM-CERT-016"
        , revisionScope = "llvm.phase0.preopt.storage-failure-detail.proof-bound"
        , revisionRequiredAt = "certification"
        , revisionRepresentation =
            "storage-failure-detail-v1 SystemsArtifact -> storage-failure-detail-v1 canonical pre-optimization LLVMArtifact + proof authority"
        , revisionSubjectIds =
            [ "systems:" <> unDigest sourceDigest
            , "systems-lowering-root:" <> unDigest systemsLoweringRoot
            , "llvm:" <> unDigest targetDigest
            , "llvm-text:" <> unDigest targetTextDigest
            , "runtime-abi:" <> unDigest abiDigest
            , "predecessor-cert015:" <> unDigest (artifactDigest proofBoundCert015)
            , "proof-certificate:" <> unDigest proofDigest
            ]
        , revisionContextIds =
            [ "language:" <> llvmLanguageVersion moduleValue
            , "tool-profile:" <> llvmToolVersion moduleValue
            , "target:" <> llvmTargetTriple moduleValue
            , "layout:" <> llvmDataLayout moduleValue
            , "runtime-abi-profile:" <> llvmRuntimeABIProfile moduleValue
            , "compilation-profile:" <> sourceCompilationProfile
            , "source-successor:storage-failure-detail-v1"
            , "rocq:9.2.0"
            ]
        , revisionAcceptanceRule = AcceptEntry TranslationValidated (EvidenceRole "translation_validated")
        , revisionGeneratedFrom = [proofRevisionId]
        }
      certificationRevision = provisionalRevision
        { revisionId = deriveRevisionId provisionalRevision }
      certificationRevisionId = revisionId certificationRevision
      translationArtifactRecord = Text.unlines
        [ "phil-llvm-phase0-storage-failure-detail-translation-validation/v1"
        , "source-successor=storage-failure-detail-v1"
        , "source-digest=" <> unDigest sourceDigest
        , "systems-lowering-root=" <> unDigest systemsLoweringRoot
        , "target-digest=" <> unDigest targetDigest
        , "target-text-digest=" <> unDigest targetTextDigest
        , "runtime-abi-profile=" <> llvmRuntimeABIProfile moduleValue
        , "runtime-abi-digest=" <> unDigest abiDigest
        , "predecessor-cert015=" <> unDigest (artifactDigest proofBoundCert015)
        , "proof-certificate=" <> unDigest proofDigest
        , "translation-validator=Phil.LLVM.StorageFailureDetail.verifyStorageFailureDetailTranslation"
        ]
      translationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef
            "artifact:phil:llvm:phase0:storage-failure-detail:translation-validation:v1"
        , artifactDigest = digestText translationArtifactRecord
        }
      evidenceId = EvidenceEntryId
        "evidence.llvm.phase0.storage-failure-detail.proof-bound.translation.validated"
      provisionalEvidence = EvidenceEntry
        { evidenceEntryId = evidenceId
        , evidenceEntryDigest = Digest ""
        , evidenceObligationRevision = certificationRevisionId
        , evidenceAssuranceKind = TranslationValidated
        , evidenceRole = EvidenceRole "translation_validated"
        , evidenceProducer = "Phil.LLVM.StorageFailureDetail.verifyStorageFailureDetailTranslation"
        , evidenceChecker = "Phil.Assurance.Verify.verifyManifest"
        , evidenceArtifact = Just translationArtifact
        , evidenceInputDigests =
            [ sourceDigest
            , systemsLoweringRoot
            , targetDigest
            , targetTextDigest
            , abiDigest
            , artifactDigest proofBoundCert015
            , proofDigest
            ]
        , evidenceAssumptions = []
        , evidenceDependsOn = [DependsOnObligation proofRevisionId]
        , evidenceValidityScope = evidenceScope
        , evidenceResult = EvidenceAccepted
        , evidenceJustifies =
            [ "store-with-error receives the exact transferred payload-owner identity"
            , "UploadId and StorageError outputs preserve the exact semantic identities"
            , "store success/failure edges remain the exact source-derived branches"
            , "both output slots are null-initialized before the provider call"
            , "storage failure forwards the exact StorageError with the exact server transport"
            , "the generated failure path does not observe, release, or clean up the transferred payload"
            , "proof-bound Server Framed Ingress predecessor remains physically preserved"
            , "legacy/ambient storage-failure state is absent"
            , "provider store semantics, handle lifetime, physical I/O and wire framing remain external"
            ]
        , evidenceRuntimeMechanism = Nothing
        , evidenceRuntimeResidue = []
        , evidenceCostRefs = []
        }
      translationEvidence = provisionalEvidence
        { evidenceEntryDigest = deriveEvidenceEntryDigest provisionalEvidence }
      certificationRecord = Text.unlines
        [ "phil-llvm-phase0-storage-failure-detail-certification/v1"
        , "obligation=PHIL-LLVM-CERT-016"
        , "revision=" <> unRevisionId certificationRevisionId
        , "source-successor=storage-failure-detail-v1"
        , "source-digest=" <> unDigest sourceDigest
        , "systems-lowering-root=" <> unDigest systemsLoweringRoot
        , "target-digest=" <> unDigest targetDigest
        , "target-text-digest=" <> unDigest targetTextDigest
        , "runtime-abi-profile=" <> llvmRuntimeABIProfile moduleValue
        , "runtime-abi-digest=" <> unDigest abiDigest
        , "translation-artifact=" <> renderArtifact translationArtifact
        , "predecessor-cert015=" <> renderArtifact proofBoundCert015
        , "proof=" <> unObligationId (rocqCertificateObligation (rocqBundleCertificate llvmProof))
            <> ";artifact=" <> unArtifactRef (artifactReference proofArtifact)
            <> ";sha256=" <> unDigest proofDigest
        , "external-store-provider=payload consumption + status/output-slot semantics"
        , "external-handle-semantics=UploadId/StorageError representation and lifetime"
        , "external-llvm=LLVM 18 acceptance/link gate"
        , "wire-codec=outside storage-failure-detail-v1 compiler scope"
        ]
      certificationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef "certificate:phil:llvm:PHIL-LLVM-CERT-016:v1"
        , artifactDigest = digestText certificationRecord
        }
      revisions = Map.insert certificationRevisionId certificationRevision
        (ledgerRevisions proofLedger)
      evidence = Map.insert evidenceId translationEvidence (ledgerEvidence proofLedger)
      obligationIds = Set.insert certificationRevisionId (Map.keysSet (ledgerRevisions proofLedger))
      evidenceIds = Set.insert evidenceId (Map.keysSet (ledgerEvidence proofLedger))
      ledger = emptyLedger { ledgerRevisions = revisions, ledgerEvidence = evidence }
      certificationRoot = digestText $ Text.intercalate "|"
        [ "phil-llvm-phase0-storage-failure-detail-proof-bound-certification-root-v1"
        , unDigest sourceDigest
        , unDigest systemsLoweringRoot
        , unDigest targetDigest
        , unDigest targetTextDigest
        , unDigest abiDigest
        , unDigest (artifactDigest proofBoundCert015)
        , unDigest proofDigest
        ]
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
      explicitArtifacts = [translationArtifact, certificationArtifact, proofBoundCert015, proofArtifact]
      availableArtifacts = Map.fromList
        [ (artifactReference artifact, artifactDigest artifact)
        | artifact <- explicitArtifacts
        ]
      context = emptyVerificationContext
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
      result = StorageFailureDetailProofCertificationBundle
        { storageFailureDetailProofSystems = systemsBundle
        , storageFailureDetailProofLLVM = llvmArtifact
        , storageFailureDetailProofArtifact = certificationArtifact
        , storageFailureDetailProofRecord = certificationRecord
        , storageFailureDetailProofLedger = ledger
        , storageFailureDetailProofManifest = manifest
        , storageFailureDetailProofContext = context
        }

  mapLeft StorageFailureDetailProofFinalManifestError $ verifyManifest context ledger manifest
  pure result

verifyPhase0StorageFailureDetailProofCertification
  :: RocqCertificationBundle
  -> Either StorageFailureDetailProofCertificationError ()
verifyPhase0StorageFailureDetailProofCertification proofBundle = do
  bundle <- phase0StorageFailureDetailProofCertification proofBundle
  mapLeft StorageFailureDetailProofFinalManifestError $
    verifyManifest
      (storageFailureDetailProofContext bundle)
      (storageFailureDetailProofLedger bundle)
      (storageFailureDetailProofManifest bundle)

renderStorageFailureDetailProofCertification
  :: StorageFailureDetailProofCertificationBundle
  -> Text
renderStorageFailureDetailProofCertification = storageFailureDetailProofRecord

verifyProof
  :: RocqCertificationSpec
  -> RocqCertificationBundle
  -> Either StorageFailureDetailProofCertificationError ()
verifyProof spec bundle = do
  let expected = rocqSpecObligation spec
      actual = rocqCertificateObligation (rocqBundleCertificate bundle)
  unless (actual == expected) $
    Left (StorageFailureDetailProofWrongProof expected actual)
  mapLeft (StorageFailureDetailProofManifestError "llvm-storage-failure-detail") $
    verifyManifest
      (rocqBundleVerificationContext bundle)
      (rocqBundleLedger bundle)
      (rocqBundleManifest bundle)

renderArtifact :: ArtifactIdentity -> Text
renderArtifact artifact =
  unArtifactRef (artifactReference artifact) <> ";sha256=" <> unDigest (artifactDigest artifact)

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
