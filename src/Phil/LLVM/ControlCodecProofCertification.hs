{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.ControlCodecProofCertification
  ( llvmControlCodecCertificationSpec
  , ControlCodecProofCertificationError (..)
  , ControlCodecProofCertificationBundle (..)
  , phase0ControlCodecProofCertification
  , verifyPhase0ControlCodecProofCertification
  , renderControlCodecProofCertification
  ) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.ControlCodecTestEvidence
import Phil.Assurance.Rocq
import Phil.Assurance.TestEvidenceCertification
import Phil.Assurance.Types
import Phil.Assurance.Verify (ManifestError, verifyManifest)
import Phil.Core.Syntax (ObligationId (..), unObligationId)
import Phil.LLVM.ControlCodec
import Phil.LLVM.IR
import Phil.Systems.IR
import Phil.Systems.StorageFailure
import Phil.Systems.Verify (SystemsVerificationContext (..))

llvmControlCodecCertificationSpec :: RocqCertificationSpec
llvmControlCodecCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "llvm-control-codec"
  , rocqSpecObligation = ObligationId "PHIL-LLVM-CONTROL-CODEC-001"
  , rocqSpecClaim =
      "For control-codec-v1 over the certified storage-failure-detail-v1 Systems source, verified lowering preserves the proof-bound CERT-016 predecessor function bodies and strengthenings exactly, changes only the runtime ABI profile/digest to the exact control-codec-v1 descriptor, retains the explicit client/server/store primitive declarations required by the predecessor physical chain, eliminates the legacy storage-failure-detail runtime-profile identity from the rendered target, and requires concrete native codec behavior to be established by separate content-bound runtime evidence rather than by this theorem."
  , rocqSpecKind = "LLVM control-codec runtime-profile preservation v1"
  , rocqSpecOrigin =
      "src/Phil/LLVM/ControlCodec.hs; docs/phase-0/control-codec-v1.md; proof/Phil/LLVM/ControlCodec.v"
  , rocqSpecScope = "Phil.LLVM control-codec-v1 over storage-failure-detail-v1 Systems authority"
  , rocqSpecRepresentation =
      "storage-failure-detail-v1 function bodies/strengthenings preserved exactly while runtime ABI profile/digest selects the concrete shared control codec"
  , rocqSpecSubjects =
      [ "exact predecessor LLVM function bodies"
      , "exact predecessor LLVM strengthenings"
      , "phil-runtime/phase0/control-codec-v1"
      , "controlCodecABIDescriptor digest"
      , "explicit Hello/Begin send and receive/recognize declarations"
      , "explicit detailed storage declarations"
      , "legacy storage-failure-detail runtime-profile absence"
      ]
  , rocqSpecTheorems =
      [ "verified_llvm_control_codec_reuses_source_and_cert016_predecessor"
      , "verified_llvm_control_codec_preserves_function_bodies_and_strengthenings"
      , "verified_llvm_control_codec_selects_exact_runtime_profile"
      , "verified_llvm_control_codec_binds_exact_descriptor_dimensions"
      , "verified_llvm_control_codec_requires_concrete_runtime_evidence"
      , "verified_llvm_control_codec_claims_no_universal_provider_or_io_theorem"
      , "llvm_control_codec_profile_or_body_drift_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/LLVM/ControlCodec.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/LLVM/ControlCodec.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-LLVM-CONTROL-CODEC-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-LLVM-CONTROL-CODEC-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness; reviewed storage-failure Systems/control-codec LLVM-to-normalized-proof correspondence; concrete C codec correctness; allocator/pointer lifetime; operating-system I/O; target calling convention; LLVM/Clang implementation correctness; linking/native execution; and exhaustive malformed-input coverage remain explicit trust boundaries or are established only by separately scoped runtime evidence."
  }

data ControlCodecProofCertificationError
  = ControlCodecProofSystemsError StorageFailureError
  | ControlCodecProofTranslationError ControlCodecLLVMError
  | ControlCodecProofWrongProof ObligationId ObligationId
  | ControlCodecProofWrongRuntimeTest ObligationId ObligationId
  | ControlCodecProofManifestError Text ManifestError
  | ControlCodecProofRuntimeManifestError ManifestError
  | ControlCodecProofFinalManifestError ManifestError
  deriving (Eq, Show)

data ControlCodecProofCertificationBundle = ControlCodecProofCertificationBundle
  { controlCodecProofSystems :: StorageFailureBundle
  , controlCodecProofLLVM :: LLVMArtifact
  , controlCodecProofRuntimeTestArtifact :: ArtifactIdentity
  , controlCodecProofArtifact :: ArtifactIdentity
  , controlCodecProofRecord :: Text
  , controlCodecProofLedger :: AssuranceLedger
  , controlCodecProofManifest :: AssuranceManifest
  , controlCodecProofContext :: VerificationContext
  }
  deriving (Eq, Show)

proofBoundCert016 :: ArtifactIdentity
proofBoundCert016 = ArtifactIdentity
  { artifactReference = ArtifactRef "certificate:phil:llvm:PHIL-LLVM-CERT-016:v1"
  , artifactDigest = Digest "4c32dcdc8175206fab4c8321588065bc8505c9e69fba9117e0d1be0b65685236"
  }

phase0ControlCodecProofCertification
  :: RocqCertificationBundle
  -> TestEvidenceCertificationBundle
  -> Either ControlCodecProofCertificationError ControlCodecProofCertificationBundle
phase0ControlCodecProofCertification llvmProof runtimeTest = do
  verifyProof llvmControlCodecCertificationSpec llvmProof
  verifyRuntimeTest runtimeTest
  systemsBundle <- mapLeft ControlCodecProofSystemsError phase0StorageFailureBundle
  let systemsArtifact = storageFailureArtifact systemsBundle
      llvmArtifact = lowerSystemsControlCodec phase0ControlCodecLLVMTarget systemsArtifact
  mapLeft ControlCodecProofTranslationError $
    verifyControlCodecTranslation systemsBundle llvmArtifact

  let proofLedger = rocqBundleLedger llvmProof
      proofRevisionId = rocqCertificateRevision (rocqBundleCertificate llvmProof)
      proofArtifact = rocqBundleCertificateArtifact llvmProof
      proofDigest = artifactDigest proofArtifact
      runtimeCertificate = testBundleCertificate runtimeTest
      runtimeRevisionId = testCertificateRevision runtimeCertificate
      runtimeTestArtifact = testBundleCertificateArtifact runtimeTest
      runtimeTestDigest = artifactDigest runtimeTestArtifact
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
        "/control-codec-v1/storage-failure-detail-v1/proof+runtime-test-bound"
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
        , ("predecessor_cert016", unDigest (artifactDigest proofBoundCert016))
        , ("proof_certificate", unDigest proofDigest)
        , ("runtime_test_certificate", unDigest runtimeTestDigest)
        , ("runtime_test_revision", unRevisionId runtimeRevisionId)
        , ("proof_assistant", "Rocq")
        , ("rocq_version", "9.2.0")
        , ("certificate_profile", "proof-assistant-theorem/v1")
        , ("function_bodies", "byte-structurally equal to storage-failure-detail-v1 predecessor IR")
        , ("strengthenings", "exactly equal to storage-failure-detail-v1 predecessor")
        , ("codec_runtime_evidence", "separately manifest-verified DifferentialTested certificate")
        , ("universal_codec_correctness", "not claimed")
        , ("operating_system_io", "outside this target scope")
        ]
      evidenceScope = ValidityScope $
        Map.insert "target" certificationTarget $
        Map.insert "compilation_profile" certificationProfile validityContext
      revisionStatement =
        "The control-codec-v1 runtime-profile successor over the storage-failure-detail-v1 Systems source may be labeled Certified only when the exact source/target/text digests, Systems lowering root, target/runtime-ABI/tool identities, proof-bound PHIL-LLVM-CERT-016 predecessor artifact, PHIL-LLVM-CONTROL-CODEC-001 proof authority, separately manifest-verified PHIL-RUNTIME-CONTROL-CODEC-001 test certificate, and exact verifyControlCodecTranslation result are content-bound. The compiler target preserves predecessor function bodies and strengthenings exactly while rebinding the runtime ABI to the canonical shared control-codec descriptor. The runtime certificate establishes only its exact deterministic fixture scope; universal C codec correctness, allocator/pointer lifetime, operating-system I/O, LLVM/Clang correctness, and exhaustive malformed-input coverage remain external or unproved."
      provisionalRevision = ObligationRevision
        { revisionObligationId = ObligationId "PHIL-LLVM-CERT-017"
        , revisionId = RevisionId ""
        , revisionStatement = revisionStatement
        , revisionStatementDigest = digestText revisionStatement
        , revisionKind = "LLVMControlCodecProofAndRuntimeEvidenceCertification"
        , revisionOrigin = "control-codec v1 / proof-bound PHIL-LLVM-CERT-017"
        , revisionScope = "llvm.phase0.preopt.control-codec.proof+runtime-test-bound"
        , revisionRequiredAt = "certification"
        , revisionRepresentation =
            "storage-failure-detail-v1 SystemsArtifact -> control-codec-v1 canonical pre-optimization LLVMArtifact + Rocq profile-preservation authority + content-bound native codec test certificate"
        , revisionSubjectIds =
            [ "systems:" <> unDigest sourceDigest
            , "systems-lowering-root:" <> unDigest systemsLoweringRoot
            , "llvm:" <> unDigest targetDigest
            , "llvm-text:" <> unDigest targetTextDigest
            , "runtime-abi:" <> unDigest abiDigest
            , "predecessor-cert016:" <> unDigest (artifactDigest proofBoundCert016)
            , "proof-certificate:" <> unDigest proofDigest
            , "runtime-test-certificate:" <> unDigest runtimeTestDigest
            , "runtime-test-revision:" <> unRevisionId runtimeRevisionId
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
            , "runtime-test:PHIL-RUNTIME-CONTROL-CODEC-001"
            ]
        , revisionAcceptanceRule = AcceptEntry TranslationValidated (EvidenceRole "translation_validated")
        , revisionGeneratedFrom = [proofRevisionId]
        }
      certificationRevision = provisionalRevision
        { revisionId = deriveRevisionId provisionalRevision }
      certificationRevisionId = revisionId certificationRevision
      translationArtifactRecord = Text.unlines
        [ "phil-llvm-phase0-control-codec-translation-validation/v1"
        , "source-successor=storage-failure-detail-v1"
        , "source-digest=" <> unDigest sourceDigest
        , "systems-lowering-root=" <> unDigest systemsLoweringRoot
        , "target-digest=" <> unDigest targetDigest
        , "target-text-digest=" <> unDigest targetTextDigest
        , "runtime-abi-profile=" <> llvmRuntimeABIProfile moduleValue
        , "runtime-abi-digest=" <> unDigest abiDigest
        , "predecessor-cert016=" <> unDigest (artifactDigest proofBoundCert016)
        , "proof-certificate=" <> unDigest proofDigest
        , "runtime-test-certificate=" <> unDigest runtimeTestDigest
        , "runtime-test-revision=" <> unRevisionId runtimeRevisionId
        , "translation-validator=Phil.LLVM.ControlCodec.verifyControlCodecTranslation"
        ]
      translationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef
            "artifact:phil:llvm:phase0:control-codec:translation-validation:v1"
        , artifactDigest = digestText translationArtifactRecord
        }
      evidenceId = EvidenceEntryId
        "evidence.llvm.phase0.control-codec.proof+runtime-test-bound.translation.validated"
      provisionalEvidence = EvidenceEntry
        { evidenceEntryId = evidenceId
        , evidenceEntryDigest = Digest ""
        , evidenceObligationRevision = certificationRevisionId
        , evidenceAssuranceKind = TranslationValidated
        , evidenceRole = EvidenceRole "translation_validated"
        , evidenceProducer = "Phil.LLVM.ControlCodec.verifyControlCodecTranslation + separately verified control-codec runtime test certificate"
        , evidenceChecker = "Phil.Assurance.Verify.verifyManifest"
        , evidenceArtifact = Just translationArtifact
        , evidenceInputDigests =
            [ sourceDigest
            , systemsLoweringRoot
            , targetDigest
            , targetTextDigest
            , abiDigest
            , artifactDigest proofBoundCert016
            , proofDigest
            , runtimeTestDigest
            ]
        , evidenceAssumptions = []
        , evidenceDependsOn = [DependsOnObligation proofRevisionId]
        , evidenceValidityScope = evidenceScope
        , evidenceResult = EvidenceAccepted
        , evidenceJustifies =
            [ "control-codec-v1 reuses the exact storage-failure-detail-v1 Systems authority"
            , "LLVM function bodies remain exactly equal to the certified CERT-016 predecessor target"
            , "LLVM strengthenings remain exactly equal to the certified CERT-016 predecessor target"
            , "runtime ABI profile/digest select the exact canonical control-codec-v1 descriptor"
            , "required explicit client/server/storage primitives remain rendered and the legacy profile identity is absent"
            , "the separately manifest-verified runtime test certificate binds the exact shared-provider deterministic fixture evidence"
            , "universal C codec correctness and operating-system I/O are not claimed"
            ]
        , evidenceRuntimeMechanism = Nothing
        , evidenceRuntimeResidue = []
        , evidenceCostRefs = []
        }
      translationEvidence = provisionalEvidence
        { evidenceEntryDigest = deriveEvidenceEntryDigest provisionalEvidence }
      certificationRecord = Text.unlines
        [ "phil-llvm-phase0-control-codec-certification/v1"
        , "obligation=PHIL-LLVM-CERT-017"
        , "revision=" <> unRevisionId certificationRevisionId
        , "source-successor=storage-failure-detail-v1"
        , "source-digest=" <> unDigest sourceDigest
        , "systems-lowering-root=" <> unDigest systemsLoweringRoot
        , "target-digest=" <> unDigest targetDigest
        , "target-text-digest=" <> unDigest targetTextDigest
        , "runtime-abi-profile=" <> llvmRuntimeABIProfile moduleValue
        , "runtime-abi-digest=" <> unDigest abiDigest
        , "translation-artifact=" <> renderArtifact translationArtifact
        , "predecessor-cert016=" <> renderArtifact proofBoundCert016
        , "proof=" <> unObligationId (rocqCertificateObligation (rocqBundleCertificate llvmProof))
            <> ";artifact=" <> unArtifactRef (artifactReference proofArtifact)
            <> ";sha256=" <> unDigest proofDigest
        , "runtime-test-obligation=" <> unObligationId (testCertificateObligation runtimeCertificate)
        , "runtime-test-revision=" <> unRevisionId runtimeRevisionId
        , "runtime-test-artifact=" <> renderArtifact runtimeTestArtifact
        , "runtime-test-scope=exact deterministic shared-provider fixtures only"
        , "universal-codec-correctness=not claimed"
        , "operating-system-io=outside control-codec-v1 certification scope"
        ]
      certificationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef "certificate:phil:llvm:PHIL-LLVM-CERT-017:v1"
        , artifactDigest = digestText certificationRecord
        }
      revisions = Map.insert certificationRevisionId certificationRevision
        (ledgerRevisions proofLedger)
      evidence = Map.insert evidenceId translationEvidence (ledgerEvidence proofLedger)
      obligationIds = Set.insert certificationRevisionId (Map.keysSet (ledgerRevisions proofLedger))
      evidenceIds = Set.insert evidenceId (Map.keysSet (ledgerEvidence proofLedger))
      ledger = emptyLedger { ledgerRevisions = revisions, ledgerEvidence = evidence }
      certificationRoot = digestText $ Text.intercalate "|"
        [ "phil-llvm-phase0-control-codec-proof+runtime-test-bound-certification-root-v1"
        , unDigest sourceDigest
        , unDigest systemsLoweringRoot
        , unDigest targetDigest
        , unDigest targetTextDigest
        , unDigest abiDigest
        , unDigest (artifactDigest proofBoundCert016)
        , unDigest proofDigest
        , unDigest runtimeTestDigest
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
      explicitArtifacts =
        [ translationArtifact
        , certificationArtifact
        , proofBoundCert016
        , proofArtifact
        , runtimeTestArtifact
        ]
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
      result = ControlCodecProofCertificationBundle
        { controlCodecProofSystems = systemsBundle
        , controlCodecProofLLVM = llvmArtifact
        , controlCodecProofRuntimeTestArtifact = runtimeTestArtifact
        , controlCodecProofArtifact = certificationArtifact
        , controlCodecProofRecord = certificationRecord
        , controlCodecProofLedger = ledger
        , controlCodecProofManifest = manifest
        , controlCodecProofContext = context
        }

  mapLeft ControlCodecProofFinalManifestError $ verifyManifest context ledger manifest
  pure result

verifyPhase0ControlCodecProofCertification
  :: RocqCertificationBundle
  -> TestEvidenceCertificationBundle
  -> Either ControlCodecProofCertificationError ()
verifyPhase0ControlCodecProofCertification proofBundle runtimeTest = do
  bundle <- phase0ControlCodecProofCertification proofBundle runtimeTest
  mapLeft ControlCodecProofFinalManifestError $
    verifyManifest
      (controlCodecProofContext bundle)
      (controlCodecProofLedger bundle)
      (controlCodecProofManifest bundle)

renderControlCodecProofCertification
  :: ControlCodecProofCertificationBundle
  -> Text
renderControlCodecProofCertification = controlCodecProofRecord

verifyProof
  :: RocqCertificationSpec
  -> RocqCertificationBundle
  -> Either ControlCodecProofCertificationError ()
verifyProof spec bundle = do
  let expected = rocqSpecObligation spec
      actual = rocqCertificateObligation (rocqBundleCertificate bundle)
  unless (actual == expected) $
    Left (ControlCodecProofWrongProof expected actual)
  mapLeft (ControlCodecProofManifestError "llvm-control-codec") $
    verifyManifest
      (rocqBundleVerificationContext bundle)
      (rocqBundleLedger bundle)
      (rocqBundleManifest bundle)

verifyRuntimeTest
  :: TestEvidenceCertificationBundle
  -> Either ControlCodecProofCertificationError ()
verifyRuntimeTest bundle = do
  let expected = testSpecObligation controlCodecRuntimeCertificationSpec
      actual = testCertificateObligation (testBundleCertificate bundle)
  unless (actual == expected) $
    Left (ControlCodecProofWrongRuntimeTest expected actual)
  mapLeft ControlCodecProofRuntimeManifestError $
    verifyManifest
      (testBundleVerificationContext bundle)
      (testBundleLedger bundle)
      (testBundleManifest bundle)

renderArtifact :: ArtifactIdentity -> Text
renderArtifact artifact =
  unArtifactRef (artifactReference artifact) <> ";sha256=" <> unDigest (artifactDigest artifact)

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
