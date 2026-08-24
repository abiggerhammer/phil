{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.ServerFramedIngressProofCertification
  ( llvmServerFramedIngressCertificationSpec
  , ServerFramedIngressProofCertificationError (..)
  , ServerFramedIngressProofCertificationBundle (..)
  , phase0ServerFramedIngressProofCertification
  , verifyPhase0ServerFramedIngressProofCertification
  , renderServerFramedIngressProofCertification
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
import Phil.LLVM.ServerFramedIngress
import Phil.Systems.IR
import Phil.Systems.RecognitionFailure
import Phil.Systems.Verify (SystemsVerificationContext (..))

llvmServerFramedIngressCertificationSpec :: RocqCertificationSpec
llvmServerFramedIngressCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "llvm-server-framed-ingress"
  , rocqSpecObligation = ObligationId "PHIL-LLVM-SERVER-FRAMED-INGRESS-001"
  , rocqSpecClaim =
      "For server-framed-ingress-v1 over the certified recognition-failure-detail-v1 Systems source, verified lowering preserves the proof-bound Client Control Send predecessor; lowers Hello and Begin frame receive with the exact server transport and explicit pending/frame outputs; lowers each frame borrow to a no-copy explicit frame-view primitive; recognizes each grammar with the exact pending/raw inputs and exact record/reason outputs; commits the exact pending ingress on the exact transport on success; forwards the exact grammar-specific reason before destroying the exact pending/frame pair on failure; preserves distinct Hello/Begin reason identities; eliminates legacy nullary and ambient ingress state; and claims no concrete frame codec, provider handle-lifetime semantics, physical I/O, or storage-failure detail."
  , rocqSpecKind = "LLVM server framed-ingress and recognition-failure ABI v1"
  , rocqSpecOrigin =
      "src/Phil/LLVM/ServerFramedIngress.hs; docs/phase-0/server-framed-ingress-v1.md; proof/Phil/LLVM/ServerFramedIngress.v"
  , rocqSpecScope = "Phil.LLVM server-framed-ingress-v1 over recognition-failure-detail-v1"
  , rocqSpecRepresentation =
      "explicit transport/pending/frame/raw/record/reason identities for Hello and Begin ingress with no-copy frame views and exact failure cleanup"
  , rocqSpecSubjects =
      [ "phil_runtime_receive_frame_Hello(ptr,ptr,ptr)->void"
      , "phil_runtime_frame_borrow_view_Hello(ptr)->ptr"
      , "phil_runtime_recognize_Hello(ptr,ptr,ptr,ptr)->i8"
      , "phil_runtime_commit_ingress_Hello(ptr,ptr)->void"
      , "phil_runtime_fail_recognition_Hello(ptr,ptr)->void"
      , "phil_runtime_destroy_pending_Hello(ptr,ptr)->void"
      , "phil_runtime_receive_frame_Begin(ptr,ptr,ptr)->void"
      , "phil_runtime_frame_borrow_view_Begin(ptr)->ptr"
      , "phil_runtime_recognize_Begin(ptr,ptr,ptr,ptr)->i8"
      , "phil_runtime_commit_ingress_Begin(ptr,ptr)->void"
      , "phil_runtime_fail_recognition_Begin(ptr,ptr)->void"
      , "phil_runtime_destroy_pending_Begin(ptr,ptr)->void"
      ]
  , rocqSpecTheorems =
      [ "verified_llvm_server_framed_ingress_reuses_source_and_predecessor_authority"
      , "verified_llvm_server_framed_ingress_preserves_exact_hello_ingress"
      , "verified_llvm_server_framed_ingress_preserves_exact_begin_ingress"
      , "verified_llvm_server_framed_ingress_preserves_commit_and_failure_cleanup"
      , "verified_llvm_server_framed_ingress_preserves_distinct_failure_reasons"
      , "verified_llvm_server_framed_ingress_eliminates_legacy_and_ambient_ingress_state"
      , "verified_llvm_server_framed_ingress_claims_no_codec_lifetime_or_storage_detail"
      , "llvm_server_framed_ingress_identity_or_order_drift_is_rejected"
      , "llvm_server_framed_ingress_ambient_or_legacy_drift_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/LLVM/ServerFramedIngress.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/LLVM/ServerFramedIngress.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-LLVM-SERVER-FRAMED-INGRESS-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-LLVM-SERVER-FRAMED-INGRESS-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness; reviewed recognition-failure Systems/LLVM-to-normalized-proof correspondence; concrete Hello/Begin frame codec/framing; pending/frame/record/reason provider representation and lifetime; receive-frame completion semantics; physical I/O; target calling convention; LLVM 18; linking/native execution; and storage-failure detail remain explicit trust boundaries or out of scope."
  }

data ServerFramedIngressProofCertificationError
  = ServerFramedIngressProofSystemsError RecognitionFailureError
  | ServerFramedIngressProofTranslationError ServerFramedIngressLLVMError
  | ServerFramedIngressProofWrongProof ObligationId ObligationId
  | ServerFramedIngressProofManifestError Text ManifestError
  | ServerFramedIngressProofFinalManifestError ManifestError
  deriving (Eq, Show)

data ServerFramedIngressProofCertificationBundle = ServerFramedIngressProofCertificationBundle
  { serverFramedIngressProofSystems :: RecognitionFailureBundle
  , serverFramedIngressProofLLVM :: LLVMArtifact
  , serverFramedIngressProofArtifact :: ArtifactIdentity
  , serverFramedIngressProofRecord :: Text
  , serverFramedIngressProofLedger :: AssuranceLedger
  , serverFramedIngressProofManifest :: AssuranceManifest
  , serverFramedIngressProofContext :: VerificationContext
  }
  deriving (Eq, Show)

proofBoundCert014 :: ArtifactIdentity
proofBoundCert014 = ArtifactIdentity
  { artifactReference = ArtifactRef "certificate:phil:llvm:PHIL-LLVM-CERT-014:v1"
  , artifactDigest = Digest "fbf7f5be73773f7e7293b748ea266d6b3b60787ff61f7b8bf45b5e1e29d3967e"
  }

phase0ServerFramedIngressProofCertification
  :: RocqCertificationBundle
  -> Either ServerFramedIngressProofCertificationError ServerFramedIngressProofCertificationBundle
phase0ServerFramedIngressProofCertification llvmProof = do
  verifyProof llvmServerFramedIngressCertificationSpec llvmProof
  systemsBundle <- mapLeft ServerFramedIngressProofSystemsError phase0RecognitionFailureBundle
  let systemsArtifact = recognitionFailureArtifact systemsBundle
      llvmArtifact = lowerSystemsServerFramedIngress
        phase0ServerFramedIngressLLVMTarget
        systemsArtifact
  mapLeft ServerFramedIngressProofTranslationError $
    verifyServerFramedIngressTranslation systemsBundle llvmArtifact

  let proofLedger = rocqBundleLedger llvmProof
      proofRevisionId = rocqCertificateRevision (rocqBundleCertificate llvmProof)
      proofArtifact = rocqBundleCertificateArtifact llvmProof
      proofDigest = artifactDigest proofArtifact
      systemsManifest = systemsAssuranceManifest (recognitionFailureContext systemsBundle)
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
        "/server-framed-ingress-v1/recognition-failure-detail-v1/proof-bound"
      validityContext = Map.fromList
        [ ("source_successor", "recognition-failure-detail-v1")
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
        , ("predecessor_cert014", unDigest (artifactDigest proofBoundCert014))
        , ("proof_certificate", unDigest proofDigest)
        , ("proof_assistant", "Rocq")
        , ("rocq_version", "9.2.0")
        , ("certificate_profile", "proof-assistant-theorem/v1")
        , ("ingress_identity", "explicit transport/pending/frame/raw/record/reason per grammar")
        , ("frame_view", "borrow-no-copy")
        , ("recognition_failure_order", "fail exact reason before destroy exact pending/frame")
        , ("concrete_codec", "external runtime provider gate")
        , ("storage_failure_detail", "outside this target scope")
        ]
      evidenceScope = ValidityScope $
        Map.insert "target" certificationTarget $
        Map.insert "compilation_profile" certificationProfile validityContext
      revisionStatement =
        "The server-framed-ingress-v1 lowering over the recognition-failure-detail-v1 Systems source may be labeled Certified only when the exact source/target/text digests, Systems lowering root, target/runtime-ABI/tool identities, proof-bound PHIL-LLVM-CERT-014 predecessor artifact, PHIL-LLVM-SERVER-FRAMED-INGRESS-001 proof authority, and exact translation-validation result are content-bound. The target preserves explicit Hello/Begin transport, pending, frame, borrowed raw-view, recognized-record, and grammar-specific failure-reason identities; commits the exact pending ingress on success; forwards each exact reason before destroying the exact pending/frame pair on failure; preserves the proof-bound client-control-send predecessor; and eliminates legacy nullary/ambient ingress state. Concrete frame encoding/framing, provider handle representation/lifetime, receive completion semantics, physical I/O, LLVM implementation correctness, linking/native execution, and storage-failure detail remain external or out of scope."
      provisionalRevision = ObligationRevision
        { revisionObligationId = ObligationId "PHIL-LLVM-CERT-015"
        , revisionId = RevisionId ""
        , revisionStatement = revisionStatement
        , revisionStatementDigest = digestText revisionStatement
        , revisionKind = "LLVMServerFramedIngressProofBoundCertification"
        , revisionOrigin = "server-framed-ingress ABI v1 / proof-bound PHIL-LLVM-CERT-015"
        , revisionScope = "llvm.phase0.preopt.server-framed-ingress.recognition-failure-detail.proof-bound"
        , revisionRequiredAt = "certification"
        , revisionRepresentation =
            "recognition-failure-detail-v1 SystemsArtifact -> server-framed-ingress-v1 canonical pre-optimization LLVMArtifact + proof authority"
        , revisionSubjectIds =
            [ "systems:" <> unDigest sourceDigest
            , "systems-lowering-root:" <> unDigest systemsLoweringRoot
            , "llvm:" <> unDigest targetDigest
            , "llvm-text:" <> unDigest targetTextDigest
            , "runtime-abi:" <> unDigest abiDigest
            , "predecessor-cert014:" <> unDigest (artifactDigest proofBoundCert014)
            , "proof-certificate:" <> unDigest proofDigest
            ]
        , revisionContextIds =
            [ "language:" <> llvmLanguageVersion moduleValue
            , "tool-profile:" <> llvmToolVersion moduleValue
            , "target:" <> llvmTargetTriple moduleValue
            , "layout:" <> llvmDataLayout moduleValue
            , "runtime-abi-profile:" <> llvmRuntimeABIProfile moduleValue
            , "compilation-profile:" <> sourceCompilationProfile
            , "source-successor:recognition-failure-detail-v1"
            , "rocq:9.2.0"
            ]
        , revisionAcceptanceRule = AcceptEntry TranslationValidated (EvidenceRole "translation_validated")
        , revisionGeneratedFrom = [proofRevisionId]
        }
      certificationRevision = provisionalRevision
        { revisionId = deriveRevisionId provisionalRevision }
      certificationRevisionId = revisionId certificationRevision
      translationArtifactRecord = Text.unlines
        [ "phil-llvm-phase0-server-framed-ingress-translation-validation/v1"
        , "source-successor=recognition-failure-detail-v1"
        , "source-digest=" <> unDigest sourceDigest
        , "systems-lowering-root=" <> unDigest systemsLoweringRoot
        , "target-digest=" <> unDigest targetDigest
        , "target-text-digest=" <> unDigest targetTextDigest
        , "runtime-abi-profile=" <> llvmRuntimeABIProfile moduleValue
        , "runtime-abi-digest=" <> unDigest abiDigest
        , "predecessor-cert014=" <> unDigest (artifactDigest proofBoundCert014)
        , "proof-certificate=" <> unDigest proofDigest
        , "translation-validator=Phil.LLVM.ServerFramedIngress.verifyServerFramedIngressTranslation"
        ]
      translationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef
            "artifact:phil:llvm:phase0:server-framed-ingress:translation-validation:v1"
        , artifactDigest = digestText translationArtifactRecord
        }
      evidenceId = EvidenceEntryId
        "evidence.llvm.phase0.server-framed-ingress.proof-bound.translation.validated"
      provisionalEvidence = EvidenceEntry
        { evidenceEntryId = evidenceId
        , evidenceEntryDigest = Digest ""
        , evidenceObligationRevision = certificationRevisionId
        , evidenceAssuranceKind = TranslationValidated
        , evidenceRole = EvidenceRole "translation_validated"
        , evidenceProducer = "Phil.LLVM.ServerFramedIngress.verifyServerFramedIngressTranslation"
        , evidenceChecker = "Phil.Assurance.Verify.verifyManifest"
        , evidenceArtifact = Just translationArtifact
        , evidenceInputDigests =
            [ sourceDigest
            , systemsLoweringRoot
            , targetDigest
            , targetTextDigest
            , abiDigest
            , artifactDigest proofBoundCert014
            , proofDigest
            ]
        , evidenceAssumptions = []
        , evidenceDependsOn = [DependsOnObligation proofRevisionId]
        , evidenceValidityScope = evidenceScope
        , evidenceResult = EvidenceAccepted
        , evidenceJustifies =
            [ "Hello and Begin frame receive use exact server transport with explicit pending/frame outputs"
            , "frame-view borrowing reuses the exact frame owner without representation copy"
            , "recognition uses exact pending/raw inputs and exact record/reason outputs"
            , "successful recognition commits the exact pending ingress on the exact server transport"
            , "failure forwards the exact grammar-specific reason before exact pending/frame destruction"
            , "proof-bound Client Control Send predecessor remains physically preserved"
            , "legacy nullary and ambient ingress state are absent"
            , "concrete frame codec/provider lifetimes and storage failure detail are outside certification scope"
            ]
        , evidenceRuntimeMechanism = Nothing
        , evidenceRuntimeResidue = []
        , evidenceCostRefs = []
        }
      translationEvidence = provisionalEvidence
        { evidenceEntryDigest = deriveEvidenceEntryDigest provisionalEvidence }
      certificationRecord = Text.unlines
        [ "phil-llvm-phase0-server-framed-ingress-certification/v1"
        , "obligation=PHIL-LLVM-CERT-015"
        , "revision=" <> unRevisionId certificationRevisionId
        , "source-successor=recognition-failure-detail-v1"
        , "source-digest=" <> unDigest sourceDigest
        , "systems-lowering-root=" <> unDigest systemsLoweringRoot
        , "target-digest=" <> unDigest targetDigest
        , "target-text-digest=" <> unDigest targetTextDigest
        , "runtime-abi-profile=" <> llvmRuntimeABIProfile moduleValue
        , "runtime-abi-digest=" <> unDigest abiDigest
        , "translation-artifact=" <> renderArtifact translationArtifact
        , "predecessor-cert014=" <> renderArtifact proofBoundCert014
        , "proof=" <> unObligationId (rocqCertificateObligation (rocqBundleCertificate llvmProof))
            <> ";artifact=" <> unArtifactRef (artifactReference proofArtifact)
            <> ";sha256=" <> unDigest proofDigest
        , "external-codec=Hello/Begin frame grammar/framing provider gate"
        , "external-provider-semantics=pending/frame/record/reason handles and lifetimes"
        , "external-llvm=LLVM 18 acceptance/link gate"
        , "storage-failure-detail=outside server-framed-ingress-v1 source scope"
        ]
      certificationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef "certificate:phil:llvm:PHIL-LLVM-CERT-015:v1"
        , artifactDigest = digestText certificationRecord
        }
      revisions = Map.insert certificationRevisionId certificationRevision
        (ledgerRevisions proofLedger)
      evidence = Map.insert evidenceId translationEvidence (ledgerEvidence proofLedger)
      obligationIds = Set.insert certificationRevisionId (Map.keysSet (ledgerRevisions proofLedger))
      evidenceIds = Set.insert evidenceId (Map.keysSet (ledgerEvidence proofLedger))
      ledger = emptyLedger { ledgerRevisions = revisions, ledgerEvidence = evidence }
      certificationRoot = digestText $ Text.intercalate "|"
        [ "phil-llvm-phase0-server-framed-ingress-proof-bound-certification-root-v1"
        , unDigest sourceDigest
        , unDigest systemsLoweringRoot
        , unDigest targetDigest
        , unDigest targetTextDigest
        , unDigest abiDigest
        , unDigest (artifactDigest proofBoundCert014)
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
      explicitArtifacts = [translationArtifact, certificationArtifact, proofBoundCert014, proofArtifact]
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
      result = ServerFramedIngressProofCertificationBundle
        { serverFramedIngressProofSystems = systemsBundle
        , serverFramedIngressProofLLVM = llvmArtifact
        , serverFramedIngressProofArtifact = certificationArtifact
        , serverFramedIngressProofRecord = certificationRecord
        , serverFramedIngressProofLedger = ledger
        , serverFramedIngressProofManifest = manifest
        , serverFramedIngressProofContext = context
        }

  mapLeft ServerFramedIngressProofFinalManifestError $ verifyManifest context ledger manifest
  pure result

verifyPhase0ServerFramedIngressProofCertification
  :: RocqCertificationBundle
  -> Either ServerFramedIngressProofCertificationError ()
verifyPhase0ServerFramedIngressProofCertification proofBundle = do
  bundle <- phase0ServerFramedIngressProofCertification proofBundle
  mapLeft ServerFramedIngressProofFinalManifestError $
    verifyManifest
      (serverFramedIngressProofContext bundle)
      (serverFramedIngressProofLedger bundle)
      (serverFramedIngressProofManifest bundle)

renderServerFramedIngressProofCertification
  :: ServerFramedIngressProofCertificationBundle
  -> Text
renderServerFramedIngressProofCertification = serverFramedIngressProofRecord

verifyProof
  :: RocqCertificationSpec
  -> RocqCertificationBundle
  -> Either ServerFramedIngressProofCertificationError ()
verifyProof spec bundle = do
  let expected = rocqSpecObligation spec
      actual = rocqCertificateObligation (rocqBundleCertificate bundle)
  unless (actual == expected) $
    Left (ServerFramedIngressProofWrongProof expected actual)
  mapLeft (ServerFramedIngressProofManifestError "llvm-server-framed-ingress") $
    verifyManifest
      (rocqBundleVerificationContext bundle)
      (rocqBundleLedger bundle)
      (rocqBundleManifest bundle)

renderArtifact :: ArtifactIdentity -> Text
renderArtifact artifact =
  unArtifactRef (artifactReference artifact) <> ";sha256=" <> unDigest (artifactDigest artifact)

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
