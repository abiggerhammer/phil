{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.ClientControlSendProofCertification
  ( llvmClientControlSendCertificationSpec
  , ClientControlSendProofCertificationError (..)
  , ClientControlSendProofCertificationBundle (..)
  , phase0ClientControlSendProofCertification
  , verifyPhase0ClientControlSendProofCertification
  , renderClientControlSendProofCertification
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
import Phil.LLVM.ClientControlSend
import Phil.LLVM.IR
import Phil.Systems.ClientOutbound
import Phil.Systems.IR
import Phil.Systems.Verify (SystemsVerificationContext (..))

llvmClientControlSendCertificationSpec :: RocqCertificationSpec
llvmClientControlSendCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "llvm-client-control-send"
  , rocqSpecObligation = ObligationId "PHIL-LLVM-CLIENT-CONTROL-SEND-001"
  , rocqSpecClaim =
      "For client-control-send-v1 over the certified client-outbound-semantics-v1 source, verified lowering materializes exactly one explicit supported-version-set handle, sends Hello with the exact transport and that exact handle, reuses the same handle for selected-version refinement, erases the semantic payload borrow to the exact existing payload-owner handle without copying, derives SHA-256/length/kind from that exact owner, sends Begin[sha256] with the exact derived operands, preserves the proof-bound exact payload send, eliminates generic/ambient outbound state and target-side Hello/Begin/view residue, and claims no concrete Hello/Begin byte codec, provider semantics, or server failure-detail lowering."
  , rocqSpecKind = "LLVM client control-message send ABI v1"
  , rocqSpecOrigin =
      "src/Phil/LLVM/ClientControlSend.hs; docs/phase-0/client-control-send-abi-v1.md; proof/Phil/LLVM/ClientControlSend.v"
  , rocqSpecScope = "Phil.LLVM client-control-send-v1 over client-outbound-semantics-v1"
  , rocqSpecRepresentation =
      "explicit supported-version identity + fused Hello/Begin serializer/send operations + payload-owner derivations + explicit version-set refinement"
  , rocqSpecSubjects =
      [ "phil_runtime_supported_versions()->ptr"
      , "phil_runtime_send_hello(ptr,ptr)->void"
      , "client.payload -> client.payload.owner"
      , "phil_runtime_sha256(ptr)->ptr"
      , "phil_runtime_payload_length(ptr)->i64"
      , "phil_runtime_payload_kind(ptr)->ptr"
      , "phil_runtime_send_begin_sha256(ptr,i64,ptr,ptr)->void"
      , "phil_runtime_refine_selected_version_with_set(ptr,ptr,i16)->i1"
      , "phil_runtime_send_exact(ptr,ptr)->void"
      ]
  , rocqSpecTheorems =
      [ "verified_llvm_client_control_send_reuses_source_and_exact_send_authority"
      , "verified_llvm_client_control_send_preserves_one_hello_with_explicit_versions"
      , "verified_llvm_client_control_send_preserves_payload_derivations_without_copy"
      , "verified_llvm_client_control_send_preserves_exact_begin_operands"
      , "verified_llvm_client_control_send_eliminates_ambient_version_state"
      , "verified_llvm_client_control_send_preserves_exact_payload_send"
      , "verified_llvm_client_control_send_claims_no_codec_or_server_failure_detail"
      , "llvm_client_control_send_versions_or_begin_drift_is_rejected"
      , "llvm_client_control_send_copy_ambient_or_exact_send_drift_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/LLVM/ClientControlSend.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/LLVM/ClientControlSend.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-LLVM-CLIENT-CONTROL-SEND-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-LLVM-CLIENT-CONTROL-SEND-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness; reviewed client-outbound Systems/LLVM-to-normalized-proof correspondence; supported-version-set provider semantics/lifetime; SHA-256/payload-kind provider semantics; concrete Hello/Begin codec/framing; whole-send/non-return behavior; physical I/O; target calling convention; LLVM 18; linking; native execution; and later server-side recognition/storage failure lowering remain explicit trust boundaries or out of scope."
  }

data ClientControlSendProofCertificationError
  = ClientControlSendProofSystemsError ClientOutboundError
  | ClientControlSendProofTranslationError ClientControlSendLLVMError
  | ClientControlSendProofWrongProof ObligationId ObligationId
  | ClientControlSendProofManifestError Text ManifestError
  | ClientControlSendProofFinalManifestError ManifestError
  deriving (Eq, Show)

data ClientControlSendProofCertificationBundle = ClientControlSendProofCertificationBundle
  { clientControlSendProofSystems :: ClientOutboundBundle
  , clientControlSendProofLLVM :: LLVMArtifact
  , clientControlSendProofArtifact :: ArtifactIdentity
  , clientControlSendProofRecord :: Text
  , clientControlSendProofLedger :: AssuranceLedger
  , clientControlSendProofManifest :: AssuranceManifest
  , clientControlSendProofContext :: VerificationContext
  }
  deriving (Eq, Show)

proofBoundCert013 :: ArtifactIdentity
proofBoundCert013 = ArtifactIdentity
  { artifactReference = ArtifactRef "certificate:phil:llvm:PHIL-LLVM-CERT-013:v1"
  , artifactDigest = Digest "00882e397eed6a6473521f950a48ce9a3e923b0ae6190a612ef8b8d8dff0e30e"
  }

phase0ClientControlSendProofCertification
  :: RocqCertificationBundle
  -> Either ClientControlSendProofCertificationError ClientControlSendProofCertificationBundle
phase0ClientControlSendProofCertification llvmProof = do
  verifyProof llvmClientControlSendCertificationSpec llvmProof
  systemsBundle <- mapLeft ClientControlSendProofSystemsError phase0ClientOutboundBundle
  let systemsArtifact = clientOutboundArtifact systemsBundle
      llvmArtifact = lowerSystemsClientControlSend
        phase0ClientControlSendLLVMTarget
        systemsArtifact
  mapLeft ClientControlSendProofTranslationError $
    verifyClientControlSendTranslation systemsBundle llvmArtifact

  let proofLedger = rocqBundleLedger llvmProof
      proofRevisionId = rocqCertificateRevision (rocqBundleCertificate llvmProof)
      proofArtifact = rocqBundleCertificateArtifact llvmProof
      proofDigest = artifactDigest proofArtifact
      systemsManifest = systemsAssuranceManifest (clientOutboundContext systemsBundle)
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
        "/client-control-send-v1/client-outbound-v1/proof-bound"
      validityContext = Map.fromList
        [ ("source_successor", "client-outbound-semantics-v1")
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
        , ("predecessor_cert013", unDigest (artifactDigest proofBoundCert013))
        , ("proof_certificate", unDigest proofDigest)
        , ("proof_assistant", "Rocq")
        , ("rocq_version", "9.2.0")
        , ("certificate_profile", "proof-assistant-theorem/v1")
        , ("supported_versions_identity", "same explicit handle used by Hello send and version refinement")
        , ("payload_relation", "client.payload -> client.payload.owner; borrowed view erased without copy")
        , ("hello_begin_record_lowering", "fused into explicit serializer/send runtime primitives")
        , ("concrete_codec", "external runtime provider gate")
        , ("server_failure_detail", "outside this target scope")
        ]
      evidenceScope = ValidityScope $
        Map.insert "target" certificationTarget $
        Map.insert "compilation_profile" certificationProfile validityContext
      revisionStatement =
        "The client-control-send-v1 lowering over the client-outbound-semantics-v1 Systems source may be labeled Certified only when the exact source/target/text digests, Systems lowering root, target/runtime-ABI/tool identities, proof-bound PHIL-LLVM-CERT-013 predecessor artifact, PHIL-LLVM-CLIENT-CONTROL-SEND-001 proof authority, and exact translation-validation result are content-bound. The target preserves the same explicit supported-version handle across Hello send and selected-version refinement, erases the payload borrow to the original owner handle without copy, derives and forwards exact Begin operands, preserves exact payload send authority, and eliminates generic/ambient outbound state. Concrete Hello/Begin byte encoding and framing, supported-version/payload-kind/SHA-256 provider semantics and lifetime, whole-send/non-return behavior, physical I/O, LLVM implementation correctness, linking/native execution, and later server recognition/storage failure-detail lowering remain external or out of scope."
      provisionalRevision = ObligationRevision
        { revisionObligationId = ObligationId "PHIL-LLVM-CERT-014"
        , revisionId = RevisionId ""
        , revisionStatement = revisionStatement
        , revisionStatementDigest = digestText revisionStatement
        , revisionKind = "LLVMClientControlSendProofBoundCertification"
        , revisionOrigin = "client-control-send ABI v1 / proof-bound PHIL-LLVM-CERT-014"
        , revisionScope = "llvm.phase0.preopt.client-control-send.client-outbound.proof-bound"
        , revisionRequiredAt = "certification"
        , revisionRepresentation =
            "client-outbound-semantics-v1 SystemsArtifact -> client-control-send-v1 canonical pre-optimization LLVMArtifact + proof authority"
        , revisionSubjectIds =
            [ "systems:" <> unDigest sourceDigest
            , "systems-lowering-root:" <> unDigest systemsLoweringRoot
            , "llvm:" <> unDigest targetDigest
            , "llvm-text:" <> unDigest targetTextDigest
            , "runtime-abi:" <> unDigest abiDigest
            , "predecessor-cert013:" <> unDigest (artifactDigest proofBoundCert013)
            , "proof-certificate:" <> unDigest proofDigest
            ]
        , revisionContextIds =
            [ "language:" <> llvmLanguageVersion moduleValue
            , "tool-profile:" <> llvmToolVersion moduleValue
            , "target:" <> llvmTargetTriple moduleValue
            , "layout:" <> llvmDataLayout moduleValue
            , "runtime-abi-profile:" <> llvmRuntimeABIProfile moduleValue
            , "compilation-profile:" <> sourceCompilationProfile
            , "source-successor:client-outbound-semantics-v1"
            , "rocq:9.2.0"
            ]
        , revisionAcceptanceRule = AcceptEntry TranslationValidated (EvidenceRole "translation_validated")
        , revisionGeneratedFrom = [proofRevisionId]
        }
      certificationRevision = provisionalRevision
        { revisionId = deriveRevisionId provisionalRevision }
      certificationRevisionId = revisionId certificationRevision
      translationArtifactRecord = Text.unlines
        [ "phil-llvm-phase0-client-control-send-translation-validation/v1"
        , "source-successor=client-outbound-semantics-v1"
        , "source-digest=" <> unDigest sourceDigest
        , "systems-lowering-root=" <> unDigest systemsLoweringRoot
        , "target-digest=" <> unDigest targetDigest
        , "target-text-digest=" <> unDigest targetTextDigest
        , "runtime-abi-profile=" <> llvmRuntimeABIProfile moduleValue
        , "runtime-abi-digest=" <> unDigest abiDigest
        , "predecessor-cert013=" <> unDigest (artifactDigest proofBoundCert013)
        , "proof-certificate=" <> unDigest proofDigest
        , "translation-validator=Phil.LLVM.ClientControlSend.verifyClientControlSendTranslation"
        ]
      translationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef
            "artifact:phil:llvm:phase0:client-control-send:translation-validation:v1"
        , artifactDigest = digestText translationArtifactRecord
        }
      evidenceId = EvidenceEntryId
        "evidence.llvm.phase0.client-control-send.proof-bound.translation.validated"
      provisionalEvidence = EvidenceEntry
        { evidenceEntryId = evidenceId
        , evidenceEntryDigest = Digest ""
        , evidenceObligationRevision = certificationRevisionId
        , evidenceAssuranceKind = TranslationValidated
        , evidenceRole = EvidenceRole "translation_validated"
        , evidenceProducer = "Phil.LLVM.ClientControlSend.verifyClientControlSendTranslation"
        , evidenceChecker = "Phil.Assurance.Verify.verifyManifest"
        , evidenceArtifact = Just translationArtifact
        , evidenceInputDigests =
            [ sourceDigest
            , systemsLoweringRoot
            , targetDigest
            , targetTextDigest
            , abiDigest
            , artifactDigest proofBoundCert013
            , proofDigest
            ]
        , evidenceAssumptions = []
        , evidenceDependsOn = [DependsOnObligation proofRevisionId]
        , evidenceValidityScope = evidenceScope
        , evidenceResult = EvidenceAccepted
        , evidenceJustifies =
            [ "one explicit supported-version handle is produced and sent with exact client transport"
            , "the same supported-version handle is passed to selected-version refinement"
            , "client payload borrow erases to exact client.payload.owner without a copy"
            , "SHA-256, payload length, and payload kind derive from the exact payload owner"
            , "Begin[sha256] send receives exact transport/length/kind/digest operands"
            , "the proof-bound exact payload send predecessor remains physically present"
            , "target-side Hello/Begin/view handles, generic outbound calls, poison, and ambient state are absent"
            , "concrete codec/framing and later server failure detail are outside this certification scope"
            ]
        , evidenceRuntimeMechanism = Nothing
        , evidenceRuntimeResidue = []
        , evidenceCostRefs = []
        }
      translationEvidence = provisionalEvidence
        { evidenceEntryDigest = deriveEvidenceEntryDigest provisionalEvidence }
      certificationRecord = Text.unlines
        [ "phil-llvm-phase0-client-control-send-certification/v1"
        , "obligation=PHIL-LLVM-CERT-014"
        , "revision=" <> unRevisionId certificationRevisionId
        , "source-successor=client-outbound-semantics-v1"
        , "source-digest=" <> unDigest sourceDigest
        , "systems-lowering-root=" <> unDigest systemsLoweringRoot
        , "target-digest=" <> unDigest targetDigest
        , "target-text-digest=" <> unDigest targetTextDigest
        , "runtime-abi-profile=" <> llvmRuntimeABIProfile moduleValue
        , "runtime-abi-digest=" <> unDigest abiDigest
        , "translation-artifact=" <> renderArtifact translationArtifact
        , "predecessor-cert013=" <> renderArtifact proofBoundCert013
        , "proof=" <> unObligationId (rocqCertificateObligation (rocqBundleCertificate llvmProof))
            <> ";artifact=" <> unArtifactRef (artifactReference proofArtifact)
            <> ";sha256=" <> unDigest proofDigest
        , "external-codec=Hello/Begin frozen grammar/framing provider gate"
        , "external-provider-semantics=VersionSet/PayloadKind/SHA256 handles and lifetimes"
        , "external-llvm=LLVM 18 acceptance/link gate"
        , "server-failure-detail=outside client-control-send-v1 source scope"
        ]
      certificationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef "certificate:phil:llvm:PHIL-LLVM-CERT-014:v1"
        , artifactDigest = digestText certificationRecord
        }
      revisions = Map.insert certificationRevisionId certificationRevision
        (ledgerRevisions proofLedger)
      evidence = Map.insert evidenceId translationEvidence (ledgerEvidence proofLedger)
      obligationIds = Set.insert certificationRevisionId (Map.keysSet (ledgerRevisions proofLedger))
      evidenceIds = Set.insert evidenceId (Map.keysSet (ledgerEvidence proofLedger))
      ledger = emptyLedger { ledgerRevisions = revisions, ledgerEvidence = evidence }
      certificationRoot = digestText $ Text.intercalate "|"
        [ "phil-llvm-phase0-client-control-send-proof-bound-certification-root-v1"
        , unDigest sourceDigest
        , unDigest systemsLoweringRoot
        , unDigest targetDigest
        , unDigest targetTextDigest
        , unDigest abiDigest
        , unDigest (artifactDigest proofBoundCert013)
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
      manifest = provisionalManifest { manifestId = deriveManifestId ledger provisionalManifest }
      explicitArtifacts = [translationArtifact, certificationArtifact, proofBoundCert013, proofArtifact]
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
      result = ClientControlSendProofCertificationBundle
        { clientControlSendProofSystems = systemsBundle
        , clientControlSendProofLLVM = llvmArtifact
        , clientControlSendProofArtifact = certificationArtifact
        , clientControlSendProofRecord = certificationRecord
        , clientControlSendProofLedger = ledger
        , clientControlSendProofManifest = manifest
        , clientControlSendProofContext = context
        }

  mapLeft ClientControlSendProofFinalManifestError $ verifyManifest context ledger manifest
  pure result

verifyPhase0ClientControlSendProofCertification
  :: RocqCertificationBundle
  -> Either ClientControlSendProofCertificationError ()
verifyPhase0ClientControlSendProofCertification proofBundle = do
  bundle <- phase0ClientControlSendProofCertification proofBundle
  mapLeft ClientControlSendProofFinalManifestError $
    verifyManifest
      (clientControlSendProofContext bundle)
      (clientControlSendProofLedger bundle)
      (clientControlSendProofManifest bundle)

renderClientControlSendProofCertification :: ClientControlSendProofCertificationBundle -> Text
renderClientControlSendProofCertification = clientControlSendProofRecord

verifyProof
  :: RocqCertificationSpec
  -> RocqCertificationBundle
  -> Either ClientControlSendProofCertificationError ()
verifyProof spec bundle = do
  let expected = rocqSpecObligation spec
      actual = rocqCertificateObligation (rocqBundleCertificate bundle)
  unless (actual == expected) $
    Left (ClientControlSendProofWrongProof expected actual)
  mapLeft (ClientControlSendProofManifestError "llvm-client-control-send") $
    verifyManifest
      (rocqBundleVerificationContext bundle)
      (rocqBundleLedger bundle)
      (rocqBundleManifest bundle)

renderArtifact :: ArtifactIdentity -> Text
renderArtifact artifact =
  unArtifactRef (artifactReference artifact) <> ";sha256=" <> unDigest (artifactDigest artifact)

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
