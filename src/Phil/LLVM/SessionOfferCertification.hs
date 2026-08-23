{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.SessionOfferCertification
  ( FinalResponseReceiveCertificationError (..)
  , FinalResponseReceiveCertificationBundle (..)
  , systemsFinalResponseCertificationSpec
  , llvmFinalResponseCertificationSpec
  , phase0FinalResponseReceiveLLVMCertification
  , verifyPhase0FinalResponseReceiveLLVMCertification
  , FinalResponseReceiveProofCertificationError (..)
  , FinalResponseReceiveProofCertificationBundle (..)
  , phase0FinalResponseReceiveProofCertification
  , verifyPhase0FinalResponseReceiveProofCertification
  , renderFinalResponseReceiveProofCertification
  ) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Rocq
import Phil.Assurance.Types
import Phil.Assurance.Verify (ManifestError, verifyManifest)
import Phil.Core.Syntax (ObligationId (..))
import Phil.LLVM.IR
import Phil.LLVM.RejectedResponseCertification
import Phil.LLVM.SessionOffer
import Phil.Systems.IR
import Phil.Systems.SessionChoice
import Phil.Systems.Verify (SystemsVerificationContext (..))

data FinalResponseReceiveCertificationError
  = FinalResponseReceiveCertificationSystemsError SessionChoiceError
  | FinalResponseReceiveCertificationTranslationError FinalResponseReceiveLLVMError
  | FinalResponseReceiveCertificationManifestError ManifestError
  deriving (Eq, Show)

data FinalResponseReceiveCertificationBundle = FinalResponseReceiveCertificationBundle
  { finalResponseReceiveCertificationSystems :: SessionChoiceBundle
  , finalResponseReceiveCertificationLLVM :: LLVMArtifact
  , finalResponseReceiveCertificationArtifact :: ArtifactIdentity
  , finalResponseReceiveCertificationLedger :: AssuranceLedger
  , finalResponseReceiveCertificationManifest :: AssuranceManifest
  , finalResponseReceiveCertificationContext :: VerificationContext
  }
  deriving (Eq, Show)

systemsFinalResponseCertificationSpec :: RocqCertificationSpec
systemsFinalResponseCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "systems-final-response"
  , rocqSpecObligation = ObligationId "PHIL-SYS-FINAL-RESPONSE-001"
  , rocqSpecClaim =
      "For the verified Phase 0 final-response session-choice candidate, the exact client transport carries the exact accepted/rejected labels, branch-local UploadId/DigestFailure payload identities and continuations; each payload-bearing arm has its dedicated sole-predecessor binder block; accepted records the exact UploadId exactly once; the frozen client has zero semantic uses of rejected DigestFailure and no cross-arm payload escape; the historical anonymous result Boolean and generic receive-label call are absent; and accepted/rejected terminate with exact source success/failure outcomes. The zero-use statement is exact-program-specific and is not a general representation theorem for DigestFailure."
  , rocqSpecKind = "Systems final-response semantic session choice"
  , rocqSpecOrigin =
      "src/Phil/Systems/SessionChoice.hs; proof/Phil/Systems/FinalResponse.v"
  , rocqSpecScope = "Phil.Systems final accepted/rejected session offer"
  , rocqSpecRepresentation =
      "normalized exact transport / semantic labels / branch-local payload binders / continuation model"
  , rocqSpecSubjects =
      [ "TransportHandle client.transport"
      , "accepted(client.upload_id : UploadId)"
      , "rejected(client.digest_failure : DigestFailure)"
      , "record_upload_id(client.upload_id)"
      , "exact accepted/rejected continuations"
      ]
  , rocqSpecTheorems =
      [ "verified_systems_final_response_reuses_rejected_authority"
      , "verified_systems_final_response_preserves_exact_offer"
      , "verified_systems_final_response_preserves_branch_payloads_and_targets"
      , "verified_systems_final_response_preserves_branch_locality"
      , "verified_systems_final_response_records_accepted_id_and_erases_no_semantics"
      , "verified_systems_final_response_eliminates_legacy_boolean_and_preserves_outcomes"
      , "systems_final_response_offer_or_transport_drift_is_rejected"
      , "systems_final_response_payload_target_or_binder_drift_is_rejected"
      , "systems_final_response_use_escape_or_legacy_drift_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Systems/FinalResponse.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Systems/FinalResponse.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-SYS-FINAL-RESPONSE-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-SYS-FINAL-RESPONSE-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness plus reviewed correspondence from concrete Haskell transport/label/payload/block identities, branch-local binder discipline, exact semantic use counts, and predecessor relation to the normalized proof model remain explicit trust boundaries. No physical response decoder, wire payload, or DigestFailure representation is proved at Systems level."
  }

llvmFinalResponseCertificationSpec :: RocqCertificationSpec
llvmFinalResponseCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "llvm-final-response-receive"
  , rocqSpecObligation = ObligationId "PHIL-LLVM-FINAL-RESPONSE-001"
  , rocqSpecClaim =
      "For final-response-receive-v1, verified lowering passes the exact client transport and caller-owned accepted out-slot to physical phil_runtime_receive_final_response(ptr,ptr)->i1, maps the exact accepted/rejected continuations, loads the runtime-private opaque UploadId handle only in the accepted binder block and passes that exact handle exactly once to phil_runtime_record_upload_id(ptr), preserves non-owning opacity and lifetime through that call, erases physical DigestFailure only under the exact-program no-use witness, eliminates generic/ambient final-response state, preserves already-materialized server accepted/rejected operations, and invents no malformed-response CFG edge."
  , rocqSpecKind = "LLVM final-response receive ABI v1"
  , rocqSpecOrigin =
      "docs/phase-0/final-response-receive-abi-v1.md; src/Phil/LLVM/SessionOffer.hs; src/Phil/LLVM/IR.hs; src/Phil/LLVM/Verify.hs; proof/Phil/LLVM/FinalResponseReceive.v"
  , rocqSpecScope = "Phil.LLVM final-response-receive-v1"
  , rocqSpecRepresentation =
      "normalized exact decoder operands / accepted out-slot / branch-local opaque UploadId / exact-program DigestFailure erasure model"
  , rocqSpecSubjects =
      [ "phil_runtime_receive_final_response(ptr,ptr)->i1"
      , "phil_runtime_record_upload_id(ptr)->void"
      , "exact client transport operand"
      , "caller-owned accepted UploadId out-slot"
      , "exact accepted/rejected target mapping"
      ]
  , rocqSpecTheorems =
      [ "verified_llvm_final_response_reuses_semantic_and_predecessor_authority"
      , "verified_llvm_final_response_preserves_decoder_boundary"
      , "verified_llvm_final_response_binds_and_records_accepted_upload_id"
      , "verified_llvm_final_response_preserves_upload_id_opacity"
      , "verified_llvm_final_response_erases_only_unobserved_digest_failure"
      , "verified_llvm_final_response_forbids_ambient_generic_and_malformed_edges"
      , "verified_llvm_final_response_preserves_server_response_operations"
      , "llvm_final_response_decoder_or_target_drift_is_rejected"
      , "llvm_final_response_upload_id_dataflow_drift_is_rejected"
      , "llvm_final_response_erasure_ambient_or_malformed_drift_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/LLVM/FinalResponseReceive.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/LLVM/FinalResponseReceive.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-LLVM-FINAL-RESPONSE-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-LLVM-FINAL-RESPONSE-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness; reviewed Systems/LLVM-to-normalized-proof correspondence; concrete LLVM pointer/calling-convention behavior; provider-side decoding/token materialization; accepted/rejected native execution; malformed-input non-return; physical write behavior; and outer framing remain explicit trust boundaries. UploadId provider representation remains runtime-private."
  }

-- PHIL-LLVM-CERT-008
--
-- This certificate covers only the exact Systems -> canonical pre-optimization
-- LLVM translation for final-response-receive-v1. Concrete wire parsing,
-- provider conformance, malformed-response non-return, LLVM 18 acceptance,
-- linking, and native execution remain separate external gates.
phase0FinalResponseReceiveLLVMCertification
  :: Either FinalResponseReceiveCertificationError FinalResponseReceiveCertificationBundle
phase0FinalResponseReceiveLLVMCertification = do
  systemsBundle <- mapLeft
    FinalResponseReceiveCertificationSystemsError
    phase0SessionChoiceBundle
  let systemsArtifact = sessionChoiceArtifact systemsBundle
      llvmArtifact = lowerSystemsFinalResponseReceive
        phase0FinalResponseReceiveLLVMTarget
        systemsArtifact
  mapLeft FinalResponseReceiveCertificationTranslationError $
    verifyFinalResponseReceiveTranslation systemsBundle llvmArtifact
  let systemsManifest = systemsAssuranceManifest (sessionChoiceContext systemsBundle)
      moduleValue = llvmArtifactModule llvmArtifact
      sourceDigest = llvmContractSourceDigest (llvmArtifactContract llvmArtifact)
      targetDigest = llvmContractTargetDigest (llvmArtifactContract llvmArtifact)
      targetTextDigest = digestText (llvmArtifactText llvmArtifact)
      abiDigest = llvmRuntimeABIDigest moduleValue
      certificationTarget = "preopt-llvm:" <> llvmTargetTriple moduleValue
      sourceCompilationProfile = Text.pack (show (llvmCompilationProfile moduleValue))
      certificationProfile =
        "translation-validation/" <> sourceCompilationProfile <> "/final-response-receive-v1"
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
        , ("final_response_decoder", "phil_runtime_receive_final_response(ptr,ptr)->i1")
        , ("record_upload_id", "phil_runtime_record_upload_id(ptr)->void")
        , ("accepted_wire", "0x01 || UploadIdToken[16]")
        , ("rejected_wire", "0x00 || 0x01")
        , ("accepted_binding", "decoder out-slot -> exact client.upload_id binder block")
        , ("digest_failure_erasure", "exact-program no-use erasure after Systems witness")
        , ("malformed_response", "provider must not return normally; no source CFG branch invented")
        , ("outer_framing", "not defined by final-response-receive-v1")
        , ("ambient_final_response_state", "forbidden")
        , ("ambient_upload_id_state", "forbidden")
        , ("runtime_symbol_identity", "physical primitive/signature")
        , ("external_runtime_gate", "exact decode/materialization/malformed behavior checked independently in CI")
        , ("external_llvm_gate", "canonical target text must be accepted by LLVM 18 in CI")
        ]
      evidenceScope = ValidityScope $
        Map.insert "target" certificationTarget $
        Map.insert "compilation_profile" certificationProfile validityContext
      revisionStatement =
        "The canonical Phase 0 final-response session-choice Systems -> pre-optimization LLVM pair is certified only for the exact source, target, target text, target profile, and phil-runtime/phase0/final-response-receive-v1 ABI bound by this revision; independent Phil translation validation establishes the exact client transport, accepted/rejected continuation mapping, branch-local accepted UploadId binding and record_upload_id use, exact-program erasure of unused DigestFailure, and absence of ambient/generic final-response state, while concrete response parsing, UploadId token materialization, malformed-input non-return, provider conformance, LLVM 18 acceptance, linking, and execution remain external certification gates."
      provisionalRevision = ObligationRevision
        { revisionObligationId = ObligationId "PHIL-LLVM-CERT-008"
        , revisionId = RevisionId ""
        , revisionStatement = revisionStatement
        , revisionStatementDigest = digestText revisionStatement
        , revisionKind = "LLVMFinalResponseReceiveTranslationCertification"
        , revisionOrigin = "final response receive ABI v1 / PHIL-LLVM-CERT-008"
        , revisionScope = "llvm.phase0.preopt.final-response-receive.translation"
        , revisionRequiredAt = "certification"
        , revisionRepresentation =
            "session-choice SystemsArtifact -> explicit final-response decoder canonical pre-optimization LLVMArtifact"
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
        [ "phil-llvm-phase0-final-response-receive-translation-validation-v1"
        , "source-digest=" <> unDigest sourceDigest
        , "target-digest=" <> unDigest targetDigest
        , "target-text-digest=" <> unDigest targetTextDigest
        , "llvm-language=" <> llvmLanguageVersion moduleValue
        , "llvm-tool-profile=" <> llvmToolVersion moduleValue
        , "target-triple=" <> llvmTargetTriple moduleValue
        , "data-layout=" <> llvmDataLayout moduleValue
        , "runtime-abi-digest=" <> unDigest abiDigest
        , "runtime-abi-profile=" <> llvmRuntimeABIProfile moduleValue
        , "translation-validator=Phil.LLVM.SessionOffer.verifyFinalResponseReceiveTranslation"
        , "assurance-checker=Phil.Assurance.Verify.verifyManifest"
        ]
      translationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef
            "artifact:phil:llvm:phase0:final-response-receive:translation-validation:v1"
        , artifactDigest = digestText translationArtifactRecord
        }
      evidenceId = EvidenceEntryId
        "evidence.llvm.phase0.final-response-receive.translation.validated"
      provisionalEvidence = EvidenceEntry
        { evidenceEntryId = evidenceId
        , evidenceEntryDigest = Digest ""
        , evidenceObligationRevision = certificationRevisionId
        , evidenceAssuranceKind = TranslationValidated
        , evidenceRole = EvidenceRole "translation_validated"
        , evidenceProducer = "Phil.LLVM.SessionOffer.verifyFinalResponseReceiveTranslation"
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
            [ "exact client transport SSA identity reaches final-response decoder"
            , "accepted and rejected Systems labels map to the exact target continuations"
            , "accepted runtime out-slot is loaded only in the accepted binder block"
            , "exact client UploadId reaches record_upload_id explicitly"
            , "unused DigestFailure has no physical target representation in this exact profile"
            , "generic final-response receive and record calls are eliminated"
            , "ambient final-response and UploadId state are absent"
            , "server accepted and rejected response operations are preserved"
            , "no malformed-response CFG edge is invented"
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
        [ "phil-llvm-phase0-final-response-receive-certification-root-v1"
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
  pure FinalResponseReceiveCertificationBundle
    { finalResponseReceiveCertificationSystems = systemsBundle
    , finalResponseReceiveCertificationLLVM = llvmArtifact
    , finalResponseReceiveCertificationArtifact = translationArtifact
    , finalResponseReceiveCertificationLedger = ledger
    , finalResponseReceiveCertificationManifest = manifest
    , finalResponseReceiveCertificationContext = verificationContext
    }

verifyPhase0FinalResponseReceiveLLVMCertification
  :: Either FinalResponseReceiveCertificationError ()
verifyPhase0FinalResponseReceiveLLVMCertification = do
  bundle <- phase0FinalResponseReceiveLLVMCertification
  mapLeft FinalResponseReceiveCertificationManifestError $
    verifyManifest
      (finalResponseReceiveCertificationContext bundle)
      (finalResponseReceiveCertificationLedger bundle)
      (finalResponseReceiveCertificationManifest bundle)

data FinalResponseReceiveProofCertificationError
  = FinalResponseReceiveProofCertificationBaseError FinalResponseReceiveCertificationError
  | FinalResponseReceiveProofCertificationPredecessorError RejectedResponseProofCertificationError
  | FinalResponseReceiveProofCertificationWrongProof Text ObligationId ObligationId
  | FinalResponseReceiveProofCertificationProofManifestError Text ManifestError
  | FinalResponseReceiveProofCertificationManifestError ManifestError
  deriving (Eq, Show)

data FinalResponseReceiveProofCertificationBundle = FinalResponseReceiveProofCertificationBundle
  { finalResponseReceiveProofCertificationBase :: FinalResponseReceiveCertificationBundle
  , finalResponseReceiveProofCertificationPredecessor :: RejectedResponseProofCertificationBundle
  , finalResponseReceiveProofCertificationArtifact :: ArtifactIdentity
  , finalResponseReceiveProofCertificationRecord :: Text
  , finalResponseReceiveProofCertificationLedger :: AssuranceLedger
  , finalResponseReceiveProofCertificationManifest :: AssuranceManifest
  , finalResponseReceiveProofCertificationContext :: VerificationContext
  }
  deriving (Eq, Show)

phase0FinalResponseReceiveProofCertification
  :: RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> Either FinalResponseReceiveProofCertificationError FinalResponseReceiveProofCertificationBundle
phase0FinalResponseReceiveProofCertification
    systemsFinalProof llvmFinalProof
    systemsRejectedProof llvmRejectedProof
    systemsAcceptedProof llvmAcceptedProof
    systemsStorageProof llvmStorageProof
    systemsDigestProof llvmDigestProof systemsRecordProof exactProof abiProof symbolProof = do
  verifyFinalProof "systems-final-response" systemsFinalResponseCertificationSpec systemsFinalProof
  verifyFinalProof "llvm-final-response" llvmFinalResponseCertificationSpec llvmFinalProof

  predecessor <- mapLeft FinalResponseReceiveProofCertificationPredecessorError $
    phase0RejectedResponseProofCertification
      systemsRejectedProof llvmRejectedProof
      systemsAcceptedProof llvmAcceptedProof
      systemsStorageProof llvmStorageProof
      systemsDigestProof llvmDigestProof systemsRecordProof exactProof abiProof symbolProof
  base <- mapLeft FinalResponseReceiveProofCertificationBaseError $
    phase0FinalResponseReceiveLLVMCertification

  let explicitProofBundles =
        [ systemsFinalProof
        , llvmFinalProof
        , systemsRejectedProof
        , llvmRejectedProof
        , systemsAcceptedProof
        , llvmAcceptedProof
        , systemsStorageProof
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
      predecessorArtifact = rejectedResponseProofCertificationArtifact predecessor

      systemsBundle = finalResponseReceiveCertificationSystems base
      systemsArtifact = sessionChoiceArtifact systemsBundle
      systemsManifest = systemsAssuranceManifest (sessionChoiceContext systemsBundle)
      llvmArtifact = finalResponseReceiveCertificationLLVM base
      moduleValue = llvmArtifactModule llvmArtifact
      translationArtifact = finalResponseReceiveCertificationArtifact base
      sourceDigest = llvmContractSourceDigest (llvmArtifactContract llvmArtifact)
      targetDigest = llvmContractTargetDigest (llvmArtifactContract llvmArtifact)
      targetTextDigest = digestText (llvmArtifactText llvmArtifact)
      abiDigest = llvmRuntimeABIDigest moduleValue
      systemsLoweringRoot = loweringLedgerRoot (systemsArtifactLoweringLedger systemsArtifact)
      certificationTarget = "preopt-llvm:" <> llvmTargetTriple moduleValue
      sourceCompilationProfile = Text.pack (show (llvmCompilationProfile moduleValue))
      certificationProfile =
        "translation-validation/" <> sourceCompilationProfile <> "/final-response-receive-v1/proof-bound"
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
        , ("final_response_decoder", "phil_runtime_receive_final_response(ptr,ptr)->i1")
        , ("final_response_transport", "exact client transport handle")
        , ("accepted_out_slot", "caller-owned slot receives runtime-private opaque UploadId handle")
        , ("accepted_binding", "out-slot loaded only in exact accepted binder block")
        , ("record_upload_id", "exact loaded UploadId handle reaches phil_runtime_record_upload_id(ptr) exactly once")
        , ("upload_id_ownership", "runtime-owned; generated code non-owning and opaque")
        , ("upload_id_lifetime", "guaranteed through exact record_upload_id call")
        , ("digest_failure_erasure", "physical representation erased only after exact-program zero-use Systems proof")
        , ("rejected_predecessor", "proof-bound rejected-response authority preserved")
        , ("predecessor_certification", unDigest (artifactDigest predecessorArtifact))
        , ("accepted_wire", "0x01 || UploadIdToken[16]; runtime evidence only")
        , ("rejected_wire", "0x00 || 0x01; runtime evidence only")
        , ("malformed_response", "provider must not return normally; no generated malformed CFG edge")
        , ("proof_assistant", "Rocq")
        , ("rocq_version", "9.2.0")
        , ("certificate_profile", "proof-assistant-theorem/v1")
        , ("external_llvm_gate", "canonical target text must be accepted by LLVM 18 in CI")
        , ("external_runtime_abi_gate", "provider signature conformance must pass independently in CI")
        , ("external_accepted_execution_gate", "accepted token materialization and exact record dataflow execute independently in CI")
        , ("external_rejected_execution_gate", "exact rejected response executes independently in CI")
        , ("external_malformed_gate", "truncated, overlong, reserved-tag, and reserved-reason responses must not return normally")
        , ("outer_framing", "not defined by final-response-receive-v1")
        ]
      evidenceScope = ValidityScope $
        Map.insert "target" certificationTarget $
        Map.insert "compilation_profile" certificationProfile validityContext
      revisionStatement =
        "The final-response-receive-v1 Systems -> canonical pre-optimization LLVM pair may be labeled Certified only when exact source/target/text digests, lowering root, target/runtime-ABI/tool identities, Systems final semantic-offer proof, LLVM decoder/out-slot/UploadId-dataflow/erasure proof, compatible rejected/accepted/storage/digest/exact-receive/recognized-record/runtime-symbol proof authority, and translation-validation result are content-bound; proof-bound CERT-007 is reproducible and digest-bound without importing evidence outside its rejected-response validity scope; DigestFailure physical erasure is justified only by the frozen client's exact zero-use proof; LLVM 18, provider ABI conformance, accepted/rejected native execution, malformed-input non-return, physical write behavior, and outer framing remain explicit external gates; and the assurance manifest closes over all selected evidence."
      provisionalRevision = ObligationRevision
        { revisionObligationId = ObligationId "PHIL-LLVM-CERT-008"
        , revisionId = RevisionId ""
        , revisionStatement = revisionStatement
        , revisionStatementDigest = digestText revisionStatement
        , revisionKind = "LLVMFinalResponseReceiveProofBoundCertification"
        , revisionOrigin = "final response receive ABI v1 / proof-bound PHIL-LLVM-CERT-008"
        , revisionScope = "llvm.phase0.preopt.final-response-receive.proof-bound"
        , revisionRequiredAt = "certification"
        , revisionRepresentation =
            "session-choice SystemsArtifact -> final-response-receive-v1 canonical pre-optimization LLVMArtifact + proof authority"
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
        "evidence.llvm.phase0.final-response-receive.proof-bound.translation.validated"
      provisionalTranslationEvidence = EvidenceEntry
        { evidenceEntryId = translationEvidenceId
        , evidenceEntryDigest = Digest ""
        , evidenceObligationRevision = certificationRevisionId
        , evidenceAssuranceKind = TranslationValidated
        , evidenceRole = EvidenceRole "translation_validated"
        , evidenceProducer = "Phil.LLVM.SessionOffer.verifyFinalResponseReceiveTranslation"
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
            [ "exact client transport and accepted/rejected semantic continuation mapping"
            , "caller-owned accepted out-slot and accepted-only branch-local UploadId load"
            , "exact loaded UploadId reaches record_upload_id explicitly exactly once"
            , "generated code preserves runtime-private UploadId opacity, non-ownership, and lifetime through record call"
            , "DigestFailure physical representation is erased only under exact-program zero-use proof"
            , "generic receive/record calls and ambient final-response/current-ID state are absent"
            , "server accepted and rejected response operations remain preserved"
            , "no malformed-response CFG edge is invented"
            , "content-bound reproduction of proof-bound rejected-response predecessor authority"
            ]
        , evidenceRuntimeMechanism = Nothing
        , evidenceRuntimeResidue = []
        , evidenceCostRefs = []
        }
      translationEvidence = provisionalTranslationEvidence
        { evidenceEntryDigest = deriveEvidenceEntryDigest provisionalTranslationEvidence }
      certificationRecord = Text.unlines $
        [ "phil-llvm-phase0-final-response-receive-certification/v1"
        , "obligation=PHIL-LLVM-CERT-008"
        , "revision=" <> unRevisionId certificationRevisionId
        , "source-digest=" <> unDigest sourceDigest
        , "systems-lowering-root=" <> unDigest systemsLoweringRoot
        , "target-digest=" <> unDigest targetDigest
        , "target-text-digest=" <> unDigest targetTextDigest
        , "runtime-abi-profile=" <> llvmRuntimeABIProfile moduleValue
        , "runtime-abi-digest=" <> unDigest abiDigest
        , "translation-artifact=" <> renderFinalArtifact translationArtifact
        , "predecessor-certification=" <> renderFinalArtifact predecessorArtifact
        ] <> map renderFinalProofArtifact explicitProofBundles <>
        [ "external-llvm-gate=LLVM 18 assembler acceptance required"
        , "external-runtime-abi-gate=provider signature conformance required"
        , "external-accepted-execution-gate=accepted token materialization and record dataflow execution required"
        , "external-rejected-execution-gate=exact rejected execution required"
        , "external-malformed-gate=malformed/truncated/overlong/reserved responses must not return normally"
        , "residual-write-failure=source has no decoder/write failure continuation"
        , "residual-outer-framing=not defined by final-response-receive-v1"
        , "semantic-note=DigestFailure erasure is exact-program zero-use only, not a general representation theorem"
        ]
      certificationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef "certificate:phil:llvm:PHIL-LLVM-CERT-008:v1"
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
        [ "phil-llvm-phase0-final-response-receive-proof-bound-certification-root-v1"
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
      bundle = FinalResponseReceiveProofCertificationBundle
        { finalResponseReceiveProofCertificationBase = base
        , finalResponseReceiveProofCertificationPredecessor = predecessor
        , finalResponseReceiveProofCertificationArtifact = certificationArtifact
        , finalResponseReceiveProofCertificationRecord = certificationRecord
        , finalResponseReceiveProofCertificationLedger = ledger
        , finalResponseReceiveProofCertificationManifest = manifest
        , finalResponseReceiveProofCertificationContext = verificationContext
        }

  mapLeft FinalResponseReceiveProofCertificationManifestError $
    verifyManifest verificationContext ledger manifest
  pure bundle

verifyPhase0FinalResponseReceiveProofCertification
  :: RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> Either FinalResponseReceiveProofCertificationError ()
verifyPhase0FinalResponseReceiveProofCertification
    systemsFinalProof llvmFinalProof
    systemsRejectedProof llvmRejectedProof
    systemsAcceptedProof llvmAcceptedProof
    systemsStorageProof llvmStorageProof
    systemsDigestProof llvmDigestProof systemsRecordProof exactProof abiProof symbolProof = do
  bundle <- phase0FinalResponseReceiveProofCertification
    systemsFinalProof llvmFinalProof
    systemsRejectedProof llvmRejectedProof
    systemsAcceptedProof llvmAcceptedProof
    systemsStorageProof llvmStorageProof
    systemsDigestProof llvmDigestProof systemsRecordProof exactProof abiProof symbolProof
  mapLeft FinalResponseReceiveProofCertificationManifestError $
    verifyManifest
      (finalResponseReceiveProofCertificationContext bundle)
      (finalResponseReceiveProofCertificationLedger bundle)
      (finalResponseReceiveProofCertificationManifest bundle)

renderFinalResponseReceiveProofCertification :: FinalResponseReceiveProofCertificationBundle -> Text
renderFinalResponseReceiveProofCertification = finalResponseReceiveProofCertificationRecord

verifyFinalProof
  :: Text
  -> RocqCertificationSpec
  -> RocqCertificationBundle
  -> Either FinalResponseReceiveProofCertificationError ()
verifyFinalProof label spec bundle = do
  let expected = rocqSpecObligation spec
      actual = rocqCertificateObligation (rocqBundleCertificate bundle)
  unless (actual == expected) $
    Left (FinalResponseReceiveProofCertificationWrongProof label expected actual)
  mapLeft (FinalResponseReceiveProofCertificationProofManifestError label) $
    verifyManifest
      (rocqBundleVerificationContext bundle)
      (rocqBundleLedger bundle)
      (rocqBundleManifest bundle)

renderFinalArtifact :: ArtifactIdentity -> Text
renderFinalArtifact artifact =
  unArtifactRef (artifactReference artifact) <> ";sha256=" <> unDigest (artifactDigest artifact)

renderFinalProofArtifact :: RocqCertificationBundle -> Text
renderFinalProofArtifact bundle =
  let certificate = rocqBundleCertificate bundle
      artifact = rocqBundleCertificateArtifact bundle
  in "proof=" <> unObligationId (rocqCertificateObligation certificate)
      <> ";artifact=" <> unArtifactRef (artifactReference artifact)
      <> ";sha256=" <> unDigest (artifactDigest artifact)

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
