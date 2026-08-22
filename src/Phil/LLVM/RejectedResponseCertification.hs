{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.RejectedResponseCertification
  ( RejectedResponseCertificationError (..)
  , RejectedResponseCertificationBundle (..)
  , phase0RejectedResponseLLVMCertification
  , verifyPhase0RejectedResponseLLVMCertification
  , systemsRejectedResponseCertificationSpec
  , llvmRejectedResponseCertificationSpec
  , RejectedResponseProofCertificationError (..)
  , RejectedResponseProofCertificationBundle (..)
  , phase0RejectedResponseProofCertification
  , verifyPhase0RejectedResponseProofCertification
  , renderRejectedResponseProofCertification
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
import Phil.LLVM.AcceptedResponseCertification
import Phil.LLVM.IR
import Phil.LLVM.RejectedResponse
import Phil.Systems.IR
import Phil.Systems.RejectedResponse
import Phil.Systems.Verify (SystemsVerificationContext (..))

data RejectedResponseCertificationError
  = RejectedResponseCertificationSystemsError RejectedResponseError
  | RejectedResponseCertificationTranslationError RejectedResponseLLVMError
  | RejectedResponseCertificationManifestError ManifestError
  deriving (Eq, Show)

data RejectedResponseCertificationBundle = RejectedResponseCertificationBundle
  { rejectedResponseCertificationSystems :: RejectedResponseBundle
  , rejectedResponseCertificationLLVM :: LLVMArtifact
  , rejectedResponseCertificationArtifact :: ArtifactIdentity
  , rejectedResponseCertificationLedger :: AssuranceLedger
  , rejectedResponseCertificationManifest :: AssuranceManifest
  , rejectedResponseCertificationContext :: VerificationContext
  }
  deriving (Eq, Show)

systemsRejectedResponseCertificationSpec :: RocqCertificationSpec
systemsRejectedResponseCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "systems-rejected-response"
  , rocqSpecObligation = ObligationId "PHIL-SYS-REJECTED-001"
  , rocqSpecClaim =
      "For the verified Phase 0 rejected-response candidate, the exact DigestBoundary failure edge reaches the exact rejected block; the exact payload owner is released before the sole select rejected operation; the exact component transport is used with no outputs or runtime-site authority; this frozen program exposes exactly one peer-observable digest-failure equivalence class, DigestMismatch; and the block terminates with the exact source failure outcome. This is not a claim that abstract DigestFailure has only one inhabitant."
  , rocqSpecKind = "Systems rejected-response semantic identity"
  , rocqSpecOrigin =
      "src/Phil/Systems/RejectedResponse.hs; src/Phil/Systems/AcceptedResponse.hs; proof/Phil/Systems/RejectedResponse.v"
  , rocqSpecScope = "Phil.Systems rejected-response boundary"
  , rocqSpecRepresentation =
      "normalized digest-failure / release-before-select / singleton-observable-class / failure-termination model"
  , rocqSpecSubjects =
      [ "DigestBoundary failure edge"
      , "OwnedBuffer server.payload"
      , "TransportHandle server.transport"
      , "select rejected"
      , "observable DigestMismatch equivalence class"
      ]
  , rocqSpecTheorems =
      [ "verified_systems_rejected_reuses_accepted_authority"
      , "verified_systems_rejected_uses_exact_digest_failure_edge"
      , "verified_systems_rejected_releases_exact_payload_before_select"
      , "verified_systems_rejected_uses_exact_transport"
      , "verified_systems_rejected_has_single_observable_digest_mismatch_class"
      , "verified_systems_rejected_has_exact_selector_shape_and_failure_termination"
      , "systems_rejected_digest_edge_drift_is_rejected"
      , "systems_rejected_release_drift_is_rejected"
      , "systems_rejected_transport_drift_is_rejected"
      , "systems_rejected_observable_class_drift_is_rejected"
      , "systems_rejected_selector_or_termination_drift_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Systems/RejectedResponse.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Systems/RejectedResponse.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-SYS-REJECTED-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-SYS-REJECTED-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness plus reviewed correspondence from concrete Haskell ValueId/BlockId identities, DigestBoundary predecessor inspection, operation ordering, owner release identity, and the frozen program's observational DigestFailure quotient to the normalized proof model remain explicit trust boundaries. Numeric reason representation and wire encoding are not proved at Systems level."
  }

llvmRejectedResponseCertificationSpec :: RocqCertificationSpec
llvmRejectedResponseCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "llvm-rejected-response"
  , rocqSpecObligation = ObligationId "PHIL-LLVM-REJECTED-001"
  , rocqSpecClaim =
      "For rejected-response-v1, verified lowering preserves the exact digest-failure edge, releases the exact digest payload owner before response emission, passes the exact component transport to physical phil_runtime_select_rejected(ptr,i8), maps this frozen program's single observable DigestMismatch class to canonical one-octet reason code 0x01, preserves exact source failure termination and proof-bound accepted-response authority, and rejects ambient/nullary/generic rejection state, unauthorized strengthening, operand/edge/reason drift, or evidence-derived runtime symbols."
  , rocqSpecKind = "LLVM rejected-response ABI v1"
  , rocqSpecOrigin =
      "docs/phase-0/rejected-response-abi-v1.md; src/Phil/LLVM/RejectedResponse.hs; src/Phil/LLVM/IR.hs; src/Phil/LLVM/Verify.hs; proof/Phil/LLVM/RejectedResponse.v"
  , rocqSpecScope = "Phil.LLVM rejected-response-v1"
  , rocqSpecRepresentation =
      "normalized digest-failure / release-before-selector / exact transport / i8 DigestMismatch reason model"
  , rocqSpecSubjects =
      [ "phil_runtime_select_rejected(ptr,i8)"
      , "exact digest-failure block"
      , "exact released payload owner"
      , "exact server transport operand"
      , "DigestMismatch -> i8 0x01 for the frozen program"
      ]
  , rocqSpecTheorems =
      [ "verified_llvm_rejected_reuses_systems_rejected_authority"
      , "verified_llvm_rejected_reuses_accepted_response_authority"
      , "verified_llvm_rejected_reuses_runtime_symbol_authority"
      , "verified_llvm_rejected_preserves_exact_digest_failure_edge"
      , "verified_llvm_rejected_releases_exact_digest_payload_before_selector"
      , "verified_llvm_rejected_preserves_exact_transport_operand"
      , "verified_llvm_rejected_maps_single_observable_digest_mismatch_to_reason_0x01"
      , "verified_llvm_rejected_uses_physical_selector_and_preserves_failure"
      , "verified_llvm_rejected_forbids_ambient_nullary_generic_strengthening_and_evidence_symbols"
      , "llvm_rejected_transport_drift_is_rejected"
      , "llvm_rejected_release_owner_or_order_drift_is_rejected"
      , "llvm_rejected_block_or_digest_edge_drift_is_rejected"
      , "llvm_rejected_reason_representation_drift_is_rejected"
      , "llvm_rejected_selector_or_termination_drift_is_rejected"
      , "llvm_rejected_ambient_or_symbol_drift_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/LLVM/RejectedResponse.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/LLVM/RejectedResponse.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-LLVM-REJECTED-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-LLVM-REJECTED-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness; reviewed Systems/LLVM-to-normalized-proof correspondence; concrete LLVM i8 representation and calling convention; provider-side two-octet encoder behavior; physical write behavior; outer framing; and native execution remain explicit trust boundaries. The singleton result is observational and program-specific, not a cardinality theorem for DigestFailure."
  }

-- PHIL-LLVM-CERT-007
--
-- Content-bound to rejected-response-v1. Exact two-octet encoder behavior,
-- provider conformance, LLVM 18 acceptance, linking, and native execution are
-- external gates rather than claims of this pure translation certificate.
phase0RejectedResponseLLVMCertification
  :: Either RejectedResponseCertificationError RejectedResponseCertificationBundle
phase0RejectedResponseLLVMCertification = do
  systemsBundle <- mapLeft
    RejectedResponseCertificationSystemsError
    phase0RejectedResponseBundle
  let systemsArtifact = rejectedResponseArtifact systemsBundle
      llvmArtifact = lowerSystemsRejectedResponse
        phase0RejectedResponseLLVMTarget
        systemsArtifact
  mapLeft RejectedResponseCertificationTranslationError $
    verifyRejectedResponseTranslation systemsBundle llvmArtifact
  let systemsManifest = systemsAssuranceManifest (rejectedResponseContext systemsBundle)
      moduleValue = llvmArtifactModule llvmArtifact
      sourceDigest = llvmContractSourceDigest (llvmArtifactContract llvmArtifact)
      targetDigest = llvmContractTargetDigest (llvmArtifactContract llvmArtifact)
      targetTextDigest = digestText (llvmArtifactText llvmArtifact)
      abiDigest = llvmRuntimeABIDigest moduleValue
      certificationTarget = "preopt-llvm:" <> llvmTargetTriple moduleValue
      sourceCompilationProfile = Text.pack (show (llvmCompilationProfile moduleValue))
      certificationProfile =
        "translation-validation/" <> sourceCompilationProfile <> "/rejected-response-v1"
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
        , ("rejected_selector", "phil_runtime_select_rejected(ptr,i8)->void")
        , ("rejected_transport", "exact component transport handle")
        , ("rejected_wire", "2 octets: 0x00 || 0x01")
        , ("rejected_reason", "0x01 = DigestMismatch; all other v1 codes reserved")
        , ("reason_lowering", "digest-failure control-flow singleton -> i8 0x01")
        , ("diagnostic_detail", "not protocol data")
        , ("outer_framing", "not defined by rejected-response-v1")
        , ("write_failure", "residual runtime assumption; source provides no select-failure edge")
        , ("ambient_rejected_state", "forbidden")
        , ("runtime_symbol_identity", "physical primitive/signature")
        , ("external_runtime_gate", "provider signatures and exact rejected-response bytes are checked independently in CI")
        , ("external_llvm_gate", "canonical target text must be accepted by LLVM 18 in CI")
        ]
      evidenceScope = ValidityScope $
        Map.insert "target" certificationTarget $
        Map.insert "compilation_profile" certificationProfile validityContext
      revisionStatement =
        "The canonical Phase 0 rejected-response Systems -> pre-optimization LLVM pair is certified only for the exact source, target, target text, target profile, and phil-runtime/phase0/rejected-response-v1 ABI bound by this revision; independent Phil translation validation establishes the exact digest-failure edge, payload release, exact transport, and singleton DigestMismatch reason code at select rejected(reason), while exact two-octet runtime encoding, provider conformance, LLVM 18 acceptance, linking, and execution remain external certification gates."
      provisionalRevision = ObligationRevision
        { revisionObligationId = ObligationId "PHIL-LLVM-CERT-007"
        , revisionId = RevisionId ""
        , revisionStatement = revisionStatement
        , revisionStatementDigest = digestText revisionStatement
        , revisionKind = "LLVMRejectedResponseTranslationCertification"
        , revisionOrigin = "rejected response ABI v1 / PHIL-LLVM-CERT-007"
        , revisionScope = "llvm.phase0.preopt.rejected-response.translation"
        , revisionRequiredAt = "certification"
        , revisionRepresentation =
            "accepted-response-witnessed SystemsArtifact -> explicit rejected-response canonical pre-optimization LLVMArtifact"
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
        [ "phil-llvm-phase0-rejected-response-translation-validation-v1"
        , "source-digest=" <> unDigest sourceDigest
        , "target-digest=" <> unDigest targetDigest
        , "target-text-digest=" <> unDigest targetTextDigest
        , "llvm-language=" <> llvmLanguageVersion moduleValue
        , "llvm-tool-profile=" <> llvmToolVersion moduleValue
        , "target-triple=" <> llvmTargetTriple moduleValue
        , "data-layout=" <> llvmDataLayout moduleValue
        , "runtime-abi-digest=" <> unDigest abiDigest
        , "runtime-abi-profile=" <> llvmRuntimeABIProfile moduleValue
        , "translation-validator=Phil.LLVM.RejectedResponse.verifyRejectedResponseTranslation"
        , "assurance-checker=Phil.Assurance.Verify.verifyManifest"
        ]
      translationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef
            "artifact:phil:llvm:phase0:rejected-response:translation-validation:v1"
        , artifactDigest = digestText translationArtifactRecord
        }
      evidenceId = EvidenceEntryId
        "evidence.llvm.phase0.rejected-response.translation.validated"
      provisionalEvidence = EvidenceEntry
        { evidenceEntryId = evidenceId
        , evidenceEntryDigest = Digest ""
        , evidenceObligationRevision = certificationRevisionId
        , evidenceAssuranceKind = TranslationValidated
        , evidenceRole = EvidenceRole "translation_validated"
        , evidenceProducer = "Phil.LLVM.RejectedResponse.verifyRejectedResponseTranslation"
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
            [ "exact digest-failure control-flow edge reaches the rejected response"
            , "exact payload owner is released before rejected response emission"
            , "exact rejected-response transport SSA identity"
            , "DigestMismatch is encoded as explicit i8 reason code 0x01"
            , "generic nullary select rejected call is eliminated"
            , "ambient rejection and last-digest-error state are absent"
            , "accepted response remains operand-explicit in the successor profile"
            , "rejected block terminates with exact source failure outcome"
            , "physical encoder symbol identity is independent of assurance claim names"
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
        [ "phil-llvm-phase0-rejected-response-certification-root-v1"
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
  pure RejectedResponseCertificationBundle
    { rejectedResponseCertificationSystems = systemsBundle
    , rejectedResponseCertificationLLVM = llvmArtifact
    , rejectedResponseCertificationArtifact = translationArtifact
    , rejectedResponseCertificationLedger = ledger
    , rejectedResponseCertificationManifest = manifest
    , rejectedResponseCertificationContext = verificationContext
    }

verifyPhase0RejectedResponseLLVMCertification
  :: Either RejectedResponseCertificationError ()
verifyPhase0RejectedResponseLLVMCertification = do
  bundle <- phase0RejectedResponseLLVMCertification
  mapLeft RejectedResponseCertificationManifestError $
    verifyManifest
      (rejectedResponseCertificationContext bundle)
      (rejectedResponseCertificationLedger bundle)
      (rejectedResponseCertificationManifest bundle)

data RejectedResponseProofCertificationError
  = RejectedResponseProofCertificationBaseError RejectedResponseCertificationError
  | RejectedResponseProofCertificationPredecessorError AcceptedResponseProofCertificationError
  | RejectedResponseProofCertificationWrongProof Text ObligationId ObligationId
  | RejectedResponseProofCertificationProofManifestError Text ManifestError
  | RejectedResponseProofCertificationManifestError ManifestError
  deriving (Eq, Show)

data RejectedResponseProofCertificationBundle = RejectedResponseProofCertificationBundle
  { rejectedResponseProofCertificationBase :: RejectedResponseCertificationBundle
  , rejectedResponseProofCertificationPredecessor :: AcceptedResponseProofCertificationBundle
  , rejectedResponseProofCertificationArtifact :: ArtifactIdentity
  , rejectedResponseProofCertificationRecord :: Text
  , rejectedResponseProofCertificationLedger :: AssuranceLedger
  , rejectedResponseProofCertificationManifest :: AssuranceManifest
  , rejectedResponseProofCertificationContext :: VerificationContext
  }
  deriving (Eq, Show)

phase0RejectedResponseProofCertification
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
  -> Either RejectedResponseProofCertificationError RejectedResponseProofCertificationBundle
phase0RejectedResponseProofCertification
    systemsRejectedProof llvmRejectedProof
    systemsAcceptedProof llvmAcceptedProof
    systemsStorageProof llvmStorageProof
    systemsDigestProof llvmDigestProof systemsRecordProof exactProof abiProof symbolProof = do
  verifyRejectedProof "systems-rejected-response" systemsRejectedResponseCertificationSpec systemsRejectedProof
  verifyRejectedProof "llvm-rejected-response" llvmRejectedResponseCertificationSpec llvmRejectedProof
  verifyRejectedProof "systems-accepted-response" systemsAcceptedResponseCertificationSpec systemsAcceptedProof
  verifyRejectedProof "llvm-accepted-response" llvmAcceptedResponseCertificationSpec llvmAcceptedProof
  verifyRejectedProof "systems-storage" systemsStorageCertificationSpec systemsStorageProof
  verifyRejectedProof "llvm-storage" llvmStorageCertificationSpec llvmStorageProof
  verifyRejectedProof "systems-digest-validation" systemsDigestValidationCertificationSpec systemsDigestProof
  verifyRejectedProof "llvm-digest-validation" llvmDigestValidationCertificationSpec llvmDigestProof
  verifyRejectedProof "systems-recognized-record" systemsRecognizedRecordCertificationSpec systemsRecordProof
  verifyRejectedProof "llvm-exact-receive" llvmExactReceiveCertificationSpec exactProof
  verifyRejectedProof "llvm-recognized-record-abi" llvmRecognizedRecordABICertificationSpec abiProof
  verifyRejectedProof "llvm-runtime-symbol-identity" llvmRuntimeSymbolCertificationSpec symbolProof

  predecessor <- mapLeft RejectedResponseProofCertificationPredecessorError $
    phase0AcceptedResponseProofCertification
      systemsAcceptedProof llvmAcceptedProof
      systemsStorageProof llvmStorageProof
      systemsDigestProof llvmDigestProof systemsRecordProof exactProof abiProof symbolProof
  base <- mapLeft RejectedResponseProofCertificationBaseError $
    phase0RejectedResponseLLVMCertification

  let explicitProofBundles =
        [ systemsRejectedProof
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
      predecessorArtifact = acceptedResponseProofCertificationArtifact predecessor

      systemsBundle = rejectedResponseCertificationSystems base
      systemsArtifact = rejectedResponseArtifact systemsBundle
      systemsManifest = systemsAssuranceManifest (rejectedResponseContext systemsBundle)
      llvmArtifact = rejectedResponseCertificationLLVM base
      moduleValue = llvmArtifactModule llvmArtifact
      translationArtifact = rejectedResponseCertificationArtifact base
      sourceDigest = llvmContractSourceDigest (llvmArtifactContract llvmArtifact)
      targetDigest = llvmContractTargetDigest (llvmArtifactContract llvmArtifact)
      targetTextDigest = digestText (llvmArtifactText llvmArtifact)
      abiDigest = llvmRuntimeABIDigest moduleValue
      systemsLoweringRoot = loweringLedgerRoot (systemsArtifactLoweringLedger systemsArtifact)
      certificationTarget = "preopt-llvm:" <> llvmTargetTriple moduleValue
      sourceCompilationProfile = Text.pack (show (llvmCompilationProfile moduleValue))
      certificationProfile =
        "translation-validation/" <> sourceCompilationProfile <> "/rejected-response-v1/proof-bound"
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
        , ("rejected_selector", "phil_runtime_select_rejected(ptr,i8)->void")
        , ("rejected_transport", "exact server transport handle")
        , ("rejected_predecessor", "exact digest-failure edge reaches rejected block")
        , ("rejected_release", "exact digest payload owner released before rejected selector")
        , ("observable_failure_class", "frozen program exposes exactly one peer-visible digest-failure class: DigestMismatch")
        , ("reason_representation", "for this exact program DigestMismatch maps to canonical i8 0x01")
        , ("abstract_digest_failure", "not asserted singleton; richer future programs require richer representation")
        , ("accepted_response_predecessor", "proof-bound accepted-response authority is preserved")
        , ("rejected_wire", "2 octets: 0x00 || 0x01; runtime evidence only")
        , ("diagnostic_detail", "not protocol data")
        , ("predecessor_certification", unDigest (artifactDigest predecessorArtifact))
        , ("proof_assistant", "Rocq")
        , ("rocq_version", "9.2.0")
        , ("certificate_profile", "proof-assistant-theorem/v1")
        , ("external_llvm_gate", "canonical target text must be accepted by LLVM 18 in CI")
        , ("external_runtime_abi_gate", "provider signature conformance must pass independently in CI")
        , ("external_wire_gate", "exact two-octet rejected bytes, release ordering, and no accepted/storage emission must execute independently in CI")
        , ("outer_framing", "not defined by rejected-response-v1")
        , ("write_failure", "residual runtime assumption; source has no rejected-select failure edge")
        ]
      evidenceScope = ValidityScope $
        Map.insert "target" certificationTarget $
        Map.insert "compilation_profile" certificationProfile validityContext
      revisionStatement =
        "The rejected-response-v1 Systems -> canonical pre-optimization LLVM pair may be labeled Certified only when exact source/target/text digests, lowering root, target/runtime-ABI/tool identities, Systems rejected-response proof, LLVM rejected-response/reason-representation proof, compatible accepted/storage/digest/exact-receive/recognized-record/runtime-symbol proof authority, and translation-validation result are content-bound; proof-bound CERT-006 is reproducible and digest-bound without importing evidence outside its accepted-response validity scope; the singleton DigestMismatch statement is explicitly observational for this frozen program rather than a cardinality claim about DigestFailure; LLVM 18, exact two-octet provider encoding, physical write behavior, and runtime ABI conformance remain explicit external gates; and the assurance manifest closes over all selected evidence."
      provisionalRevision = ObligationRevision
        { revisionObligationId = ObligationId "PHIL-LLVM-CERT-007"
        , revisionId = RevisionId ""
        , revisionStatement = revisionStatement
        , revisionStatementDigest = digestText revisionStatement
        , revisionKind = "LLVMRejectedResponseProofBoundCertification"
        , revisionOrigin = "rejected response ABI v1 / proof-bound PHIL-LLVM-CERT-007"
        , revisionScope = "llvm.phase0.preopt.rejected-response.proof-bound"
        , revisionRequiredAt = "certification"
        , revisionRepresentation =
            "accepted-response-witnessed SystemsArtifact -> rejected-response-v1 canonical pre-optimization LLVMArtifact + proof authority"
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
        "evidence.llvm.phase0.rejected-response.proof-bound.translation.validated"
      provisionalTranslationEvidence = EvidenceEntry
        { evidenceEntryId = translationEvidenceId
        , evidenceEntryDigest = Digest ""
        , evidenceObligationRevision = certificationRevisionId
        , evidenceAssuranceKind = TranslationValidated
        , evidenceRole = EvidenceRole "translation_validated"
        , evidenceProducer = "Phil.LLVM.RejectedResponse.verifyRejectedResponseTranslation"
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
            [ "exact DigestBoundary failure -> rejected-response boundary"
            , "exact digest payload owner release before response emission"
            , "exact server transport operand identity"
            , "single peer-observable DigestMismatch equivalence class for the frozen program"
            , "canonical i8 0x01 representation for that exact observable class"
            , "physical rejected-selector symbol identity"
            , "exact source failure termination"
            , "absence of nullary/generic selector, ambient rejection/reason/digest-error state, unauthorized strengthening, and evidence-derived runtime symbols"
            , "content-bound reproduction of proof-bound accepted-response predecessor authority"
            ]
        , evidenceRuntimeMechanism = Nothing
        , evidenceRuntimeResidue = []
        , evidenceCostRefs = []
        }
      translationEvidence = provisionalTranslationEvidence
        { evidenceEntryDigest = deriveEvidenceEntryDigest provisionalTranslationEvidence }
      certificationRecord = Text.unlines $
        [ "phil-llvm-phase0-rejected-response-certification/v1"
        , "obligation=PHIL-LLVM-CERT-007"
        , "revision=" <> unRevisionId certificationRevisionId
        , "source-digest=" <> unDigest sourceDigest
        , "systems-lowering-root=" <> unDigest systemsLoweringRoot
        , "target-digest=" <> unDigest targetDigest
        , "target-text-digest=" <> unDigest targetTextDigest
        , "runtime-abi-profile=" <> llvmRuntimeABIProfile moduleValue
        , "runtime-abi-digest=" <> unDigest abiDigest
        , "translation-artifact=" <> renderRejectedArtifact translationArtifact
        , "predecessor-certification=" <> renderRejectedArtifact predecessorArtifact
        ] <> map renderRejectedProofArtifact explicitProofBundles <>
        [ "external-llvm-gate=LLVM 18 assembler acceptance required"
        , "external-runtime-abi-gate=provider signature conformance required"
        , "external-wire-gate=exact 2-octet rejected encoding, release-before-emission, and no accepted/storage emission execution required"
        , "residual-write-failure=source has no rejected-select failure edge"
        , "residual-outer-framing=not defined by rejected-response-v1"
        , "semantic-note=DigestMismatch singleton is observational for this frozen program, not a cardinality theorem for DigestFailure"
        ]
      certificationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef "certificate:phil:llvm:PHIL-LLVM-CERT-007:v1"
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
        [ "phil-llvm-phase0-rejected-response-proof-bound-certification-root-v1"
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
      bundle = RejectedResponseProofCertificationBundle
        { rejectedResponseProofCertificationBase = base
        , rejectedResponseProofCertificationPredecessor = predecessor
        , rejectedResponseProofCertificationArtifact = certificationArtifact
        , rejectedResponseProofCertificationRecord = certificationRecord
        , rejectedResponseProofCertificationLedger = ledger
        , rejectedResponseProofCertificationManifest = manifest
        , rejectedResponseProofCertificationContext = verificationContext
        }

  mapLeft RejectedResponseProofCertificationManifestError $
    verifyManifest verificationContext ledger manifest
  pure bundle

verifyPhase0RejectedResponseProofCertification
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
  -> Either RejectedResponseProofCertificationError ()
verifyPhase0RejectedResponseProofCertification
    systemsRejectedProof llvmRejectedProof
    systemsAcceptedProof llvmAcceptedProof
    systemsStorageProof llvmStorageProof
    systemsDigestProof llvmDigestProof systemsRecordProof exactProof abiProof symbolProof = do
  bundle <- phase0RejectedResponseProofCertification
    systemsRejectedProof llvmRejectedProof
    systemsAcceptedProof llvmAcceptedProof
    systemsStorageProof llvmStorageProof
    systemsDigestProof llvmDigestProof systemsRecordProof exactProof abiProof symbolProof
  mapLeft RejectedResponseProofCertificationManifestError $
    verifyManifest
      (rejectedResponseProofCertificationContext bundle)
      (rejectedResponseProofCertificationLedger bundle)
      (rejectedResponseProofCertificationManifest bundle)

renderRejectedResponseProofCertification :: RejectedResponseProofCertificationBundle -> Text
renderRejectedResponseProofCertification = rejectedResponseProofCertificationRecord

verifyRejectedProof
  :: Text
  -> RocqCertificationSpec
  -> RocqCertificationBundle
  -> Either RejectedResponseProofCertificationError ()
verifyRejectedProof label spec bundle = do
  let expected = rocqSpecObligation spec
      actual = rocqCertificateObligation (rocqBundleCertificate bundle)
  unless (actual == expected) $
    Left (RejectedResponseProofCertificationWrongProof label expected actual)
  mapLeft (RejectedResponseProofCertificationProofManifestError label) $
    verifyManifest
      (rocqBundleVerificationContext bundle)
      (rocqBundleLedger bundle)
      (rocqBundleManifest bundle)

renderRejectedArtifact :: ArtifactIdentity -> Text
renderRejectedArtifact artifact =
  unArtifactRef (artifactReference artifact) <> ";sha256=" <> unDigest (artifactDigest artifact)

renderRejectedProofArtifact :: RocqCertificationBundle -> Text
renderRejectedProofArtifact bundle =
  let certificate = rocqBundleCertificate bundle
      artifact = rocqBundleCertificateArtifact bundle
  in "proof=" <> unObligationId (rocqCertificateObligation certificate)
      <> ";artifact=" <> unArtifactRef (artifactReference artifact)
      <> ";sha256=" <> unDigest (artifactDigest artifact)

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
