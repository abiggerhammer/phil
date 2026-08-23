{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.AcceptedResponseCertification
  ( AcceptedResponseCertificationError (..)
  , AcceptedResponseCertificationBundle (..)
  , phase0AcceptedResponseLLVMCertification
  , verifyPhase0AcceptedResponseLLVMCertification
  , systemsAcceptedResponseCertificationSpec
  , llvmAcceptedResponseCertificationSpec
  , AcceptedResponseProofCertificationError (..)
  , AcceptedResponseProofCertificationBundle (..)
  , phase0AcceptedResponseProofCertification
  , verifyPhase0AcceptedResponseProofCertification
  , renderAcceptedResponseProofCertification
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
import Phil.LLVM.AcceptedResponse
import Phil.LLVM.IR
import Phil.LLVM.Lower (lowerSystemsAcceptedResponse)
import Phil.LLVM.StorageProofCertification
import Phil.Systems.AcceptedResponse
import Phil.Systems.IR
import Phil.Systems.Verify (SystemsVerificationContext (..))

data AcceptedResponseCertificationError
  = AcceptedResponseCertificationSystemsError AcceptedResponseError
  | AcceptedResponseCertificationTranslationError AcceptedResponseLLVMError
  | AcceptedResponseCertificationManifestError ManifestError
  deriving (Eq, Show)

data AcceptedResponseCertificationBundle = AcceptedResponseCertificationBundle
  { acceptedResponseCertificationSystems :: AcceptedResponseBundle
  , acceptedResponseCertificationLLVM :: LLVMArtifact
  , acceptedResponseCertificationArtifact :: ArtifactIdentity
  , acceptedResponseCertificationLedger :: AssuranceLedger
  , acceptedResponseCertificationManifest :: AssuranceManifest
  , acceptedResponseCertificationContext :: VerificationContext
  }
  deriving (Eq, Show)

systemsAcceptedResponseCertificationSpec :: RocqCertificationSpec
systemsAcceptedResponseCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "systems-accepted-response"
  , rocqSpecObligation = ObligationId "PHIL-SYS-ACCEPTED-001"
  , rocqSpecClaim =
      "For the verified Phase 0 accepted-response candidate, storage success reaches the exact accepted block; select accepted consumes exactly the server transport and the exact semantic UploadId produced by storage, has no outputs or ambient state, the UploadId has exactly one semantic operation use in the current artifact, and the block terminates with the exact source success outcome; transport/UploadId/block/use/termination drift rejects."
  , rocqSpecKind = "Systems accepted-response semantic identity"
  , rocqSpecOrigin =
      "src/Phil/Systems/AcceptedResponse.hs; src/Phil/Systems/Storage.hs; proof/Phil/Systems/AcceptedResponse.v"
  , rocqSpecScope = "Phil.Systems accepted-response boundary"
  , rocqSpecRepresentation =
      "normalized storage-success / exact transport+UploadId select / success-termination model"
  , rocqSpecSubjects =
      [ "TransportHandle server.transport"
      , "RuntimeScalar UploadId server.upload_id"
      , "select accepted"
      , "storage-success predecessor"
      , "source success termination"
      ]
  , rocqSpecTheorems =
      [ "verified_systems_accepted_reuses_storage_authority"
      , "verified_systems_accepted_reaches_exact_block_from_storage_success"
      , "verified_systems_accepted_uses_exact_transport_and_storage_upload_id"
      , "verified_systems_accepted_preserves_exact_ordered_operand_pair"
      , "verified_systems_accepted_has_no_outputs_or_runtime_site"
      , "verified_systems_accepted_uses_upload_id_once_and_terminates_success"
      , "systems_accepted_transport_drift_is_rejected"
      , "systems_accepted_upload_id_drift_is_rejected"
      , "systems_accepted_block_or_predecessor_drift_is_rejected"
      , "systems_accepted_operation_or_multiplicity_drift_is_rejected"
      , "systems_accepted_operand_order_or_arity_drift_is_rejected"
      , "systems_accepted_outputs_or_runtime_site_drift_is_rejected"
      , "systems_accepted_use_count_or_termination_drift_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Systems/AcceptedResponse.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Systems/AcceptedResponse.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-SYS-ACCEPTED-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-SYS-ACCEPTED-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness plus reviewed correspondence from concrete Haskell ValueId/BlockId identities, operation-use enumeration, storage-success reachability, select-accepted identity, and source success termination to the normalized proof model remain explicit trust boundaries. Concrete wire encoding is not proved here."
  }

llvmAcceptedResponseCertificationSpec :: RocqCertificationSpec
llvmAcceptedResponseCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "llvm-accepted-response"
  , rocqSpecObligation = ObligationId "PHIL-LLVM-ACCEPTED-001"
  , rocqSpecClaim =
      "For accepted-response-v1, verified lowering preserves the exact server transport and exact storage-produced UploadId as the ordered operands to the physical phil_runtime_select_accepted(ptr,ptr) call, reaches that call only from storage success, preserves exact source success termination, keeps UploadId opaque to generated code, and rejects ambient/nullary encoding, UploadId layout access or release, unauthorized pointer strengthening, operand/edge drift, or evidence-derived runtime symbols."
  , rocqSpecKind = "LLVM accepted-response ABI v1"
  , rocqSpecOrigin =
      "docs/phase-0/accepted-response-abi-v1.md; src/Phil/LLVM/AcceptedResponse.hs; src/Phil/LLVM/Lower.hs; src/Phil/LLVM/IR.hs; src/Phil/LLVM/Verify.hs; proof/Phil/LLVM/AcceptedResponse.v"
  , rocqSpecScope = "Phil.LLVM accepted-response-v1"
  , rocqSpecRepresentation =
      "normalized storage-success / physical accepted selector / opaque UploadId model"
  , rocqSpecSubjects =
      [ "phil_runtime_select_accepted(ptr,ptr)"
      , "exact server transport operand"
      , "exact storage UploadId operand"
      , "storage-success predecessor"
      , "opaque UploadId discipline"
      ]
  , rocqSpecTheorems =
      [ "verified_llvm_accepted_reuses_systems_accepted_authority"
      , "verified_llvm_accepted_reuses_storage_authority"
      , "verified_llvm_accepted_reuses_runtime_symbol_authority"
      , "verified_llvm_accepted_preserves_exact_transport_operand"
      , "verified_llvm_accepted_preserves_exact_storage_upload_id_operand"
      , "verified_llvm_accepted_reaches_only_from_storage_success"
      , "verified_llvm_accepted_preserves_exact_ordered_pair_and_success"
      , "verified_llvm_accepted_preserves_upload_id_opacity"
      , "verified_llvm_accepted_forbids_ambient_nullary_generic_and_evidence_symbols"
      , "llvm_accepted_transport_operand_drift_is_rejected"
      , "llvm_accepted_upload_id_operand_drift_is_rejected"
      , "llvm_accepted_block_or_storage_edge_drift_is_rejected"
      , "llvm_accepted_operation_order_or_termination_drift_is_rejected"
      , "llvm_accepted_upload_id_representation_drift_is_rejected"
      , "llvm_accepted_ambient_or_symbol_drift_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/LLVM/AcceptedResponse.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/LLVM/AcceptedResponse.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-LLVM-ACCEPTED-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-LLVM-ACCEPTED-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness; reviewed Systems/LLVM-to-normalized-proof correspondence; opaque runtime UploadId representation; target calling convention; concrete 17-octet provider encoding; physical write behavior; outer framing; and native execution remain explicit trust boundaries."
  }

-- PHIL-LLVM-CERT-006
--
-- Content-bound to accepted-response-v1. The exact 17-octet encoder behavior,
-- provider conformance, LLVM 18 acceptance, linking, and native execution are
-- external gates rather than claims of this pure translation certificate.
phase0AcceptedResponseLLVMCertification
  :: Either AcceptedResponseCertificationError AcceptedResponseCertificationBundle
phase0AcceptedResponseLLVMCertification = do
  systemsBundle <- mapLeft
    AcceptedResponseCertificationSystemsError
    phase0AcceptedResponseBundle
  let systemsArtifact = acceptedResponseArtifact systemsBundle
      llvmArtifact = lowerSystemsAcceptedResponse
        phase0AcceptedResponseLLVMTarget
        systemsArtifact
  mapLeft AcceptedResponseCertificationTranslationError $
    verifyAcceptedResponseTranslation systemsBundle llvmArtifact
  let systemsManifest = systemsAssuranceManifest (acceptedResponseContext systemsBundle)
      moduleValue = llvmArtifactModule llvmArtifact
      sourceDigest = llvmContractSourceDigest (llvmArtifactContract llvmArtifact)
      targetDigest = llvmContractTargetDigest (llvmArtifactContract llvmArtifact)
      targetTextDigest = digestText (llvmArtifactText llvmArtifact)
      abiDigest = llvmRuntimeABIDigest moduleValue
      certificationTarget = "preopt-llvm:" <> llvmTargetTriple moduleValue
      sourceCompilationProfile = Text.pack (show (llvmCompilationProfile moduleValue))
      certificationProfile =
        "translation-validation/" <> sourceCompilationProfile <> "/accepted-response-v1"
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
        , ("accepted_selector", "phil_runtime_select_accepted(ptr,ptr)->void")
        , ("accepted_transport", "exact component transport handle")
        , ("accepted_upload_id", "exact opaque UploadId returned by storage")
        , ("accepted_wire", "17 octets: 0x01 || 16-octet runtime-encoded UploadId token")
        , ("upload_id_representation", "semantic handle stays opaque to generated code")
        , ("outer_framing", "not defined by accepted-response-v1")
        , ("write_failure", "residual runtime assumption; source provides no select-failure edge")
        , ("ambient_accepted_state", "forbidden")
        , ("runtime_symbol_identity", "physical primitive/signature")
        , ("external_runtime_gate", "provider signatures and exact accepted-response bytes are checked independently in CI")
        , ("external_llvm_gate", "canonical target text must be accepted by LLVM 18 in CI")
        ]
      evidenceScope = ValidityScope $
        Map.insert "target" certificationTarget $
        Map.insert "compilation_profile" certificationProfile validityContext
      revisionStatement =
        "The canonical Phase 0 accepted-response Systems -> pre-optimization LLVM pair is certified only for the exact source, target, target text, target profile, and phil-runtime/phase0/accepted-response-v1 ABI bound by this revision; independent Phil translation validation establishes exact transport and opaque UploadId operand identity at select accepted(id), while exact 17-octet runtime encoding, provider conformance, LLVM 18 acceptance, linking, and execution remain external certification gates."
      provisionalRevision = ObligationRevision
        { revisionObligationId = ObligationId "PHIL-LLVM-CERT-006"
        , revisionId = RevisionId ""
        , revisionStatement = revisionStatement
        , revisionStatementDigest = digestText revisionStatement
        , revisionKind = "LLVMAcceptedResponseTranslationCertification"
        , revisionOrigin = "accepted response ABI v1 / PHIL-LLVM-CERT-006"
        , revisionScope = "llvm.phase0.preopt.accepted-response.translation"
        , revisionRequiredAt = "certification"
        , revisionRepresentation =
            "storage-witnessed SystemsArtifact -> operand-explicit accepted-response canonical pre-optimization LLVMArtifact"
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
        [ "phil-llvm-phase0-accepted-response-translation-validation-v1"
        , "source-digest=" <> unDigest sourceDigest
        , "target-digest=" <> unDigest targetDigest
        , "target-text-digest=" <> unDigest targetTextDigest
        , "llvm-language=" <> llvmLanguageVersion moduleValue
        , "llvm-tool-profile=" <> llvmToolVersion moduleValue
        , "target-triple=" <> llvmTargetTriple moduleValue
        , "data-layout=" <> llvmDataLayout moduleValue
        , "runtime-abi-digest=" <> unDigest abiDigest
        , "runtime-abi-profile=" <> llvmRuntimeABIProfile moduleValue
        , "translation-validator=Phil.LLVM.AcceptedResponse.verifyAcceptedResponseTranslation"
        , "assurance-checker=Phil.Assurance.Verify.verifyManifest"
        ]
      translationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef
            "artifact:phil:llvm:phase0:accepted-response:translation-validation:v1"
        , artifactDigest = digestText translationArtifactRecord
        }
      evidenceId = EvidenceEntryId
        "evidence.llvm.phase0.accepted-response.translation.validated"
      provisionalEvidence = EvidenceEntry
        { evidenceEntryId = evidenceId
        , evidenceEntryDigest = Digest ""
        , evidenceObligationRevision = certificationRevisionId
        , evidenceAssuranceKind = TranslationValidated
        , evidenceRole = EvidenceRole "translation_validated"
        , evidenceProducer = "Phil.LLVM.AcceptedResponse.verifyAcceptedResponseTranslation"
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
            [ "exact accepted-response transport SSA identity"
            , "exact storage-produced UploadId SSA identity"
            , "accepted response is reached only from storage success"
            , "generic nullary select accepted call is eliminated"
            , "opaque UploadId has no generated layout access, release, or ambient recovery"
            , "accepted block terminates with exact source success outcome"
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
        [ "phil-llvm-phase0-accepted-response-certification-root-v1"
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
  pure AcceptedResponseCertificationBundle
    { acceptedResponseCertificationSystems = systemsBundle
    , acceptedResponseCertificationLLVM = llvmArtifact
    , acceptedResponseCertificationArtifact = translationArtifact
    , acceptedResponseCertificationLedger = ledger
    , acceptedResponseCertificationManifest = manifest
    , acceptedResponseCertificationContext = verificationContext
    }

verifyPhase0AcceptedResponseLLVMCertification
  :: Either AcceptedResponseCertificationError ()
verifyPhase0AcceptedResponseLLVMCertification = do
  bundle <- phase0AcceptedResponseLLVMCertification
  mapLeft AcceptedResponseCertificationManifestError $
    verifyManifest
      (acceptedResponseCertificationContext bundle)
      (acceptedResponseCertificationLedger bundle)
      (acceptedResponseCertificationManifest bundle)

data AcceptedResponseProofCertificationError
  = AcceptedResponseProofCertificationBaseError AcceptedResponseCertificationError
  | AcceptedResponseProofCertificationPredecessorError StorageProofCertificationError
  | AcceptedResponseProofCertificationWrongProof Text ObligationId ObligationId
  | AcceptedResponseProofCertificationProofManifestError Text ManifestError
  | AcceptedResponseProofCertificationManifestError ManifestError
  deriving (Eq, Show)

data AcceptedResponseProofCertificationBundle = AcceptedResponseProofCertificationBundle
  { acceptedResponseProofCertificationBase :: AcceptedResponseCertificationBundle
  , acceptedResponseProofCertificationPredecessor :: StorageProofCertificationBundle
  , acceptedResponseProofCertificationArtifact :: ArtifactIdentity
  , acceptedResponseProofCertificationRecord :: Text
  , acceptedResponseProofCertificationLedger :: AssuranceLedger
  , acceptedResponseProofCertificationManifest :: AssuranceManifest
  , acceptedResponseProofCertificationContext :: VerificationContext
  }
  deriving (Eq, Show)

phase0AcceptedResponseProofCertification
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
  -> Either AcceptedResponseProofCertificationError AcceptedResponseProofCertificationBundle
phase0AcceptedResponseProofCertification
    systemsAcceptedProof llvmAcceptedProof
    systemsStorageProof llvmStorageProof
    systemsDigestProof llvmDigestProof systemsRecordProof exactProof abiProof symbolProof = do
  verifyAcceptedProof "systems-accepted-response" systemsAcceptedResponseCertificationSpec systemsAcceptedProof
  verifyAcceptedProof "llvm-accepted-response" llvmAcceptedResponseCertificationSpec llvmAcceptedProof
  verifyAcceptedProof "systems-storage" systemsStorageCertificationSpec systemsStorageProof
  verifyAcceptedProof "llvm-storage" llvmStorageCertificationSpec llvmStorageProof
  verifyAcceptedProof "systems-digest-validation" systemsDigestValidationCertificationSpec systemsDigestProof
  verifyAcceptedProof "llvm-digest-validation" llvmDigestValidationCertificationSpec llvmDigestProof
  verifyAcceptedProof "systems-recognized-record" systemsRecognizedRecordCertificationSpec systemsRecordProof
  verifyAcceptedProof "llvm-exact-receive" llvmExactReceiveCertificationSpec exactProof
  verifyAcceptedProof "llvm-recognized-record-abi" llvmRecognizedRecordABICertificationSpec abiProof
  verifyAcceptedProof "llvm-runtime-symbol-identity" llvmRuntimeSymbolCertificationSpec symbolProof

  predecessor <- mapLeft AcceptedResponseProofCertificationPredecessorError $
    phase0StorageProofCertification
      systemsStorageProof llvmStorageProof
      systemsDigestProof llvmDigestProof systemsRecordProof exactProof abiProof symbolProof
  base <- mapLeft AcceptedResponseProofCertificationBaseError $
    phase0AcceptedResponseLLVMCertification

  let explicitProofBundles =
        [ systemsAcceptedProof
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
      predecessorArtifact = storageProofCertificationArtifact predecessor

      systemsBundle = acceptedResponseCertificationSystems base
      systemsArtifact = acceptedResponseArtifact systemsBundle
      systemsManifest = systemsAssuranceManifest (acceptedResponseContext systemsBundle)
      llvmArtifact = acceptedResponseCertificationLLVM base
      moduleValue = llvmArtifactModule llvmArtifact
      translationArtifact = acceptedResponseCertificationArtifact base
      sourceDigest = llvmContractSourceDigest (llvmArtifactContract llvmArtifact)
      targetDigest = llvmContractTargetDigest (llvmArtifactContract llvmArtifact)
      targetTextDigest = digestText (llvmArtifactText llvmArtifact)
      abiDigest = llvmRuntimeABIDigest moduleValue
      systemsLoweringRoot = loweringLedgerRoot (systemsArtifactLoweringLedger systemsArtifact)
      certificationTarget = "preopt-llvm:" <> llvmTargetTriple moduleValue
      sourceCompilationProfile = Text.pack (show (llvmCompilationProfile moduleValue))
      certificationProfile =
        "translation-validation/" <> sourceCompilationProfile <> "/accepted-response-v1/proof-bound"
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
        , ("accepted_selector", "phil_runtime_select_accepted(ptr,ptr)->void")
        , ("accepted_transport", "exact server transport handle")
        , ("accepted_upload_id", "exact storage-produced opaque UploadId")
        , ("accepted_predecessor", "accepted selector is reachable only from exact storage success")
        , ("accepted_termination", "exact source success termination")
        , ("upload_id_representation", "opaque to generated code; no layout access, release, ambient recovery, or unauthorized strengthening")
        , ("accepted_wire", "17 octets: 0x01 || UploadIdToken[16]; runtime evidence only")
        , ("predecessor_certification", unDigest (artifactDigest predecessorArtifact))
        , ("proof_assistant", "Rocq")
        , ("rocq_version", "9.2.0")
        , ("certificate_profile", "proof-assistant-theorem/v1")
        , ("external_llvm_gate", "canonical target text must be accepted by LLVM 18 in CI")
        , ("external_runtime_abi_gate", "provider signature conformance must pass independently in CI")
        , ("external_wire_gate", "exact 17-octet accepted bytes and fail-closed no-emission paths must execute independently in CI")
        , ("outer_framing", "not defined by accepted-response-v1")
        , ("write_failure", "residual runtime assumption; source has no accepted-select failure edge")
        , ("upload_id_freshness_or_uniqueness", "not certified by accepted-response-v1")
        ]
      evidenceScope = ValidityScope $
        Map.insert "target" certificationTarget $
        Map.insert "compilation_profile" certificationProfile validityContext
      revisionStatement =
        "The accepted-response-v1 Systems -> canonical pre-optimization LLVM pair may be labeled Certified only when exact source/target/text digests, lowering root, target/runtime-ABI/tool identities, Systems accepted-response proof, LLVM accepted-response/opaque-UploadId proof, compatible predecessor storage/digest/exact-receive/recognized-record/runtime-symbol proof authority, and translation-validation result are content-bound; proof-bound CERT-005 is reproducible and digest-bound without importing evidence outside its storage validity scope; LLVM 18, exact 17-octet provider encoding, physical write behavior, and runtime ABI conformance remain explicit external gates; and the assurance manifest closes over all selected evidence."
      provisionalRevision = ObligationRevision
        { revisionObligationId = ObligationId "PHIL-LLVM-CERT-006"
        , revisionId = RevisionId ""
        , revisionStatement = revisionStatement
        , revisionStatementDigest = digestText revisionStatement
        , revisionKind = "LLVMAcceptedResponseProofBoundCertification"
        , revisionOrigin = "accepted response ABI v1 / proof-bound PHIL-LLVM-CERT-006"
        , revisionScope = "llvm.phase0.preopt.accepted-response.proof-bound"
        , revisionRequiredAt = "certification"
        , revisionRepresentation =
            "storage-witnessed SystemsArtifact -> accepted-response-v1 canonical pre-optimization LLVMArtifact + proof authority"
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
        "evidence.llvm.phase0.accepted-response.proof-bound.translation.validated"
      provisionalTranslationEvidence = EvidenceEntry
        { evidenceEntryId = translationEvidenceId
        , evidenceEntryDigest = Digest ""
        , evidenceObligationRevision = certificationRevisionId
        , evidenceAssuranceKind = TranslationValidated
        , evidenceRole = EvidenceRole "translation_validated"
        , evidenceProducer = "Phil.LLVM.AcceptedResponse.verifyAcceptedResponseTranslation"
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
            [ "exact storage-success -> accepted-response boundary"
            , "exact server transport operand identity"
            , "exact storage-produced UploadId operand identity"
            , "exact ordered accepted selector operand pair"
            , "physical accepted-selector symbol identity"
            , "exact source success termination"
            , "opaque UploadId with no generated layout access, release, ambient recovery, or unauthorized strengthening"
            , "absence of nullary/generic accepted selector and evidence-derived runtime symbols"
            , "content-bound reproduction of proof-bound storage predecessor authority"
            ]
        , evidenceRuntimeMechanism = Nothing
        , evidenceRuntimeResidue = []
        , evidenceCostRefs = []
        }
      translationEvidence = provisionalTranslationEvidence
        { evidenceEntryDigest = deriveEvidenceEntryDigest provisionalTranslationEvidence }
      certificationRecord = Text.unlines $
        [ "phil-llvm-phase0-accepted-response-certification/v1"
        , "obligation=PHIL-LLVM-CERT-006"
        , "revision=" <> unRevisionId certificationRevisionId
        , "source-digest=" <> unDigest sourceDigest
        , "systems-lowering-root=" <> unDigest systemsLoweringRoot
        , "target-digest=" <> unDigest targetDigest
        , "target-text-digest=" <> unDigest targetTextDigest
        , "runtime-abi-profile=" <> llvmRuntimeABIProfile moduleValue
        , "runtime-abi-digest=" <> unDigest abiDigest
        , "translation-artifact=" <> renderAcceptedArtifact translationArtifact
        , "predecessor-certification=" <> renderAcceptedArtifact predecessorArtifact
        ] <> map renderAcceptedProofArtifact explicitProofBundles <>
        [ "external-llvm-gate=LLVM 18 assembler acceptance required"
        , "external-runtime-abi-gate=provider signature conformance required"
        , "external-wire-gate=exact 17-octet accepted encoding and fail-closed no-emission execution required"
        , "residual-write-failure=source has no accepted-select failure edge"
        , "residual-outer-framing=not defined by accepted-response-v1"
        , "residual-upload-id-freshness=not certified"
        ]
      certificationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef "certificate:phil:llvm:PHIL-LLVM-CERT-006:v1"
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
        [ "phil-llvm-phase0-accepted-response-proof-bound-certification-root-v1"
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
      bundle = AcceptedResponseProofCertificationBundle
        { acceptedResponseProofCertificationBase = base
        , acceptedResponseProofCertificationPredecessor = predecessor
        , acceptedResponseProofCertificationArtifact = certificationArtifact
        , acceptedResponseProofCertificationRecord = certificationRecord
        , acceptedResponseProofCertificationLedger = ledger
        , acceptedResponseProofCertificationManifest = manifest
        , acceptedResponseProofCertificationContext = verificationContext
        }

  mapLeft AcceptedResponseProofCertificationManifestError $
    verifyManifest verificationContext ledger manifest
  pure bundle

verifyPhase0AcceptedResponseProofCertification
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
  -> Either AcceptedResponseProofCertificationError ()
verifyPhase0AcceptedResponseProofCertification
    systemsAcceptedProof llvmAcceptedProof
    systemsStorageProof llvmStorageProof
    systemsDigestProof llvmDigestProof systemsRecordProof exactProof abiProof symbolProof = do
  bundle <- phase0AcceptedResponseProofCertification
    systemsAcceptedProof llvmAcceptedProof
    systemsStorageProof llvmStorageProof
    systemsDigestProof llvmDigestProof systemsRecordProof exactProof abiProof symbolProof
  mapLeft AcceptedResponseProofCertificationManifestError $
    verifyManifest
      (acceptedResponseProofCertificationContext bundle)
      (acceptedResponseProofCertificationLedger bundle)
      (acceptedResponseProofCertificationManifest bundle)

renderAcceptedResponseProofCertification :: AcceptedResponseProofCertificationBundle -> Text
renderAcceptedResponseProofCertification = acceptedResponseProofCertificationRecord

verifyAcceptedProof
  :: Text
  -> RocqCertificationSpec
  -> RocqCertificationBundle
  -> Either AcceptedResponseProofCertificationError ()
verifyAcceptedProof label spec bundle = do
  let expected = rocqSpecObligation spec
      actual = rocqCertificateObligation (rocqBundleCertificate bundle)
  unless (actual == expected) $
    Left (AcceptedResponseProofCertificationWrongProof label expected actual)
  mapLeft (AcceptedResponseProofCertificationProofManifestError label) $
    verifyManifest
      (rocqBundleVerificationContext bundle)
      (rocqBundleLedger bundle)
      (rocqBundleManifest bundle)

renderAcceptedArtifact :: ArtifactIdentity -> Text
renderAcceptedArtifact artifact =
  unArtifactRef (artifactReference artifact) <> ";sha256=" <> unDigest (artifactDigest artifact)

renderAcceptedProofArtifact :: RocqCertificationBundle -> Text
renderAcceptedProofArtifact bundle =
  let certificate = rocqBundleCertificate bundle
      artifact = rocqBundleCertificateArtifact bundle
  in "proof=" <> unObligationId (rocqCertificateObligation certificate)
      <> ";artifact=" <> unArtifactRef (artifactReference artifact)
      <> ";sha256=" <> unDigest (artifactDigest artifact)

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
