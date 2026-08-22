{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.PayloadCancelChoiceProofCertification
  ( systemsPayloadCancelChoiceCertificationSpec
  , llvmPayloadCancelChoiceCertificationSpec
  , PayloadCancelChoiceProofCertificationError (..)
  , PayloadCancelChoiceProofCertificationBundle (..)
  , phase0PayloadCancelChoiceProofCertification
  , verifyPhase0PayloadCancelChoiceProofCertification
  , renderPayloadCancelChoiceProofCertification
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
import Phil.LLVM.PayloadCancelChoiceCertification
import Phil.LLVM.SessionOfferCertification
import Phil.Systems.IR
import Phil.Systems.PayloadCancelChoice
import Phil.Systems.Verify (SystemsVerificationContext (..))

systemsPayloadCancelChoiceCertificationSpec :: RocqCertificationSpec
systemsPayloadCancelChoiceCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "systems-payload-cancel-choice"
  , rocqSpecObligation = ObligationId "PHIL-SYS-PAYLOAD-CANCEL-001"
  , rocqSpecClaim =
      "For the verified Phase 0 payload/cancel semantic-choice candidate, exact client and server transport identities, exact payload/cancel labels and continuations, zero branch payloads, exact selector/offer multiplicity, and the local should_cancel Bool branch are preserved; local computation is not reclassified as session state; historical server Bool/generic receive and client generic select representations are absent; and proof-bound final-response authority is reused."
  , rocqSpecKind = "Systems payload/cancel semantic session choice"
  , rocqSpecOrigin =
      "src/Phil/Systems/PayloadCancelChoice.hs; proof/Phil/Systems/PayloadCancelChoice.v"
  , rocqSpecScope = "Phil.Systems payload/cancel session choice"
  , rocqSpecRepresentation =
      "normalized exact dual labels / transports / continuations / local-decision separation model"
  , rocqSpecSubjects =
      [ "TransportHandle client.transport"
      , "TransportHandle server.transport"
      , "client select payload"
      , "client select cancel"
      , "server offer payload/cancel"
      , "client.should_cancel : Bool"
      ]
  , rocqSpecTheorems =
      [ "verified_systems_payload_cancel_reuses_final_response_authority"
      , "verified_systems_payload_cancel_preserves_exact_transports"
      , "verified_systems_payload_cancel_preserves_dual_labels_targets_and_no_payloads"
      , "verified_systems_payload_cancel_has_exact_choice_multiplicity"
      , "verified_systems_payload_cancel_keeps_should_cancel_local"
      , "verified_systems_payload_cancel_eliminates_legacy_protocol_state"
      , "systems_payload_cancel_transport_or_label_drift_is_rejected"
      , "systems_payload_cancel_target_payload_or_multiplicity_drift_is_rejected"
      , "systems_payload_cancel_local_or_legacy_conflation_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Systems/PayloadCancelChoice.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Systems/PayloadCancelChoice.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-SYS-PAYLOAD-CANCEL-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-SYS-PAYLOAD-CANCEL-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness plus reviewed correspondence from concrete Haskell transport/label/block identities, semantic select/offer multiplicity, local should_cancel control, and predecessor relation to the normalized proof model remain explicit trust boundaries. No physical one-octet encoding is proved at Systems level."
  }

llvmPayloadCancelChoiceCertificationSpec :: RocqCertificationSpec
llvmPayloadCancelChoiceCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "llvm-payload-cancel-choice"
  , rocqSpecObligation = ObligationId "PHIL-LLVM-PAYLOAD-CANCEL-001"
  , rocqSpecClaim =
      "For payload-cancel-choice-v1, verified lowering passes exact client/server transport operands, emits canonical payload=0x01 and cancel=0x00 selector constants exactly once, uses one physical receiver with true->payload and false->cancel exact continuations, carries no choice payload representation, eliminates generic and ambient choice/transport state, performs no unauthorized pointer strengthening, reuses final-response and runtime-symbol proof authority, and invents no malformed/EOF Phil CFG branch. Concrete I/O and malformed-input non-return remain external runtime gates."
  , rocqSpecKind = "LLVM payload/cancel choice ABI v1"
  , rocqSpecOrigin =
      "docs/phase-0/payload-cancel-choice-abi-v1.md; src/Phil/LLVM/PayloadCancelChoice.hs; proof/Phil/LLVM/PayloadCancelChoice.v"
  , rocqSpecScope = "Phil.LLVM payload-cancel-choice-v1"
  , rocqSpecRepresentation =
      "normalized exact transport operands / canonical selector codes / receiver continuation mapping model"
  , rocqSpecSubjects =
      [ "phil_runtime_select_payload_cancel(ptr,i8)->void"
      , "phil_runtime_receive_payload_cancel(ptr)->i1"
      , "payload code 0x01"
      , "cancel code 0x00"
      , "exact client/server transport operands"
      , "true->payload / false->cancel targets"
      ]
  , rocqSpecTheorems =
      [ "verified_llvm_payload_cancel_reuses_semantic_final_and_symbol_authority"
      , "verified_llvm_payload_cancel_preserves_exact_transport_operands"
      , "verified_llvm_payload_cancel_uses_canonical_selectors"
      , "verified_llvm_payload_cancel_preserves_receiver_and_continuations"
      , "verified_llvm_payload_cancel_forbids_payload_ambient_generic_and_malformed_edges"
      , "llvm_payload_cancel_transport_or_selector_drift_is_rejected"
      , "llvm_payload_cancel_receiver_or_target_drift_is_rejected"
      , "llvm_payload_cancel_ambient_generic_payload_or_malformed_drift_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/LLVM/PayloadCancelChoice.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/LLVM/PayloadCancelChoice.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-LLVM-PAYLOAD-CANCEL-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-LLVM-PAYLOAD-CANCEL-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness; reviewed Systems/LLVM-to-normalized-proof correspondence; concrete one-octet selector write and receiver read behavior; reserved/EOF non-return; provider ABI conformance; physical write success; target calling convention; LLVM 18; linking; and native execution remain explicit trust boundaries."
  }

data PayloadCancelChoiceProofCertificationError
  = PayloadCancelChoiceProofCertificationBaseError PayloadCancelChoiceCertificationError
  | PayloadCancelChoiceProofCertificationPredecessorError FinalResponseReceiveProofCertificationError
  | PayloadCancelChoiceProofCertificationWrongProof Text ObligationId ObligationId
  | PayloadCancelChoiceProofCertificationProofManifestError Text ManifestError
  | PayloadCancelChoiceProofCertificationManifestError ManifestError
  deriving (Eq, Show)

data PayloadCancelChoiceProofCertificationBundle = PayloadCancelChoiceProofCertificationBundle
  { payloadCancelChoiceProofCertificationBase :: PayloadCancelChoiceCertificationBundle
  , payloadCancelChoiceProofCertificationPredecessor :: FinalResponseReceiveProofCertificationBundle
  , payloadCancelChoiceProofCertificationArtifact :: ArtifactIdentity
  , payloadCancelChoiceProofCertificationRecord :: Text
  , payloadCancelChoiceProofCertificationLedger :: AssuranceLedger
  , payloadCancelChoiceProofCertificationManifest :: AssuranceManifest
  , payloadCancelChoiceProofCertificationContext :: VerificationContext
  }
  deriving (Eq, Show)

phase0PayloadCancelChoiceProofCertification
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
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> Either PayloadCancelChoiceProofCertificationError PayloadCancelChoiceProofCertificationBundle
phase0PayloadCancelChoiceProofCertification
    systemsPayloadCancelProof llvmPayloadCancelProof
    systemsFinalProof llvmFinalProof
    systemsRejectedProof llvmRejectedProof
    systemsAcceptedProof llvmAcceptedProof
    systemsStorageProof llvmStorageProof
    systemsDigestProof llvmDigestProof systemsRecordProof exactProof abiProof symbolProof = do
  verifyPayloadCancelProof
    "systems-payload-cancel"
    systemsPayloadCancelChoiceCertificationSpec
    systemsPayloadCancelProof
  verifyPayloadCancelProof
    "llvm-payload-cancel"
    llvmPayloadCancelChoiceCertificationSpec
    llvmPayloadCancelProof

  predecessor <- mapLeft PayloadCancelChoiceProofCertificationPredecessorError $
    phase0FinalResponseReceiveProofCertification
      systemsFinalProof llvmFinalProof
      systemsRejectedProof llvmRejectedProof
      systemsAcceptedProof llvmAcceptedProof
      systemsStorageProof llvmStorageProof
      systemsDigestProof llvmDigestProof systemsRecordProof exactProof abiProof symbolProof
  base <- mapLeft PayloadCancelChoiceProofCertificationBaseError $
    phase0PayloadCancelChoiceLLVMCertification

  let explicitProofBundles =
        [ systemsPayloadCancelProof
        , llvmPayloadCancelProof
        , systemsFinalProof
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
      predecessorArtifact = finalResponseReceiveProofCertificationArtifact predecessor

      systemsBundle = payloadCancelChoiceCertificationSystems base
      systemsArtifact = payloadCancelChoiceArtifact systemsBundle
      systemsManifest = systemsAssuranceManifest (payloadCancelChoiceContext systemsBundle)
      llvmArtifact = payloadCancelChoiceCertificationLLVM base
      moduleValue = llvmArtifactModule llvmArtifact
      translationArtifact = payloadCancelChoiceCertificationArtifact base
      sourceDigest = llvmContractSourceDigest (llvmArtifactContract llvmArtifact)
      targetDigest = llvmContractTargetDigest (llvmArtifactContract llvmArtifact)
      targetTextDigest = digestText (llvmArtifactText llvmArtifact)
      abiDigest = llvmRuntimeABIDigest moduleValue
      systemsLoweringRoot = loweringLedgerRoot (systemsArtifactLoweringLedger systemsArtifact)
      certificationTarget = "preopt-llvm:" <> llvmTargetTriple moduleValue
      sourceCompilationProfile = Text.pack (show (llvmCompilationProfile moduleValue))
      certificationProfile =
        "translation-validation/" <> sourceCompilationProfile <> "/payload-cancel-choice-v1/proof-bound"
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
        , ("selector", "phil_runtime_select_payload_cancel(ptr,i8)->void")
        , ("receiver", "phil_runtime_receive_payload_cancel(ptr)->i1")
        , ("payload_code", "0x01")
        , ("cancel_code", "0x00")
        , ("selector_transport", "exact client transport handle")
        , ("receiver_transport", "exact server transport handle")
        , ("receiver_mapping", "true->payload;false->cancel")
        , ("choice_payload", "none")
        , ("local_should_cancel", "local Bool branch; not session state")
        , ("predecessor_certification", unDigest (artifactDigest predecessorArtifact))
        , ("proof_assistant", "Rocq")
        , ("rocq_version", "9.2.0")
        , ("certificate_profile", "proof-assistant-theorem/v1")
        , ("external_llvm_gate", "canonical target text must be accepted by LLVM 18 in CI")
        , ("external_runtime_abi_gate", "provider signature conformance must pass independently in CI")
        , ("external_selector_execution_gate", "exact payload/cancel selector execution must pass independently in CI")
        , ("external_receiver_execution_gate", "exact payload/cancel receiver execution must pass independently in CI")
        , ("external_malformed_gate", "reserved octets and early EOF must not return normally")
        , ("residual_write_failure", "source select has no physical write-failure continuation")
        , ("outer_framing", "not defined by payload-cancel-choice-v1")
        ]
      evidenceScope = ValidityScope $
        Map.insert "target" certificationTarget $
        Map.insert "compilation_profile" certificationProfile validityContext
      revisionStatement =
        "The payload-cancel-choice-v1 Systems -> canonical pre-optimization LLVM pair may be labeled Certified only when exact source/target/text digests, lowering root, target/runtime-ABI/tool identities, Systems payload/cancel semantic-choice proof, LLVM canonical-selector/receiver proof, compatible final-response and predecessor proof authority, and translation-validation result are content-bound; proof-bound CERT-008 is reproducible and digest-bound without importing translation evidence outside its final-response validity scope; payload/cancel remain payload-free protocol labels while should_cancel remains local computation; LLVM 18, provider ABI conformance, concrete one-octet selector/receiver execution, malformed-input non-return, physical write success, and outer framing remain explicit external gates; and the assurance manifest closes over all selected evidence."
      provisionalRevision = ObligationRevision
        { revisionObligationId = ObligationId "PHIL-LLVM-CERT-009"
        , revisionId = RevisionId ""
        , revisionStatement = revisionStatement
        , revisionStatementDigest = digestText revisionStatement
        , revisionKind = "LLVMPayloadCancelChoiceProofBoundCertification"
        , revisionOrigin = "payload/cancel choice ABI v1 / proof-bound PHIL-LLVM-CERT-009"
        , revisionScope = "llvm.phase0.preopt.payload-cancel-choice.proof-bound"
        , revisionRequiredAt = "certification"
        , revisionRepresentation =
            "payload/cancel semantic SystemsArtifact -> payload-cancel-choice-v1 canonical pre-optimization LLVMArtifact + proof authority"
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
        "evidence.llvm.phase0.payload-cancel-choice.proof-bound.translation.validated"
      provisionalTranslationEvidence = EvidenceEntry
        { evidenceEntryId = translationEvidenceId
        , evidenceEntryDigest = Digest ""
        , evidenceObligationRevision = certificationRevisionId
        , evidenceAssuranceKind = TranslationValidated
        , evidenceRole = EvidenceRole "translation_validated"
        , evidenceProducer = "Phil.LLVM.PayloadCancelChoice.verifyPayloadCancelChoiceTranslation"
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
            [ "exact client/server transport identity across semantic choice and physical calls"
            , "canonical payload=0x01 and cancel=0x00 generated selector constants"
            , "one physical receiver maps true to payload and false to cancel continuations"
            , "payload/cancel carry no branch payload representation"
            , "local should_cancel computation remains separate from peer-visible protocol state"
            , "generic select/receive and ambient choice/transport state are absent"
            , "no malformed/EOF Phil CFG branch is invented"
            , "content-bound reproduction of proof-bound final-response CERT-008 predecessor authority"
            ]
        , evidenceRuntimeMechanism = Nothing
        , evidenceRuntimeResidue = []
        , evidenceCostRefs = []
        }
      translationEvidence = provisionalTranslationEvidence
        { evidenceEntryDigest = deriveEvidenceEntryDigest provisionalTranslationEvidence }
      certificationRecord = Text.unlines $
        [ "phil-llvm-phase0-payload-cancel-choice-certification/v1"
        , "obligation=PHIL-LLVM-CERT-009"
        , "revision=" <> unRevisionId certificationRevisionId
        , "source-digest=" <> unDigest sourceDigest
        , "systems-lowering-root=" <> unDigest systemsLoweringRoot
        , "target-digest=" <> unDigest targetDigest
        , "target-text-digest=" <> unDigest targetTextDigest
        , "runtime-abi-profile=" <> llvmRuntimeABIProfile moduleValue
        , "runtime-abi-digest=" <> unDigest abiDigest
        , "translation-artifact=" <> renderPayloadCancelArtifact translationArtifact
        , "predecessor-certification=" <> renderPayloadCancelArtifact predecessorArtifact
        ] <> map renderPayloadCancelProofArtifact explicitProofBundles <>
        [ "external-llvm-gate=LLVM 18 assembler acceptance required"
        , "external-runtime-abi-gate=provider signature conformance required"
        , "external-selector-execution-gate=exact payload/cancel selector execution required"
        , "external-receiver-execution-gate=exact payload/cancel receiver execution required"
        , "external-malformed-gate=reserved octets and early EOF must not return normally"
        , "residual-write-failure=source select has no physical write-failure continuation"
        , "residual-outer-framing=not defined by payload-cancel-choice-v1"
        , "semantic-note=should_cancel remains local computation; payload/cancel remain peer-visible protocol labels"
        ]
      certificationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef "certificate:phil:llvm:PHIL-LLVM-CERT-009:v1"
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
        [ "phil-llvm-phase0-payload-cancel-choice-proof-bound-certification-root-v1"
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
      bundle = PayloadCancelChoiceProofCertificationBundle
        { payloadCancelChoiceProofCertificationBase = base
        , payloadCancelChoiceProofCertificationPredecessor = predecessor
        , payloadCancelChoiceProofCertificationArtifact = certificationArtifact
        , payloadCancelChoiceProofCertificationRecord = certificationRecord
        , payloadCancelChoiceProofCertificationLedger = ledger
        , payloadCancelChoiceProofCertificationManifest = manifest
        , payloadCancelChoiceProofCertificationContext = verificationContext
        }

  mapLeft PayloadCancelChoiceProofCertificationManifestError $
    verifyManifest verificationContext ledger manifest
  pure bundle

verifyPhase0PayloadCancelChoiceProofCertification
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
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> Either PayloadCancelChoiceProofCertificationError ()
verifyPhase0PayloadCancelChoiceProofCertification
    systemsPayloadCancelProof llvmPayloadCancelProof
    systemsFinalProof llvmFinalProof
    systemsRejectedProof llvmRejectedProof
    systemsAcceptedProof llvmAcceptedProof
    systemsStorageProof llvmStorageProof
    systemsDigestProof llvmDigestProof systemsRecordProof exactProof abiProof symbolProof = do
  bundle <- phase0PayloadCancelChoiceProofCertification
    systemsPayloadCancelProof llvmPayloadCancelProof
    systemsFinalProof llvmFinalProof
    systemsRejectedProof llvmRejectedProof
    systemsAcceptedProof llvmAcceptedProof
    systemsStorageProof llvmStorageProof
    systemsDigestProof llvmDigestProof systemsRecordProof exactProof abiProof symbolProof
  mapLeft PayloadCancelChoiceProofCertificationManifestError $
    verifyManifest
      (payloadCancelChoiceProofCertificationContext bundle)
      (payloadCancelChoiceProofCertificationLedger bundle)
      (payloadCancelChoiceProofCertificationManifest bundle)

renderPayloadCancelChoiceProofCertification :: PayloadCancelChoiceProofCertificationBundle -> Text
renderPayloadCancelChoiceProofCertification = payloadCancelChoiceProofCertificationRecord

verifyPayloadCancelProof
  :: Text
  -> RocqCertificationSpec
  -> RocqCertificationBundle
  -> Either PayloadCancelChoiceProofCertificationError ()
verifyPayloadCancelProof label spec bundle = do
  let expected = rocqSpecObligation spec
      actual = rocqCertificateObligation (rocqBundleCertificate bundle)
  unless (actual == expected) $
    Left (PayloadCancelChoiceProofCertificationWrongProof label expected actual)
  mapLeft (PayloadCancelChoiceProofCertificationProofManifestError label) $
    verifyManifest
      (rocqBundleVerificationContext bundle)
      (rocqBundleLedger bundle)
      (rocqBundleManifest bundle)

renderPayloadCancelArtifact :: ArtifactIdentity -> Text
renderPayloadCancelArtifact artifact =
  unArtifactRef (artifactReference artifact) <> ";sha256=" <> unDigest (artifactDigest artifact)

renderPayloadCancelProofArtifact :: RocqCertificationBundle -> Text
renderPayloadCancelProofArtifact bundle =
  let certificate = rocqBundleCertificate bundle
      artifact = rocqBundleCertificateArtifact bundle
  in "proof=" <> unObligationId (rocqCertificateObligation certificate)
      <> ";artifact=" <> unArtifactRef (artifactReference artifact)
      <> ";sha256=" <> unDigest (artifactDigest artifact)

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
