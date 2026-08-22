{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.SessionOfferCertification
  ( FinalResponseReceiveCertificationError (..)
  , FinalResponseReceiveCertificationBundle (..)
  , phase0FinalResponseReceiveLLVMCertification
  , verifyPhase0FinalResponseReceiveLLVMCertification
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Assurance.Types
import Phil.Assurance.Verify (ManifestError, verifyManifest)
import Phil.Core.Syntax (ObligationId (..))
import Phil.LLVM.IR
import Phil.LLVM.SessionOffer
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

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
