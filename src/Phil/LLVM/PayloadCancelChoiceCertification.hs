{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.PayloadCancelChoiceCertification
  ( PayloadCancelChoiceCertificationError (..)
  , PayloadCancelChoiceCertificationBundle (..)
  , phase0PayloadCancelChoiceLLVMCertification
  , verifyPhase0PayloadCancelChoiceLLVMCertification
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Assurance.Types
import Phil.Assurance.Verify (ManifestError, verifyManifest)
import Phil.Core.Syntax (ObligationId (..))
import Phil.LLVM.IR
import Phil.LLVM.PayloadCancelChoice
import Phil.Systems.PayloadCancelChoice
import Phil.Systems.Verify (SystemsVerificationContext (..))

data PayloadCancelChoiceCertificationError
  = PayloadCancelChoiceCertificationSystemsError PayloadCancelChoiceError
  | PayloadCancelChoiceCertificationTranslationError PayloadCancelChoiceLLVMError
  | PayloadCancelChoiceCertificationManifestError ManifestError
  deriving (Eq, Show)

data PayloadCancelChoiceCertificationBundle = PayloadCancelChoiceCertificationBundle
  { payloadCancelChoiceCertificationSystems :: PayloadCancelChoiceBundle
  , payloadCancelChoiceCertificationLLVM :: LLVMArtifact
  , payloadCancelChoiceCertificationArtifact :: ArtifactIdentity
  , payloadCancelChoiceCertificationLedger :: AssuranceLedger
  , payloadCancelChoiceCertificationManifest :: AssuranceManifest
  , payloadCancelChoiceCertificationContext :: VerificationContext
  }
  deriving (Eq, Show)

-- PHIL-LLVM-CERT-009
--
-- Translation-only authority for payload-cancel-choice-v1. Runtime one-octet
-- reads/writes, malformed-input non-return, physical write success, LLVM 18,
-- linking, and native execution remain external gates.
phase0PayloadCancelChoiceLLVMCertification
  :: Either PayloadCancelChoiceCertificationError PayloadCancelChoiceCertificationBundle
phase0PayloadCancelChoiceLLVMCertification = do
  systemsBundle <- mapLeft
    PayloadCancelChoiceCertificationSystemsError
    phase0PayloadCancelChoiceBundle
  let systemsArtifact = payloadCancelChoiceArtifact systemsBundle
      llvmArtifact = lowerSystemsPayloadCancelChoice
        phase0PayloadCancelChoiceLLVMTarget
        systemsArtifact
  mapLeft PayloadCancelChoiceCertificationTranslationError $
    verifyPayloadCancelChoiceTranslation systemsBundle llvmArtifact
  let systemsManifest = systemsAssuranceManifest (payloadCancelChoiceContext systemsBundle)
      moduleValue = llvmArtifactModule llvmArtifact
      sourceDigest = llvmContractSourceDigest (llvmArtifactContract llvmArtifact)
      targetDigest = llvmContractTargetDigest (llvmArtifactContract llvmArtifact)
      targetTextDigest = digestText (llvmArtifactText llvmArtifact)
      abiDigest = llvmRuntimeABIDigest moduleValue
      certificationTarget = "preopt-llvm:" <> llvmTargetTriple moduleValue
      sourceCompilationProfile = Text.pack (show (llvmCompilationProfile moduleValue))
      certificationProfile =
        "translation-validation/" <> sourceCompilationProfile <> "/payload-cancel-choice-v1"
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
        , ("selector", "phil_runtime_select_payload_cancel(ptr,i8)->void")
        , ("receiver", "phil_runtime_receive_payload_cancel(ptr)->i1")
        , ("payload_code", "0x01")
        , ("cancel_code", "0x00")
        , ("reserved_input", "runtime must not return normally")
        , ("early_eof", "runtime must not return normally")
        , ("write_failure", "residual runtime assumption")
        , ("outer_framing", "not defined by payload-cancel-choice-v1")
        , ("ambient_choice_state", "forbidden")
        , ("runtime_symbol_identity", "physical primitive/signature")
        , ("external_runtime_gate", "exact one-octet encode/decode behavior checked independently in CI")
        , ("external_llvm_gate", "canonical target text must be accepted by LLVM 18 in CI")
        ]
      evidenceScope = ValidityScope $
        Map.insert "target" certificationTarget $
        Map.insert "compilation_profile" certificationProfile validityContext
      revisionStatement =
        "The canonical Phase 0 payload/cancel Systems -> pre-optimization LLVM pair is certified only for the exact source, target, target text, target profile, and phil-runtime/phase0/payload-cancel-choice-v1 ABI bound by this revision; Phil translation validation establishes exact client/server transport identity, canonical payload=0x01 and cancel=0x00 selector constants, exact server continuation mapping, preservation of local should_cancel computation and final-response lowering, and absence of generic/ambient choice state, while concrete one-octet I/O, reserved/EOF non-return, physical write success, provider conformance, LLVM 18, linking, and native execution remain external gates."
      provisionalRevision = ObligationRevision
        { revisionObligationId = ObligationId "PHIL-LLVM-CERT-009"
        , revisionId = RevisionId ""
        , revisionStatement = revisionStatement
        , revisionStatementDigest = digestText revisionStatement
        , revisionKind = "LLVMPayloadCancelChoiceTranslationCertification"
        , revisionOrigin = "payload/cancel choice ABI v1 / PHIL-LLVM-CERT-009"
        , revisionScope = "llvm.phase0.preopt.payload-cancel-choice.translation"
        , revisionRequiredAt = "certification"
        , revisionRepresentation =
            "payload/cancel semantic SystemsArtifact -> explicit one-octet selector/receiver canonical pre-optimization LLVMArtifact"
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
        , revisionAcceptanceRule = AcceptEntry TranslationValidated (EvidenceRole "translation_validated")
        , revisionGeneratedFrom = []
        }
      certificationRevision = provisionalRevision
        { revisionId = deriveRevisionId provisionalRevision }
      certificationRevisionId = revisionId certificationRevision
      translationArtifactRecord = Text.unlines
        [ "phil-llvm-phase0-payload-cancel-choice-translation-validation-v1"
        , "source-digest=" <> unDigest sourceDigest
        , "target-digest=" <> unDigest targetDigest
        , "target-text-digest=" <> unDigest targetTextDigest
        , "llvm-language=" <> llvmLanguageVersion moduleValue
        , "llvm-tool-profile=" <> llvmToolVersion moduleValue
        , "target-triple=" <> llvmTargetTriple moduleValue
        , "data-layout=" <> llvmDataLayout moduleValue
        , "runtime-abi-digest=" <> unDigest abiDigest
        , "runtime-abi-profile=" <> llvmRuntimeABIProfile moduleValue
        , "translation-validator=Phil.LLVM.PayloadCancelChoice.verifyPayloadCancelChoiceTranslation"
        , "assurance-checker=Phil.Assurance.Verify.verifyManifest"
        ]
      translationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef
            "artifact:phil:llvm:phase0:payload-cancel-choice:translation-validation:v1"
        , artifactDigest = digestText translationArtifactRecord
        }
      evidenceId = EvidenceEntryId
        "evidence.llvm.phase0.payload-cancel-choice.translation.validated"
      provisionalEvidence = EvidenceEntry
        { evidenceEntryId = evidenceId
        , evidenceEntryDigest = Digest ""
        , evidenceObligationRevision = certificationRevisionId
        , evidenceAssuranceKind = TranslationValidated
        , evidenceRole = EvidenceRole "translation_validated"
        , evidenceProducer = "Phil.LLVM.PayloadCancelChoice.verifyPayloadCancelChoiceTranslation"
        , evidenceChecker = "Phil.Assurance.Verify.verifyManifest"
        , evidenceArtifact = Just translationArtifact
        , evidenceInputDigests = [sourceDigest, targetDigest, targetTextDigest, abiDigest]
        , evidenceAssumptions = []
        , evidenceDependsOn = []
        , evidenceValidityScope = evidenceScope
        , evidenceResult = EvidenceAccepted
        , evidenceJustifies =
            [ "client payload select uses exact transport and canonical i8 0x01"
            , "client cancel select uses exact transport and canonical i8 0x00"
            , "server receiver uses exact transport and maps true->payload false->cancel"
            , "legacy generic select/receive-label calls are eliminated"
            , "ambient payload/cancel choice state is absent"
            , "local should_cancel computation remains separate from protocol choice"
            , "final accepted/rejected response lowering remains intact"
            , "no malformed-choice CFG edge is invented"
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
        [ "phil-llvm-phase0-payload-cancel-choice-certification-root-v1"
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
  pure PayloadCancelChoiceCertificationBundle
    { payloadCancelChoiceCertificationSystems = systemsBundle
    , payloadCancelChoiceCertificationLLVM = llvmArtifact
    , payloadCancelChoiceCertificationArtifact = translationArtifact
    , payloadCancelChoiceCertificationLedger = ledger
    , payloadCancelChoiceCertificationManifest = manifest
    , payloadCancelChoiceCertificationContext = verificationContext
    }

verifyPhase0PayloadCancelChoiceLLVMCertification
  :: Either PayloadCancelChoiceCertificationError ()
verifyPhase0PayloadCancelChoiceLLVMCertification = do
  bundle <- phase0PayloadCancelChoiceLLVMCertification
  mapLeft PayloadCancelChoiceCertificationManifestError $
    verifyManifest
      (payloadCancelChoiceCertificationContext bundle)
      (payloadCancelChoiceCertificationLedger bundle)
      (payloadCancelChoiceCertificationManifest bundle)

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
