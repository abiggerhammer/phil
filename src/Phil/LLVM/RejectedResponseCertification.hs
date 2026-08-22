{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.RejectedResponseCertification
  ( RejectedResponseCertificationError (..)
  , RejectedResponseCertificationBundle (..)
  , phase0RejectedResponseLLVMCertification
  , verifyPhase0RejectedResponseLLVMCertification
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Assurance.Types
import Phil.Assurance.Verify (ManifestError, verifyManifest)
import Phil.Core.Syntax (ObligationId (..))
import Phil.LLVM.IR
import Phil.LLVM.RejectedResponse
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

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
