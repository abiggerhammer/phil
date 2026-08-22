{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.AcceptedResponseCertification
  ( AcceptedResponseCertificationError (..)
  , AcceptedResponseCertificationBundle (..)
  , phase0AcceptedResponseLLVMCertification
  , verifyPhase0AcceptedResponseLLVMCertification
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Assurance.Types
import Phil.Assurance.Verify (ManifestError, verifyManifest)
import Phil.Core.Syntax (ObligationId (..))
import Phil.LLVM.AcceptedResponse
import Phil.LLVM.IR
import Phil.LLVM.Lower (lowerSystemsAcceptedResponse)
import Phil.Systems.AcceptedResponse
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

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
