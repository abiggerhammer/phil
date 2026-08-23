{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.VersionSessionChoiceCertification
  ( VersionSessionChoiceCertificationError (..)
  , VersionSessionChoiceCertificationBundle (..)
  , phase0VersionSessionChoiceLLVMCertification
  , verifyPhase0VersionSessionChoiceLLVMCertification
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Assurance.Types
import Phil.Assurance.Verify (ManifestError, verifyManifest)
import Phil.Core.Syntax (ObligationId (..))
import Phil.LLVM.IR
import Phil.LLVM.VersionSessionChoice
import Phil.Systems.VersionChoiceOperands
import Phil.Systems.Verify (SystemsVerificationContext (..))

data VersionSessionChoiceCertificationError
  = VersionSessionChoiceCertificationSystemsError VersionChoiceOperandsError
  | VersionSessionChoiceCertificationTranslationError VersionSessionChoiceLLVMError
  | VersionSessionChoiceCertificationManifestError ManifestError
  deriving (Eq, Show)

data VersionSessionChoiceCertificationBundle = VersionSessionChoiceCertificationBundle
  { versionSessionChoiceCertificationSystems :: VersionChoiceOperandsBundle
  , versionSessionChoiceCertificationLLVM :: LLVMArtifact
  , versionSessionChoiceCertificationArtifact :: ArtifactIdentity
  , versionSessionChoiceCertificationLedger :: AssuranceLedger
  , versionSessionChoiceCertificationManifest :: AssuranceManifest
  , versionSessionChoiceCertificationContext :: VerificationContext
  }
  deriving (Eq, Show)

-- PHIL-LLVM-CERT-010
--
-- Translation-only authority for version-session-choice-v1. The provider's
-- choose_supported set semantics, opaque version-set representation, concrete
-- byte I/O, malformed-input non-return, physical write success, LLVM 18,
-- linking, and native execution remain independent gates.
phase0VersionSessionChoiceLLVMCertification
  :: Either VersionSessionChoiceCertificationError VersionSessionChoiceCertificationBundle
phase0VersionSessionChoiceLLVMCertification = do
  systemsBundle <- mapLeft
    VersionSessionChoiceCertificationSystemsError
    phase0VersionChoiceOperandsBundle
  let systemsArtifact = versionChoiceOperandsArtifact systemsBundle
      llvmArtifact = lowerSystemsVersionSessionChoice
        phase0VersionSessionChoiceLLVMTarget
        systemsArtifact
  mapLeft VersionSessionChoiceCertificationTranslationError $
    verifyVersionSessionChoiceTranslation systemsBundle llvmArtifact
  let systemsManifest = systemsAssuranceManifest (versionChoiceOperandsContext systemsBundle)
      moduleValue = llvmArtifactModule llvmArtifact
      sourceDigest = llvmContractSourceDigest (llvmArtifactContract llvmArtifact)
      targetDigest = llvmContractTargetDigest (llvmArtifactContract llvmArtifact)
      targetTextDigest = digestText (llvmArtifactText llvmArtifact)
      abiDigest = llvmRuntimeABIDigest moduleValue
      certificationTarget = "preopt-llvm:" <> llvmTargetTriple moduleValue
      sourceCompilationProfile = Text.pack (show (llvmCompilationProfile moduleValue))
      certificationProfile =
        "translation-validation/" <> sourceCompilationProfile <> "/version-session-choice-v1"
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
        , ("server_supported", "explicit UploadServer ptr parameter")
        , ("hello_versions_projection", "phil_record_Hello_get_versions(ptr)->ptr")
        , ("chooser", "phil_runtime_choose_supported(ptr,ptr,ptr)->i1")
        , ("unsupported_selector", "phil_runtime_select_unsupported(ptr)->void")
        , ("version_selector", "phil_runtime_select_version(ptr,i16)->void")
        , ("receiver", "phil_runtime_receive_version_choice(ptr,ptr)->i1")
        , ("wire_unsupported", "0x00")
        , ("wire_version", "0x01 followed by UInt16 big-endian")
        , ("malformed_input", "tag EOF, reserved tag, or truncated UInt16 must not return normally")
        , ("write_failure", "residual runtime assumption")
        , ("outer_framing", "not defined by version-session-choice-v1")
        , ("ambient_state", "forbidden")
        , ("provider_choose_semantics", "external runtime gate")
        , ("external_runtime_gate", "chooser semantics and concrete encoding checked independently in CI")
        , ("external_llvm_gate", "canonical target text must be accepted by LLVM 18 in CI")
        ]
      evidenceScope = ValidityScope $
        Map.insert "target" certificationTarget $
        Map.insert "compilation_profile" certificationProfile validityContext
      revisionStatement =
        "The canonical Phase 0 version/unsupported Systems -> pre-optimization LLVM pair is certified only for the exact source, target, target text, target profile, and phil-runtime/phase0/version-session-choice-v1 ABI bound by this revision; Phil translation validation establishes explicit serverSupported and recognized Hello.versions operand identity, exact choose_supported input/output flow, exact server selectors, exact client receiver and branch-local UInt16 binding, preservation of payload/cancel physical lowering, and absence of ambient choice/version/transport state, while provider set-selection semantics, opaque version-set representation, concrete byte I/O, malformed-input non-return, physical write success, provider conformance, LLVM 18, linking, and native execution remain external gates."
      provisionalRevision = ObligationRevision
        { revisionObligationId = ObligationId "PHIL-LLVM-CERT-010"
        , revisionId = RevisionId ""
        , revisionStatement = revisionStatement
        , revisionStatementDigest = digestText revisionStatement
        , revisionKind = "LLVMVersionSessionChoiceTranslationCertification"
        , revisionOrigin = "version/unsupported choice ABI v1 / PHIL-LLVM-CERT-010"
        , revisionScope = "llvm.phase0.preopt.version-session-choice.translation"
        , revisionRequiredAt = "certification"
        , revisionRepresentation =
            "explicit version-choice operands SystemsArtifact -> choose_supported + version/unsupported physical primitives canonical pre-optimization LLVMArtifact"
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
        [ "phil-llvm-phase0-version-session-choice-translation-validation-v1"
        , "source-digest=" <> unDigest sourceDigest
        , "target-digest=" <> unDigest targetDigest
        , "target-text-digest=" <> unDigest targetTextDigest
        , "llvm-language=" <> llvmLanguageVersion moduleValue
        , "llvm-tool-profile=" <> llvmToolVersion moduleValue
        , "target-triple=" <> llvmTargetTriple moduleValue
        , "data-layout=" <> llvmDataLayout moduleValue
        , "runtime-abi-digest=" <> unDigest abiDigest
        , "runtime-abi-profile=" <> llvmRuntimeABIProfile moduleValue
        , "translation-validator=Phil.LLVM.VersionSessionChoice.verifyVersionSessionChoiceTranslation"
        , "assurance-checker=Phil.Assurance.Verify.verifyManifest"
        ]
      translationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef
            "artifact:phil:llvm:phase0:version-session-choice:translation-validation:v1"
        , artifactDigest = digestText translationArtifactRecord
        }
      evidenceId = EvidenceEntryId
        "evidence.llvm.phase0.version-session-choice.translation.validated"
      provisionalEvidence = EvidenceEntry
        { evidenceEntryId = evidenceId
        , evidenceEntryDigest = Digest ""
        , evidenceObligationRevision = certificationRevisionId
        , evidenceAssuranceKind = TranslationValidated
        , evidenceRole = EvidenceRole "translation_validated"
        , evidenceProducer = "Phil.LLVM.VersionSessionChoice.verifyVersionSessionChoiceTranslation"
        , evidenceChecker = "Phil.Assurance.Verify.verifyManifest"
        , evidenceArtifact = Just translationArtifact
        , evidenceInputDigests = [sourceDigest, targetDigest, targetTextDigest, abiDigest]
        , evidenceAssumptions = []
        , evidenceDependsOn = []
        , evidenceValidityScope = evidenceScope
        , evidenceResult = EvidenceAccepted
        , evidenceJustifies =
            [ "serverSupported is an explicit target parameter rather than ambient runtime state"
            , "recognized Hello.versions is projected explicitly and feeds choose_supported"
            , "choose_supported maps none/some control and selected UInt16 into exact target SSA flow"
            , "server unsupported select uses exact transport and no payload"
            , "server version select uses exact transport and selected UInt16"
            , "client receiver maps false->unsupported true->version and binds selected UInt16 only on version"
            , "payload/cancel and final-response physical lowerings remain intact"
            , "generic version/unsupported select/receive machinery is eliminated"
            , "ambient supported/offered/selected-version and transport state is absent"
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
        [ "phil-llvm-phase0-version-session-choice-certification-root-v1"
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
  pure VersionSessionChoiceCertificationBundle
    { versionSessionChoiceCertificationSystems = systemsBundle
    , versionSessionChoiceCertificationLLVM = llvmArtifact
    , versionSessionChoiceCertificationArtifact = translationArtifact
    , versionSessionChoiceCertificationLedger = ledger
    , versionSessionChoiceCertificationManifest = manifest
    , versionSessionChoiceCertificationContext = verificationContext
    }

verifyPhase0VersionSessionChoiceLLVMCertification
  :: Either VersionSessionChoiceCertificationError ()
verifyPhase0VersionSessionChoiceLLVMCertification = do
  bundle <- phase0VersionSessionChoiceLLVMCertification
  mapLeft VersionSessionChoiceCertificationManifestError $
    verifyManifest
      (versionSessionChoiceCertificationContext bundle)
      (versionSessionChoiceCertificationLedger bundle)
      (versionSessionChoiceCertificationManifest bundle)

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
