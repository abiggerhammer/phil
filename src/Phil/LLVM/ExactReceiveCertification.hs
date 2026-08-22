{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.ExactReceiveCertification
  ( ExactReceiveCertificationError (..)
  , ExactReceiveCertificationBundle (..)
  , phase0ExactReceiveLLVMCertification
  , verifyPhase0ExactReceiveLLVMCertification
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Assurance.Types
import Phil.Assurance.Verify (ManifestError, verifyManifest)
import Phil.Core.Syntax (ObligationId (..))
import Phil.LLVM.ExactReceive
import Phil.LLVM.IR
import Phil.LLVM.Lower (lowerSystemsExactReceive)
import Phil.Systems.RecognizedRecord
import Phil.Systems.Verify (SystemsVerificationContext (..))

data ExactReceiveCertificationError
  = ExactReceiveCertificationSystemsError RecognizedRecordError
  | ExactReceiveCertificationTranslationError ExactReceiveLLVMError
  | ExactReceiveCertificationManifestError ManifestError
  deriving (Eq, Show)

data ExactReceiveCertificationBundle = ExactReceiveCertificationBundle
  { exactReceiveCertificationSystems :: RecognizedRecordBundle
  , exactReceiveCertificationLLVM :: LLVMArtifact
  , exactReceiveCertificationArtifact :: ArtifactIdentity
  , exactReceiveCertificationLedger :: AssuranceLedger
  , exactReceiveCertificationManifest :: AssuranceManifest
  , exactReceiveCertificationContext :: VerificationContext
  }
  deriving (Eq, Show)

-- PHIL-LLVM-CERT-003
--
-- This certification is content-bound to the transport-exact-receive-v1
-- candidate. PHIL-LLVM-CERT-002 remains bound to recognized-record-v1. The
-- runtime signature checker, LLVM 18 assembly/linking, and executable in-memory
-- transport fixture are independent external gates rather than claims made by
-- this pure translation-validation certificate.
phase0ExactReceiveLLVMCertification
  :: Either ExactReceiveCertificationError ExactReceiveCertificationBundle
phase0ExactReceiveLLVMCertification = do
  systemsBundle <- mapLeft
    ExactReceiveCertificationSystemsError
    phase0RecognizedRecordBundle
  let systemsArtifact = recognizedRecordArtifact systemsBundle
      llvmArtifact = lowerSystemsExactReceive
        phase0ExactReceiveLLVMTarget
        systemsArtifact
  mapLeft ExactReceiveCertificationTranslationError $
    verifyExactReceiveTranslation systemsBundle llvmArtifact
  let systemsManifest = systemsAssuranceManifest (recognizedRecordContext systemsBundle)
      moduleValue = llvmArtifactModule llvmArtifact
      sourceDigest = llvmContractSourceDigest (llvmArtifactContract llvmArtifact)
      targetDigest = llvmContractTargetDigest (llvmArtifactContract llvmArtifact)
      targetTextDigest = digestText (llvmArtifactText llvmArtifact)
      abiDigest = llvmRuntimeABIDigest moduleValue
      certificationTarget = "preopt-llvm:" <> llvmTargetTriple moduleValue
      sourceCompilationProfile = Text.pack (show (llvmCompilationProfile moduleValue))
      certificationProfile =
        "translation-validation/" <> sourceCompilationProfile <> "/transport-exact-receive-v1"
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
        , ("transport_representation", "Systems TransportHandle -> component-entry opaque ptr")
        , ("recognized_record_abi", "{i8,ptr}; status==1; opaque record ptr; typed accessor")
        , ("exact_receive_dependency", "transport:ptr, Begin.length:i64 -> {status:i8,payload:ptr}")
        , ("payload_owner_identity", "Systems exactPayloadOwner -> deterministic .owner SSA -> phil_buffer_release(ptr)")
        , ("runtime_symbol_identity", "physical primitive/signature")
        , ("ambient_transport", "forbidden")
        , ("external_runtime_gate", "provider LLVM signatures checked independently; in-memory transport fixture executes in CI")
        , ("external_llvm_gate", "canonical target text must be accepted by LLVM 18 in CI")
        ]
      evidenceScope = ValidityScope $
        Map.insert "target" certificationTarget $
        Map.insert "compilation_profile" certificationProfile $
        validityContext
      revisionStatement =
        "The canonical Phase 0 recognized-record Systems -> pre-optimization LLVM transport-exact-receive pair is certified only for the exact source, target, target text, target profile, and phil-runtime/phase0/transport-exact-receive-v1 ABI bound by this revision; successful independent Phil translation validation is selected as TranslationValidated evidence, while runtime-provider conformance, LLVM 18 acceptance, linking, and execution remain external certification gates."
      provisionalRevision = ObligationRevision
        { revisionObligationId = ObligationId "PHIL-LLVM-CERT-003"
        , revisionId = RevisionId ""
        , revisionStatement = revisionStatement
        , revisionStatementDigest = digestText revisionStatement
        , revisionKind = "LLVMTransportExactReceiveTranslationCertification"
        , revisionOrigin = "transport exact-receive ABI v1 / PHIL-LLVM-CERT-003"
        , revisionScope = "llvm.phase0.preopt.transport-exact-receive.translation"
        , revisionRequiredAt = "certification"
        , revisionRepresentation =
            "recognized-record SystemsArtifact -> transport-explicit canonical pre-optimization LLVMArtifact"
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
        [ "phil-llvm-phase0-transport-exact-receive-translation-validation-v1"
        , "source-digest=" <> unDigest sourceDigest
        , "target-digest=" <> unDigest targetDigest
        , "target-text-digest=" <> unDigest targetTextDigest
        , "llvm-language=" <> llvmLanguageVersion moduleValue
        , "llvm-tool-profile=" <> llvmToolVersion moduleValue
        , "target-triple=" <> llvmTargetTriple moduleValue
        , "data-layout=" <> llvmDataLayout moduleValue
        , "runtime-abi-digest=" <> unDigest abiDigest
        , "runtime-abi-profile=" <> llvmRuntimeABIProfile moduleValue
        , "translation-validator=Phil.LLVM.ExactReceive.verifyExactReceiveTranslation"
        , "assurance-checker=Phil.Assurance.Verify.verifyManifest"
        ]
      translationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef
            "artifact:phil:llvm:phase0:transport-exact-receive:translation-validation:v1"
        , artifactDigest = digestText translationArtifactRecord
        }
      evidenceId = EvidenceEntryId
        "evidence.llvm.phase0.transport-exact-receive.translation.validated"
      provisionalEvidence = EvidenceEntry
        { evidenceEntryId = evidenceId
        , evidenceEntryDigest = Digest ""
        , evidenceObligationRevision = certificationRevisionId
        , evidenceAssuranceKind = TranslationValidated
        , evidenceRole = EvidenceRole "translation_validated"
        , evidenceProducer =
            "Phil.LLVM.ExactReceive.verifyExactReceiveTranslation"
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
            [ "exact component transport parameter identity"
            , "exact recognized Begin record identity"
            , "exact Begin.length field identity and i64 width"
            , "exact receive consumes the selected transport and projected length"
            , "exact receive materializes the Systems payload owner"
            , "exact status==1 success discipline"
            , "EarlyEOF releases the exact returned partial owner"
            , "physical runtime symbol identity with no ambient transport"
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
        [ "phil-llvm-phase0-transport-exact-receive-certification-root-v1"
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
  pure ExactReceiveCertificationBundle
    { exactReceiveCertificationSystems = systemsBundle
    , exactReceiveCertificationLLVM = llvmArtifact
    , exactReceiveCertificationArtifact = translationArtifact
    , exactReceiveCertificationLedger = ledger
    , exactReceiveCertificationManifest = manifest
    , exactReceiveCertificationContext = verificationContext
    }

verifyPhase0ExactReceiveLLVMCertification
  :: Either ExactReceiveCertificationError ()
verifyPhase0ExactReceiveLLVMCertification = do
  bundle <- phase0ExactReceiveLLVMCertification
  mapLeft ExactReceiveCertificationManifestError $
    verifyManifest
      (exactReceiveCertificationContext bundle)
      (exactReceiveCertificationLedger bundle)
      (exactReceiveCertificationManifest bundle)

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
