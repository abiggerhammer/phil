{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.RecognizedRecordCertification
  ( RecognizedRecordCertificationError (..)
  , RecognizedRecordCertificationBundle (..)
  , phase0RecognizedRecordLLVMCertification
  , verifyPhase0RecognizedRecordLLVMCertification
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Assurance.Types
import Phil.Assurance.Verify (ManifestError, verifyManifest)
import Phil.Core.Syntax (ObligationId (..))
import Phil.LLVM.IR
import Phil.LLVM.Lower (lowerSystemsRecognizedRecord)
import Phil.LLVM.RecognizedRecord
import Phil.Systems.RecognizedRecord
import Phil.Systems.Verify (SystemsVerificationContext (..))

data RecognizedRecordCertificationError
  = RecognizedRecordCertificationSystemsError RecognizedRecordError
  | RecognizedRecordCertificationTranslationError RecognizedRecordLLVMError
  | RecognizedRecordCertificationManifestError ManifestError
  deriving (Eq, Show)

data RecognizedRecordCertificationBundle = RecognizedRecordCertificationBundle
  { recognizedRecordCertificationSystems :: RecognizedRecordBundle
  , recognizedRecordCertificationLLVM :: LLVMArtifact
  , recognizedRecordCertificationArtifact :: ArtifactIdentity
  , recognizedRecordCertificationLedger :: AssuranceLedger
  , recognizedRecordCertificationManifest :: AssuranceManifest
  , recognizedRecordCertificationContext :: VerificationContext
  }
  deriving (Eq, Show)

-- PHIL-LLVM-CERT-002
--
-- This is deliberately a new exact-artifact certification rather than a
-- revision of PHIL-LLVM-CERT-001.  The latter remains bound to the historical
-- reference-v1 runtime ABI.  LLVM 18 assembly of the emitted text is still an
-- external CI gate and is not represented as if pure Haskell could attest it.
phase0RecognizedRecordLLVMCertification
  :: Either RecognizedRecordCertificationError RecognizedRecordCertificationBundle
phase0RecognizedRecordLLVMCertification = do
  systemsBundle <- mapLeft
    RecognizedRecordCertificationSystemsError
    phase0RecognizedRecordBundle
  let systemsArtifact = recognizedRecordArtifact systemsBundle
      llvmArtifact = lowerSystemsRecognizedRecord
        phase0RecognizedRecordLLVMTarget
        systemsArtifact
  mapLeft RecognizedRecordCertificationTranslationError $
    verifyRecognizedRecordTranslation systemsBundle llvmArtifact
  let systemsManifest = systemsAssuranceManifest (recognizedRecordContext systemsBundle)
      moduleValue = llvmArtifactModule llvmArtifact
      sourceDigest = llvmContractSourceDigest (llvmArtifactContract llvmArtifact)
      targetDigest = llvmContractTargetDigest (llvmArtifactContract llvmArtifact)
      targetTextDigest = digestText (llvmArtifactText llvmArtifact)
      abiDigest = llvmRuntimeABIDigest moduleValue
      certificationTarget = "preopt-llvm:" <> llvmTargetTriple moduleValue
      sourceCompilationProfile = Text.pack (show (llvmCompilationProfile moduleValue))
      certificationProfile =
        "translation-validation/" <> sourceCompilationProfile <> "/recognized-record-v1"
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
        , ("recognized_record_abi", "{i8,ptr}; status==1; opaque ptr; typed accessor")
        , ("runtime_symbol_identity", "physical primitive/signature")
        , ("exact_receive_dependency", "Begin.length:i64 -> receive_exact_u64(i64)")
        , ("external_llvm_gate", "canonical target text must be accepted by an LLVM 18 assembler in CI")
        ]
      evidenceScope = ValidityScope $
        Map.insert "target" certificationTarget $
        Map.insert "compilation_profile" certificationProfile $
        validityContext
      revisionStatement =
        "The canonical Phase 0 recognized-record Systems -> pre-optimization LLVM pair is certified only for the exact source, target, target text, target profile, and phil-runtime/phase0/recognized-record-v1 ABI bound by this revision; successful independent Phil translation validation is selected as TranslationValidated evidence, while LLVM 18 acceptance remains an external certification gate."
      provisionalRevision = ObligationRevision
        { revisionObligationId = ObligationId "PHIL-LLVM-CERT-002"
        , revisionId = RevisionId ""
        , revisionStatement = revisionStatement
        , revisionStatementDigest = digestText revisionStatement
        , revisionKind = "LLVMRecognizedRecordTranslationCertification"
        , revisionOrigin = "recognized-record ABI v1 / PHIL-LLVM-CERT-002"
        , revisionScope = "llvm.phase0.preopt.recognized-record.translation"
        , revisionRequiredAt = "certification"
        , revisionRepresentation =
            "recognized-record SystemsArtifact -> canonical pre-optimization LLVMArtifact"
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
        [ "phil-llvm-phase0-recognized-record-translation-validation-v1"
        , "source-digest=" <> unDigest sourceDigest
        , "target-digest=" <> unDigest targetDigest
        , "target-text-digest=" <> unDigest targetTextDigest
        , "llvm-language=" <> llvmLanguageVersion moduleValue
        , "llvm-tool-profile=" <> llvmToolVersion moduleValue
        , "target-triple=" <> llvmTargetTriple moduleValue
        , "data-layout=" <> llvmDataLayout moduleValue
        , "runtime-abi-digest=" <> unDigest abiDigest
        , "runtime-abi-profile=" <> llvmRuntimeABIProfile moduleValue
        , "translation-validator=Phil.LLVM.RecognizedRecord.verifyRecognizedRecordTranslation"
        , "assurance-checker=Phil.Assurance.Verify.verifyManifest"
        ]
      translationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef
            "artifact:phil:llvm:phase0:recognized-record:translation-validation:v1"
        , artifactDigest = digestText translationArtifactRecord
        }
      evidenceId = EvidenceEntryId
        "evidence.llvm.phase0.recognized-record.translation.validated"
      provisionalEvidence = EvidenceEntry
        { evidenceEntryId = evidenceId
        , evidenceEntryDigest = Digest ""
        , evidenceObligationRevision = certificationRevisionId
        , evidenceAssuranceKind = TranslationValidated
        , evidenceRole = EvidenceRole "translation_validated"
        , evidenceProducer =
            "Phil.LLVM.RecognizedRecord.verifyRecognizedRecordTranslation"
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
            [ "exact recognized-record identity"
            , "exact Begin.length field identity and i64 width"
            , "exact receive consumes projected scalar"
            , "fail-closed recognition status"
            , "physical runtime symbol identity"
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
        [ "phil-llvm-phase0-recognized-record-certification-root-v1"
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
  pure RecognizedRecordCertificationBundle
    { recognizedRecordCertificationSystems = systemsBundle
    , recognizedRecordCertificationLLVM = llvmArtifact
    , recognizedRecordCertificationArtifact = translationArtifact
    , recognizedRecordCertificationLedger = ledger
    , recognizedRecordCertificationManifest = manifest
    , recognizedRecordCertificationContext = verificationContext
    }

verifyPhase0RecognizedRecordLLVMCertification
  :: Either RecognizedRecordCertificationError ()
verifyPhase0RecognizedRecordLLVMCertification = do
  bundle <- phase0RecognizedRecordLLVMCertification
  mapLeft RecognizedRecordCertificationManifestError $
    verifyManifest
      (recognizedRecordCertificationContext bundle)
      (recognizedRecordCertificationLedger bundle)
      (recognizedRecordCertificationManifest bundle)

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
