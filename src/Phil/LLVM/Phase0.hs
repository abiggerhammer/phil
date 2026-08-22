{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.Phase0
  ( Phase0LLVMCertificationError (..)
  , phase0LLVMTarget
  , phase0LLVMArtifact
  , phase0LLVMVerificationContext
  , phase0LLVMTranslationValidationArtifact
  , phase0LLVMCertificationLedger
  , phase0LLVMCertificationManifest
  , phase0LLVMCertificationContext
  , verifyPhase0LLVMCertification
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types
import Phil.Assurance.Verify (ManifestError, verifyManifest)
import Phil.Core.Syntax (ObligationId (..))
import Phil.LLVM.IR
import Phil.LLVM.Lower (lowerSystemsConservative)
import Phil.LLVM.Verify
  ( LLVMVerificationContext (..)
  , LLVMVerificationError
  , verifyLLVMEmission
  )
import Phil.Systems.Phase0
  ( phase0SystemsArtifact
  , phase0SystemsAssuranceManifest
  , phase0SystemsVerificationContext
  )

phase0LLVMTarget :: LLVMTargetProfile
phase0LLVMTarget = LLVMTargetProfile
  { llvmTargetLanguageVersion = "LLVM IR 18 opaque-pointer subset"
  , llvmTargetToolVersion = "llvm-as 18.x expected"
  , llvmTargetTripleName = "x86_64-unknown-linux-gnu"
  , llvmTargetDataLayout =
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
  , llvmTargetRuntimeABIDigest = digestText "phil-runtime/phase0/reference-v1"
  , llvmTargetRuntimeABIProfile = "phil-runtime/phase0/reference-v1"
  }

phase0LLVMArtifact :: LLVMArtifact
phase0LLVMArtifact = lowerSystemsConservative phase0LLVMTarget phase0SystemsArtifact

phase0LLVMVerificationContext :: LLVMVerificationContext
phase0LLVMVerificationContext = LLVMVerificationContext
  { llvmSystemsContext = phase0SystemsVerificationContext
  , llvmExpectedLanguageVersion = llvmTargetLanguageVersion phase0LLVMTarget
  , llvmExpectedToolVersion = llvmTargetToolVersion phase0LLVMTarget
  , llvmExpectedTargetTriple = llvmTargetTripleName phase0LLVMTarget
  , llvmExpectedDataLayout = llvmTargetDataLayout phase0LLVMTarget
  , llvmExpectedRuntimeABIDigest = llvmTargetRuntimeABIDigest phase0LLVMTarget
  , llvmExpectedRuntimeABIProfile = llvmTargetRuntimeABIProfile phase0LLVMTarget
  , llvmAuthorizedStrengthenings = Map.empty
  }

-- PHIL-LLVM-CERT-001
--
-- The manifest below records the exact Phil-side translation-validation result
-- for the canonical Phase 0 Systems -> pre-optimization LLVM pair.  It does not
-- pretend that a pure Haskell value can attest execution of an external LLVM
-- binary.  The complete certification gate is deliberately ordered in CI:
--
--   verifyLLVMEmission
--   -> verifyManifest with selected TranslationValidated evidence
--   -> emit this exact canonical LLVM text
--   -> llvm-as 18 accepts that text
--
-- The final llvm-as step remains an explicit external TCB boundary.

data Phase0LLVMCertificationError
  = Phase0LLVMTranslationRejected LLVMVerificationError
  | Phase0LLVMManifestRejected ManifestError
  deriving (Eq, Show)

verifyPhase0LLVMCertification :: Either Phase0LLVMCertificationError ()
verifyPhase0LLVMCertification = do
  mapLeft Phase0LLVMTranslationRejected $
    verifyLLVMEmission
      phase0LLVMVerificationContext
      phase0SystemsArtifact
      phase0LLVMArtifact
  mapLeft Phase0LLVMManifestRejected $
    verifyManifest
      phase0LLVMCertificationContext
      phase0LLVMCertificationLedger
      phase0LLVMCertificationManifest

phase0LLVMCertificationLedger :: AssuranceLedger
phase0LLVMCertificationLedger = emptyLedger
  { ledgerRevisions = Map.singleton
      (revisionId phase0LLVMCertificationRevision)
      phase0LLVMCertificationRevision
  , ledgerEvidence = Map.singleton
      (evidenceEntryId phase0LLVMTranslationValidationEvidence)
      phase0LLVMTranslationValidationEvidence
  }

phase0LLVMCertificationManifest :: AssuranceManifest
phase0LLVMCertificationManifest = provisionalManifest
  { manifestId = deriveManifestId phase0LLVMCertificationLedger provisionalManifest }
  where
    provisionalManifest = emptyManifest
      { manifestArchitectureDigest =
          manifestArchitectureDigest phase0SystemsAssuranceManifest
      , manifestPhilCoreDigest =
          manifestPhilCoreDigest phase0SystemsAssuranceManifest
      , manifestImplementationDigest =
          artifactDigest phase0LLVMTranslationValidationArtifact
      , manifestTarget = phase0LLVMCertificationTarget
      , manifestCompilationProfile = phase0LLVMCertificationProfile
      , manifestObligationRevisions = Set.singleton certificationRevisionId
      , manifestCertificationScope = Set.singleton certificationRevisionId
      , manifestEvidenceEntries = Set.singleton translationValidationEvidenceId
      , manifestLoweringLedgerRoot = phase0LLVMCertificationRoot
      , manifestValidityContext = phase0LLVMCertificationValidityContext
      }

phase0LLVMCertificationContext :: VerificationContext
phase0LLVMCertificationContext = emptyVerificationContext
  { verificationArchitectureDigest =
      manifestArchitectureDigest phase0SystemsAssuranceManifest
  , verificationPhilCoreDigest =
      manifestPhilCoreDigest phase0SystemsAssuranceManifest
  , verificationImplementationDigest =
      artifactDigest phase0LLVMTranslationValidationArtifact
  , verificationTarget = phase0LLVMCertificationTarget
  , verificationCompilationProfile = phase0LLVMCertificationProfile
  , verificationExpectedObligations = Set.singleton certificationRevisionId
  , verificationAvailableArtifacts = Map.singleton
      (artifactReference phase0LLVMTranslationValidationArtifact)
      (artifactDigest phase0LLVMTranslationValidationArtifact)
  , verificationLoweringLedgerRoot = phase0LLVMCertificationRoot
  , verificationValidityContext = phase0LLVMCertificationValidityContext
  }

phase0LLVMTranslationValidationArtifact :: ArtifactIdentity
phase0LLVMTranslationValidationArtifact = ArtifactIdentity
  { artifactReference = ArtifactRef "artifact:phil:llvm:phase0:translation-validation:v1"
  , artifactDigest = digestText phase0LLVMTranslationValidationRecord
  }

phase0LLVMCertificationRevision :: ObligationRevision
phase0LLVMCertificationRevision = provisional
  { revisionId = deriveRevisionId provisional }
  where
    provisional = ObligationRevision
      { revisionObligationId = ObligationId "PHIL-LLVM-CERT-001"
      , revisionId = RevisionId ""
      , revisionStatement =
          "The canonical Phase 0 Systems -> pre-optimization LLVM pair is certified only for the exact source, target, target profile, runtime ABI, and compilation context bound by this revision; successful Phil translation validation is selected as TranslationValidated evidence, while LLVM 18 acceptance remains an external certification gate."
      , revisionStatementDigest = digestText
          "The canonical Phase 0 Systems -> pre-optimization LLVM pair is certified only for the exact source, target, target profile, runtime ABI, and compilation context bound by this revision; successful Phil translation validation is selected as TranslationValidated evidence, while LLVM 18 acceptance remains an external certification gate."
      , revisionKind = "LLVMTranslationCertification"
      , revisionOrigin = "ADR-010 / logic ledger PHIL-LLVM-CERT-001"
      , revisionScope = "llvm.phase0.preopt.translation"
      , revisionRequiredAt = "certification"
      , revisionRepresentation = "SystemsArtifact -> canonical pre-optimization LLVMArtifact"
      , revisionSubjectIds =
          [ "systems:" <> unDigest phase0LLVMCertifiedSourceDigest
          , "llvm:" <> unDigest phase0LLVMCertifiedTargetDigest
          , "llvm-text:" <> unDigest phase0LLVMCertifiedTextDigest
          ]
      , revisionContextIds =
          [ "language:" <> llvmLanguageVersion phase0LLVMModule
          , "tool-profile:" <> llvmToolVersion phase0LLVMModule
          , "target:" <> llvmTargetTriple phase0LLVMModule
          , "layout:" <> llvmDataLayout phase0LLVMModule
          , "runtime-abi:" <> unDigest (llvmRuntimeABIDigest phase0LLVMModule)
          , "runtime-abi-profile:" <> llvmRuntimeABIProfile phase0LLVMModule
          , "compilation-profile:" <> phase0LLVMSourceCompilationProfile
          ]
      , revisionAcceptanceRule = AcceptEntry
          TranslationValidated
          (EvidenceRole "translation_validated")
      , revisionGeneratedFrom = []
      }

phase0LLVMTranslationValidationEvidence :: EvidenceEntry
phase0LLVMTranslationValidationEvidence = provisional
  { evidenceEntryDigest = deriveEvidenceEntryDigest provisional }
  where
    provisional = EvidenceEntry
      { evidenceEntryId = translationValidationEvidenceId
      , evidenceEntryDigest = Digest ""
      , evidenceObligationRevision = certificationRevisionId
      , evidenceAssuranceKind = TranslationValidated
      , evidenceRole = EvidenceRole "translation_validated"
      , evidenceProducer = "Phil.LLVM.Verify.verifyLLVMEmission"
      , evidenceChecker = "Phil.Assurance.Verify.verifyManifest"
      , evidenceArtifact = Just phase0LLVMTranslationValidationArtifact
      , evidenceInputDigests =
          [ phase0LLVMCertifiedSourceDigest
          , phase0LLVMCertifiedTargetDigest
          , phase0LLVMCertifiedTextDigest
          , llvmRuntimeABIDigest phase0LLVMModule
          ]
      , evidenceAssumptions = []
      , evidenceDependsOn = []
      , evidenceValidityScope = phase0LLVMCertificationEvidenceScope
      , evidenceResult = EvidenceAccepted
      , evidenceJustifies =
          [ "PHIL-LLVM-ID-001"
          , "PHIL-LLVM-PRESERVE-001"
          , "PHIL-LLVM-STRENGTH-001"
          , "PHIL-ASSURE-SCOPE-001"
          , "PHIL-ASSURE-EVID-001"
          ]
      , evidenceRuntimeMechanism = Nothing
      , evidenceRuntimeResidue = []
      , evidenceCostRefs = []
      }

phase0LLVMCertificationEvidenceScope :: ValidityScope
phase0LLVMCertificationEvidenceScope = ValidityScope $
  Map.insert "target" phase0LLVMCertificationTarget $
  Map.insert "compilation_profile" phase0LLVMCertificationProfile $
  phase0LLVMCertificationValidityContext

phase0LLVMCertificationValidityContext :: Map.Map Text Text
phase0LLVMCertificationValidityContext = Map.fromList
  [ ("source_digest", unDigest phase0LLVMCertifiedSourceDigest)
  , ("target_digest", unDigest phase0LLVMCertifiedTargetDigest)
  , ("target_text_digest", unDigest phase0LLVMCertifiedTextDigest)
  , ("llvm_language", llvmLanguageVersion phase0LLVMModule)
  , ("llvm_tool_profile", llvmToolVersion phase0LLVMModule)
  , ("target_triple", llvmTargetTriple phase0LLVMModule)
  , ("data_layout", llvmDataLayout phase0LLVMModule)
  , ("runtime_abi_digest", unDigest (llvmRuntimeABIDigest phase0LLVMModule))
  , ("runtime_abi_profile", llvmRuntimeABIProfile phase0LLVMModule)
  , ("systems_compilation_profile", phase0LLVMSourceCompilationProfile)
  , ("external_llvm_gate", "canonical target text must be accepted by an LLVM 18 assembler in CI")
  ]

phase0LLVMCertificationTarget :: Text
phase0LLVMCertificationTarget =
  "preopt-llvm:" <> llvmTargetTriple phase0LLVMModule

phase0LLVMCertificationProfile :: Text
phase0LLVMCertificationProfile =
  "translation-validation/" <> phase0LLVMSourceCompilationProfile

phase0LLVMCertificationRoot :: Digest
phase0LLVMCertificationRoot = digestText $ Text.intercalate "|"
  [ "phil-llvm-phase0-certification-root-v1"
  , unDigest phase0LLVMCertifiedSourceDigest
  , unDigest phase0LLVMCertifiedTargetDigest
  , unDigest phase0LLVMCertifiedTextDigest
  ]

phase0LLVMTranslationValidationRecord :: Text
phase0LLVMTranslationValidationRecord = Text.unlines
  [ "phil-llvm-phase0-translation-validation-v1"
  , "source-digest=" <> unDigest phase0LLVMCertifiedSourceDigest
  , "target-digest=" <> unDigest phase0LLVMCertifiedTargetDigest
  , "target-text-digest=" <> unDigest phase0LLVMCertifiedTextDigest
  , "llvm-language=" <> llvmLanguageVersion phase0LLVMModule
  , "llvm-tool-profile=" <> llvmToolVersion phase0LLVMModule
  , "target-triple=" <> llvmTargetTriple phase0LLVMModule
  , "data-layout=" <> llvmDataLayout phase0LLVMModule
  , "runtime-abi-digest=" <> unDigest (llvmRuntimeABIDigest phase0LLVMModule)
  , "runtime-abi-profile=" <> llvmRuntimeABIProfile phase0LLVMModule
  , "systems-compilation-profile=" <> phase0LLVMSourceCompilationProfile
  , "translation-validator=Phil.LLVM.Verify.verifyLLVMEmission"
  , "assurance-checker=Phil.Assurance.Verify.verifyManifest"
  ]

phase0LLVMModule :: LLVMModule
phase0LLVMModule = llvmArtifactModule phase0LLVMArtifact

phase0LLVMCertifiedSourceDigest :: Digest
phase0LLVMCertifiedSourceDigest =
  llvmContractSourceDigest (llvmArtifactContract phase0LLVMArtifact)

phase0LLVMCertifiedTargetDigest :: Digest
phase0LLVMCertifiedTargetDigest =
  llvmContractTargetDigest (llvmArtifactContract phase0LLVMArtifact)

phase0LLVMCertifiedTextDigest :: Digest
phase0LLVMCertifiedTextDigest = digestText (llvmArtifactText phase0LLVMArtifact)

phase0LLVMSourceCompilationProfile :: Text
phase0LLVMSourceCompilationProfile =
  Text.pack (show (llvmCompilationProfile phase0LLVMModule))

certificationRevisionId :: RevisionId
certificationRevisionId = revisionId phase0LLVMCertificationRevision

translationValidationEvidenceId :: EvidenceEntryId
translationValidationEvidenceId =
  EvidenceEntryId "evidence.llvm.phase0.translation.validated"

mapLeft :: (left -> right) -> Either left value -> Either right value
mapLeft wrap = either (Left . wrap) Right
