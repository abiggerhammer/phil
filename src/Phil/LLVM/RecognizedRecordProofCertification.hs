{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.RecognizedRecordProofCertification
  ( RecognizedRecordProofCertificationError (..)
  , RecognizedRecordProofCertificationBundle (..)
  , phase0RecognizedRecordProofCertification
  , verifyPhase0RecognizedRecordProofCertification
  , renderRecognizedRecordProofCertification
  ) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Rocq
import Phil.Assurance.RocqRecognizedRecord
import Phil.Assurance.Types
import Phil.Assurance.Verify (ManifestError, verifyManifest)
import Phil.Core.Syntax (ObligationId (..))
import Phil.LLVM.IR
import Phil.LLVM.RecognizedRecordCertification
import Phil.Systems.IR
import Phil.Systems.RecognizedRecord
import Phil.Systems.Verify (SystemsVerificationContext (..))

data RecognizedRecordProofCertificationError
  = RecognizedRecordProofCertificationBaseError RecognizedRecordCertificationError
  | RecognizedRecordProofCertificationWrongProof Text ObligationId ObligationId
  | RecognizedRecordProofCertificationProofManifestError Text ManifestError
  | RecognizedRecordProofCertificationManifestError ManifestError
  deriving (Eq, Show)

data RecognizedRecordProofCertificationBundle = RecognizedRecordProofCertificationBundle
  { recognizedRecordProofCertificationBase :: RecognizedRecordCertificationBundle
  , recognizedRecordProofCertificationArtifact :: ArtifactIdentity
  , recognizedRecordProofCertificationRecord :: Text
  , recognizedRecordProofCertificationLedger :: AssuranceLedger
  , recognizedRecordProofCertificationManifest :: AssuranceManifest
  , recognizedRecordProofCertificationContext :: VerificationContext
  }
  deriving (Eq, Show)

phase0RecognizedRecordProofCertification
  :: RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> Either RecognizedRecordProofCertificationError RecognizedRecordProofCertificationBundle
phase0RecognizedRecordProofCertification systemsProof abiProof symbolProof = do
  verifyProof "systems-recognized-record" systemsRecognizedRecordCertificationSpec systemsProof
  verifyProof "llvm-recognized-record-abi" llvmRecognizedRecordABICertificationSpec abiProof
  verifyProof "llvm-runtime-symbol-identity" llvmRuntimeSymbolCertificationSpec symbolProof

  base <- mapLeft RecognizedRecordProofCertificationBaseError
    phase0RecognizedRecordLLVMCertification

  let proofBundles = [systemsProof, abiProof, symbolProof]
      proofLedgers = map rocqBundleLedger proofBundles
      proofRevisions = Map.unions (map ledgerRevisions proofLedgers)
      proofEvidence = Map.unions (map ledgerEvidence proofLedgers)
      proofRevisionIds = Map.keysSet proofRevisions
      proofEvidenceIds = Map.keysSet proofEvidence
      proofArtifacts = map rocqBundleCertificateArtifact proofBundles
      proofDigests = map artifactDigest proofArtifacts

      systemsBundle = recognizedRecordCertificationSystems base
      systemsArtifact = recognizedRecordArtifact systemsBundle
      systemsManifest = systemsAssuranceManifest (recognizedRecordContext systemsBundle)
      llvmArtifact = recognizedRecordCertificationLLVM base
      moduleValue = llvmArtifactModule llvmArtifact
      translationArtifact = recognizedRecordCertificationArtifact base
      sourceDigest = llvmContractSourceDigest (llvmArtifactContract llvmArtifact)
      targetDigest = llvmContractTargetDigest (llvmArtifactContract llvmArtifact)
      targetTextDigest = digestText (llvmArtifactText llvmArtifact)
      abiDigest = llvmRuntimeABIDigest moduleValue
      systemsLoweringRoot = loweringLedgerRoot (systemsArtifactLoweringLedger systemsArtifact)
      certificationTarget = "preopt-llvm:" <> llvmTargetTriple moduleValue
      sourceCompilationProfile = Text.pack (show (llvmCompilationProfile moduleValue))
      certificationProfile =
        "translation-validation/" <> sourceCompilationProfile <> "/recognized-record-v1/proof-bound"
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
        , ("recognized_record_abi", "{i8,ptr}; status==1; opaque ptr; typed accessor")
        , ("runtime_symbol_identity", "physical primitive/signature")
        , ("exact_receive_dependency", "Begin.length:i64 -> receive_exact_u64(i64)")
        , ("proof_assistant", "Rocq")
        , ("rocq_version", "9.2.0")
        , ("certificate_profile", "proof-assistant-theorem/v1")
        , ("external_llvm_gate", "canonical target text must be accepted by an LLVM 18 assembler in CI")
        ]
      evidenceScope = ValidityScope $
        Map.insert "target" certificationTarget $
        Map.insert "compilation_profile" certificationProfile validityContext
      revisionStatement =
        "The recognized-record ABI v1 Systems -> canonical pre-optimization LLVM pair may be labeled Certified only when its exact source/target digests, lowering-ledger root, target/runtime-ABI/tool identities, semantic proof evidence, and runtime-symbol-separation evidence are bound; the recognized-record translation validator accepts that exact pair; LLVM 18 accepts the exact canonical target text; and an ADR-010 manifest selects the resulting TranslationValidated/ProofAssistantTheorem evidence with a closed certification scope."
      provisionalRevision = ObligationRevision
        { revisionObligationId = ObligationId "PHIL-LLVM-CERT-002"
        , revisionId = RevisionId ""
        , revisionStatement = revisionStatement
        , revisionStatementDigest = digestText revisionStatement
        , revisionKind = "LLVMRecognizedRecordProofBoundCertification"
        , revisionOrigin = "recognized-record ABI v1 / proof-bound PHIL-LLVM-CERT-002"
        , revisionScope = "llvm.phase0.preopt.recognized-record.proof-bound"
        , revisionRequiredAt = "certification"
        , revisionRepresentation =
            "recognized-record SystemsArtifact -> canonical pre-optimization LLVMArtifact + proof certificates"
        , revisionSubjectIds =
            [ "systems:" <> unDigest sourceDigest
            , "systems-lowering-root:" <> unDigest systemsLoweringRoot
            , "llvm:" <> unDigest targetDigest
            , "llvm-text:" <> unDigest targetTextDigest
            , "runtime-abi:" <> unDigest abiDigest
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
        , revisionGeneratedFrom = Set.toAscList proofRevisionIds
        }
      certificationRevision = provisionalRevision
        { revisionId = deriveRevisionId provisionalRevision }
      certificationRevisionId = revisionId certificationRevision
      translationEvidenceId = EvidenceEntryId
        "evidence.llvm.phase0.recognized-record.proof-bound.translation.validated"
      provisionalTranslationEvidence = EvidenceEntry
        { evidenceEntryId = translationEvidenceId
        , evidenceEntryDigest = Digest ""
        , evidenceObligationRevision = certificationRevisionId
        , evidenceAssuranceKind = TranslationValidated
        , evidenceRole = EvidenceRole "translation_validated"
        , evidenceProducer = "Phil.LLVM.RecognizedRecord.verifyRecognizedRecordTranslation"
        , evidenceChecker = "Phil.Assurance.Verify.verifyManifest"
        , evidenceArtifact = Just translationArtifact
        , evidenceInputDigests =
            [ sourceDigest
            , targetDigest
            , targetTextDigest
            , abiDigest
            , systemsLoweringRoot
            ]
        , evidenceAssumptions = []
        , evidenceDependsOn = map DependsOnObligation (Set.toAscList proofRevisionIds)
        , evidenceValidityScope = evidenceScope
        , evidenceResult = EvidenceAccepted
        , evidenceJustifies =
            [ "exact recognized-record identity"
            , "exact Begin.length field identity and i64 width"
            , "exact receive consumes projected scalar"
            , "fail-closed recognition status"
            , "physical runtime symbol identity"
            , "proof-bound semantic authority"
            ]
        , evidenceRuntimeMechanism = Nothing
        , evidenceRuntimeResidue = []
        , evidenceCostRefs = []
        }
      translationEvidence = provisionalTranslationEvidence
        { evidenceEntryDigest = deriveEvidenceEntryDigest provisionalTranslationEvidence }
      certificationRecord = Text.unlines $
        [ "phil-llvm-phase0-recognized-record-certification/v1"
        , "obligation=PHIL-LLVM-CERT-002"
        , "revision=" <> unRevisionId certificationRevisionId
        , "source-digest=" <> unDigest sourceDigest
        , "systems-lowering-root=" <> unDigest systemsLoweringRoot
        , "target-digest=" <> unDigest targetDigest
        , "target-text-digest=" <> unDigest targetTextDigest
        , "runtime-abi-profile=" <> llvmRuntimeABIProfile moduleValue
        , "runtime-abi-digest=" <> unDigest abiDigest
        , "translation-artifact=" <> renderArtifact translationArtifact
        ] <> map renderProofArtifact proofBundles <>
        [ "external-llvm-gate=LLVM 18 assembler acceptance required"
        ]
      certificationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef "certificate:phil:llvm:PHIL-LLVM-CERT-002:v1"
        , artifactDigest = digestText certificationRecord
        }
      revisions = Map.insert certificationRevisionId certificationRevision proofRevisions
      evidence = Map.insert translationEvidenceId translationEvidence proofEvidence
      ledger = emptyLedger
        { ledgerRevisions = revisions
        , ledgerEvidence = evidence
        }
      obligationIds = Set.insert certificationRevisionId proofRevisionIds
      evidenceIds = Set.insert translationEvidenceId proofEvidenceIds
      certificationRoot = digestText $ Text.intercalate "|" $
        [ "phil-llvm-phase0-recognized-record-proof-bound-certification-root-v1"
        , unDigest sourceDigest
        , unDigest systemsLoweringRoot
        , unDigest targetDigest
        , unDigest targetTextDigest
        , unDigest abiDigest
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
      availableArtifacts = Map.fromList
        [ (artifactReference artifact, artifactDigest artifact)
        | artifact <- translationArtifact : certificationArtifact : proofArtifacts
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
      bundle = RecognizedRecordProofCertificationBundle
        { recognizedRecordProofCertificationBase = base
        , recognizedRecordProofCertificationArtifact = certificationArtifact
        , recognizedRecordProofCertificationRecord = certificationRecord
        , recognizedRecordProofCertificationLedger = ledger
        , recognizedRecordProofCertificationManifest = manifest
        , recognizedRecordProofCertificationContext = verificationContext
        }

  mapLeft RecognizedRecordProofCertificationManifestError $
    verifyManifest verificationContext ledger manifest
  pure bundle

verifyPhase0RecognizedRecordProofCertification
  :: RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> Either RecognizedRecordProofCertificationError ()
verifyPhase0RecognizedRecordProofCertification systemsProof abiProof symbolProof = do
  bundle <- phase0RecognizedRecordProofCertification systemsProof abiProof symbolProof
  mapLeft RecognizedRecordProofCertificationManifestError $
    verifyManifest
      (recognizedRecordProofCertificationContext bundle)
      (recognizedRecordProofCertificationLedger bundle)
      (recognizedRecordProofCertificationManifest bundle)

renderRecognizedRecordProofCertification
  :: RecognizedRecordProofCertificationBundle
  -> Text
renderRecognizedRecordProofCertification = recognizedRecordProofCertificationRecord

verifyProof
  :: Text
  -> RocqCertificationSpec
  -> RocqCertificationBundle
  -> Either RecognizedRecordProofCertificationError ()
verifyProof label spec bundle = do
  let expected = rocqSpecObligation spec
      actual = rocqCertificateObligation (rocqBundleCertificate bundle)
  unless (actual == expected) $
    Left (RecognizedRecordProofCertificationWrongProof label expected actual)
  mapLeft (RecognizedRecordProofCertificationProofManifestError label) $
    verifyManifest
      (rocqBundleVerificationContext bundle)
      (rocqBundleLedger bundle)
      (rocqBundleManifest bundle)

renderArtifact :: ArtifactIdentity -> Text
renderArtifact artifact =
  unArtifactRef (artifactReference artifact) <> ";sha256=" <> unDigest (artifactDigest artifact)

renderProofArtifact :: RocqCertificationBundle -> Text
renderProofArtifact bundle =
  let certificate = rocqBundleCertificate bundle
      artifact = rocqBundleCertificateArtifact bundle
  in "proof=" <> unObligationId (rocqCertificateObligation certificate)
      <> ";artifact=" <> unArtifactRef (artifactReference artifact)
      <> ";sha256=" <> unDigest (artifactDigest artifact)

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
