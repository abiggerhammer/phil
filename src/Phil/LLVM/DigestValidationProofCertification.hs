{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.DigestValidationProofCertification
  ( DigestValidationProofCertificationError (..)
  , DigestValidationProofCertificationBundle (..)
  , phase0DigestValidationProofCertification
  , verifyPhase0DigestValidationProofCertification
  , renderDigestValidationProofCertification
  ) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Rocq
import Phil.Assurance.RocqDigestValidation
import Phil.Assurance.RocqExactReceive
import Phil.Assurance.RocqRecognizedRecord
import Phil.Assurance.Types
import Phil.Assurance.Verify (ManifestError, verifyManifest)
import Phil.Core.Syntax (ObligationId (..))
import Phil.LLVM.DigestValidationCertification
import Phil.LLVM.ExactReceiveProofCertification
import Phil.LLVM.IR
import Phil.Systems.DigestValidation
import Phil.Systems.IR
import Phil.Systems.Verify (SystemsVerificationContext (..))

data DigestValidationProofCertificationError
  = DigestValidationProofCertificationBaseError DigestValidationCertificationError
  | DigestValidationProofCertificationPredecessorError ExactReceiveProofCertificationError
  | DigestValidationProofCertificationWrongProof Text ObligationId ObligationId
  | DigestValidationProofCertificationProofManifestError Text ManifestError
  | DigestValidationProofCertificationManifestError ManifestError
  deriving (Eq, Show)

data DigestValidationProofCertificationBundle = DigestValidationProofCertificationBundle
  { digestValidationProofCertificationBase :: DigestValidationCertificationBundle
  , digestValidationProofCertificationPredecessor :: ExactReceiveProofCertificationBundle
  , digestValidationProofCertificationArtifact :: ArtifactIdentity
  , digestValidationProofCertificationRecord :: Text
  , digestValidationProofCertificationLedger :: AssuranceLedger
  , digestValidationProofCertificationManifest :: AssuranceManifest
  , digestValidationProofCertificationContext :: VerificationContext
  }
  deriving (Eq, Show)

phase0DigestValidationProofCertification
  :: RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> Either DigestValidationProofCertificationError DigestValidationProofCertificationBundle
phase0DigestValidationProofCertification
    systemsDigestProof llvmDigestProof systemsRecordProof exactProof abiProof symbolProof = do
  verifyProof "systems-digest-validation" systemsDigestValidationCertificationSpec systemsDigestProof
  verifyProof "llvm-digest-validation" llvmDigestValidationCertificationSpec llvmDigestProof
  verifyProof "systems-recognized-record" systemsRecognizedRecordCertificationSpec systemsRecordProof
  verifyProof "llvm-exact-receive" llvmExactReceiveCertificationSpec exactProof
  verifyProof "llvm-recognized-record-abi" llvmRecognizedRecordABICertificationSpec abiProof
  verifyProof "llvm-runtime-symbol-identity" llvmRuntimeSymbolCertificationSpec symbolProof

  -- Reproduce the proof-bound predecessor certificate from the same exact proof
  -- inputs, but do not import its translation evidence into this manifest. The
  -- predecessor evidence is scoped to transport-exact-receive-v1, whereas this
  -- certification is scoped to digest-validation-v1. Its exact certificate
  -- digest is content-bound below while compatible proof authorities are
  -- selected directly.
  predecessor <- mapLeft DigestValidationProofCertificationPredecessorError $
    phase0ExactReceiveProofCertification exactProof abiProof symbolProof
  base <- mapLeft DigestValidationProofCertificationBaseError
    phase0DigestValidationLLVMCertification

  let explicitProofBundles =
        [ systemsDigestProof
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
      predecessorArtifact = exactReceiveProofCertificationArtifact predecessor

      systemsBundle = digestValidationCertificationSystems base
      systemsArtifact = digestValidationArtifact systemsBundle
      systemsManifest = systemsAssuranceManifest (digestValidationContext systemsBundle)
      llvmArtifact = digestValidationCertificationLLVM base
      moduleValue = llvmArtifactModule llvmArtifact
      translationArtifact = digestValidationCertificationArtifact base
      sourceDigest = llvmContractSourceDigest (llvmArtifactContract llvmArtifact)
      targetDigest = llvmContractTargetDigest (llvmArtifactContract llvmArtifact)
      targetTextDigest = digestText (llvmArtifactText llvmArtifact)
      abiDigest = llvmRuntimeABIDigest moduleValue
      systemsLoweringRoot = loweringLedgerRoot (systemsArtifactLoweringLedger systemsArtifact)
      certificationTarget = "preopt-llvm:" <> llvmTargetTriple moduleValue
      sourceCompilationProfile = Text.pack (show (llvmCompilationProfile moduleValue))
      certificationProfile =
        "translation-validation/" <> sourceCompilationProfile <> "/digest-validation-v1/proof-bound"
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
        , ("digest_subjects", "exact recognized Begin + exact BorrowedSlice(payload), in source order")
        , ("borrow_representation", "verified BorrowedSlice(owner) -> same owner ptr, no copy")
        , ("digest_abi", "phil_runtime_digest_validate(ptr,ptr)->i1")
        , ("digest_mechanism", "SHA-256 selected and content-bound in ABI identity")
        , ("predecessor_certification", unDigest (artifactDigest predecessorArtifact))
        , ("proof_assistant", "Rocq")
        , ("rocq_version", "9.2.0")
        , ("certificate_profile", "proof-assistant-theorem/v1")
        , ("external_llvm_gate", "canonical target text must be accepted by LLVM 18 in CI")
        , ("external_runtime_abi_gate", "provider signature conformance must pass independently in CI")
        , ("external_sha256_gate", "libcrypto SHA-256 standard-vector match and mismatch execution must pass independently in CI")
        ]
      evidenceScope = ValidityScope $
        Map.insert "target" certificationTarget $
        Map.insert "compilation_profile" certificationProfile validityContext
      revisionStatement =
        "The digest-validation-v1 Systems -> canonical pre-optimization LLVM pair may be labeled Certified only when its exact source/target/text digests, lowering root, target/runtime-ABI/tool identities, exact Systems digest-subject/borrow proof, exact LLVM digest-lowering proof, exact-receive, recognized-record, and runtime-symbol proof authorities, and translation-validation result are content-bound; the proof-bound CERT-003 predecessor is exactly reproducible from the selected predecessor proofs and its certificate digest is bound without importing evidence outside its validity scope; SHA-256 is selected by ABI identity while LLVM 18, provider ABI conformance, and concrete libcrypto SHA-256 match/mismatch execution remain explicit external gates; and the assurance manifest closes over all selected evidence."
      provisionalRevision = ObligationRevision
        { revisionObligationId = ObligationId "PHIL-LLVM-CERT-004"
        , revisionId = RevisionId ""
        , revisionStatement = revisionStatement
        , revisionStatementDigest = digestText revisionStatement
        , revisionKind = "LLVMDigestValidationProofBoundCertification"
        , revisionOrigin = "digest validation ABI v1 / proof-bound PHIL-LLVM-CERT-004"
        , revisionScope = "llvm.phase0.preopt.digest-validation.proof-bound"
        , revisionRequiredAt = "certification"
        , revisionRepresentation =
            "digest-subject SystemsArtifact -> operand-explicit canonical pre-optimization LLVMArtifact + proof authority"
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
        "evidence.llvm.phase0.digest-validation.proof-bound.translation.validated"
      provisionalTranslationEvidence = EvidenceEntry
        { evidenceEntryId = translationEvidenceId
        , evidenceEntryDigest = Digest ""
        , evidenceObligationRevision = certificationRevisionId
        , evidenceAssuranceKind = TranslationValidated
        , evidenceRole = EvidenceRole "translation_validated"
        , evidenceProducer = "Phil.LLVM.DigestValidation.verifyDigestValidationTranslation"
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
            [ "exact recognized Begin semantic subject"
            , "exact payload BorrowedSlice -> exact receive owner relation"
            , "exact two-operand digest order"
            , "exact digest success/failure edges"
            , "no-copy borrow-view representation erasure"
            , "SHA-256 selected in runtime ABI identity"
            , "absence of ambient digest subject recovery"
            , "physical runtime symbol identity"
            , "content-bound reproduction of proof-bound predecessor authority"
            ]
        , evidenceRuntimeMechanism = Nothing
        , evidenceRuntimeResidue = []
        , evidenceCostRefs = []
        }
      translationEvidence = provisionalTranslationEvidence
        { evidenceEntryDigest = deriveEvidenceEntryDigest provisionalTranslationEvidence }
      certificationRecord = Text.unlines $
        [ "phil-llvm-phase0-digest-validation-certification/v1"
        , "obligation=PHIL-LLVM-CERT-004"
        , "revision=" <> unRevisionId certificationRevisionId
        , "source-digest=" <> unDigest sourceDigest
        , "systems-lowering-root=" <> unDigest systemsLoweringRoot
        , "target-digest=" <> unDigest targetDigest
        , "target-text-digest=" <> unDigest targetTextDigest
        , "runtime-abi-profile=" <> llvmRuntimeABIProfile moduleValue
        , "runtime-abi-digest=" <> unDigest abiDigest
        , "translation-artifact=" <> renderArtifact translationArtifact
        , "predecessor-certification=" <> renderArtifact predecessorArtifact
        ] <> map renderProofArtifact explicitProofBundles <>
        [ "external-llvm-gate=LLVM 18 assembler acceptance required"
        , "external-runtime-abi-gate=provider signature conformance required"
        , "external-sha256-gate=libcrypto SHA-256 standard-vector match/mismatch execution required"
        ]
      certificationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef "certificate:phil:llvm:PHIL-LLVM-CERT-004:v1"
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
        [ "phil-llvm-phase0-digest-validation-proof-bound-certification-root-v1"
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
      bundle = DigestValidationProofCertificationBundle
        { digestValidationProofCertificationBase = base
        , digestValidationProofCertificationPredecessor = predecessor
        , digestValidationProofCertificationArtifact = certificationArtifact
        , digestValidationProofCertificationRecord = certificationRecord
        , digestValidationProofCertificationLedger = ledger
        , digestValidationProofCertificationManifest = manifest
        , digestValidationProofCertificationContext = verificationContext
        }

  mapLeft DigestValidationProofCertificationManifestError $
    verifyManifest verificationContext ledger manifest
  pure bundle

verifyPhase0DigestValidationProofCertification
  :: RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> Either DigestValidationProofCertificationError ()
verifyPhase0DigestValidationProofCertification
    systemsDigestProof llvmDigestProof systemsRecordProof exactProof abiProof symbolProof = do
  bundle <- phase0DigestValidationProofCertification
    systemsDigestProof llvmDigestProof systemsRecordProof exactProof abiProof symbolProof
  mapLeft DigestValidationProofCertificationManifestError $
    verifyManifest
      (digestValidationProofCertificationContext bundle)
      (digestValidationProofCertificationLedger bundle)
      (digestValidationProofCertificationManifest bundle)

renderDigestValidationProofCertification
  :: DigestValidationProofCertificationBundle
  -> Text
renderDigestValidationProofCertification = digestValidationProofCertificationRecord

verifyProof
  :: Text
  -> RocqCertificationSpec
  -> RocqCertificationBundle
  -> Either DigestValidationProofCertificationError ()
verifyProof label spec bundle = do
  let expected = rocqSpecObligation spec
      actual = rocqCertificateObligation (rocqBundleCertificate bundle)
  unless (actual == expected) $
    Left (DigestValidationProofCertificationWrongProof label expected actual)
  mapLeft (DigestValidationProofCertificationProofManifestError label) $
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
