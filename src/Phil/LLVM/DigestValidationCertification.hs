{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.DigestValidationCertification
  ( DigestValidationCertificationError (..)
  , DigestValidationCertificationBundle (..)
  , phase0DigestValidationLLVMCertification
  , verifyPhase0DigestValidationLLVMCertification
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Assurance.Types
import Phil.Assurance.Verify (ManifestError, verifyManifest)
import Phil.Core.Syntax (ObligationId (..))
import Phil.LLVM.DigestValidation
import Phil.LLVM.IR
import Phil.LLVM.Lower (lowerSystemsDigestValidation)
import Phil.Systems.DigestValidation
import Phil.Systems.Verify (SystemsVerificationContext (..))

data DigestValidationCertificationError
  = DigestValidationCertificationSystemsError DigestValidationError
  | DigestValidationCertificationTranslationError DigestValidationLLVMError
  | DigestValidationCertificationManifestError ManifestError
  deriving (Eq, Show)

data DigestValidationCertificationBundle = DigestValidationCertificationBundle
  { digestValidationCertificationSystems :: DigestValidationBundle
  , digestValidationCertificationLLVM :: LLVMArtifact
  , digestValidationCertificationArtifact :: ArtifactIdentity
  , digestValidationCertificationLedger :: AssuranceLedger
  , digestValidationCertificationManifest :: AssuranceManifest
  , digestValidationCertificationContext :: VerificationContext
  }
  deriving (Eq, Show)

-- PHIL-LLVM-CERT-004
--
-- This certification is content-bound to the digest-validation-v1 candidate.
-- PHIL-LLVM-CERT-003 remains bound to transport-exact-receive-v1.  Runtime
-- provider signature checking, LLVM 18 acceptance, libcrypto SHA-256 behavior,
-- linking, and executable smoke evidence remain independent external gates.
phase0DigestValidationLLVMCertification
  :: Either DigestValidationCertificationError DigestValidationCertificationBundle
phase0DigestValidationLLVMCertification = do
  systemsBundle <- mapLeft
    DigestValidationCertificationSystemsError
    phase0DigestValidationBundle
  let systemsArtifact = digestValidationArtifact systemsBundle
      llvmArtifact = lowerSystemsDigestValidation
        phase0DigestValidationLLVMTarget
        systemsArtifact
  mapLeft DigestValidationCertificationTranslationError $
    verifyDigestValidationTranslation systemsBundle llvmArtifact
  let systemsManifest = systemsAssuranceManifest (digestValidationContext systemsBundle)
      moduleValue = llvmArtifactModule llvmArtifact
      sourceDigest = llvmContractSourceDigest (llvmArtifactContract llvmArtifact)
      targetDigest = llvmContractTargetDigest (llvmArtifactContract llvmArtifact)
      targetTextDigest = digestText (llvmArtifactText llvmArtifact)
      abiDigest = llvmRuntimeABIDigest moduleValue
      certificationTarget = "preopt-llvm:" <> llvmTargetTriple moduleValue
      sourceCompilationProfile = Text.pack (show (llvmCompilationProfile moduleValue))
      certificationProfile =
        "translation-validation/" <> sourceCompilationProfile <> "/digest-validation-v1"
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
        , ("recognized_record_abi", "recognition result -> exact opaque Begin record ptr")
        , ("exact_receive_dependency", "transport:ptr, Begin.length:i64 -> exact payload owner ptr")
        , ("payload_owner_identity", "Systems server.payload -> deterministic server.payload.owner SSA")
        , ("digest_subjects", "Systems server.begin + server.payload_view")
        , ("borrow_representation", "BorrowedSlice(server.payload) -> same payload-owner ptr, no copy")
        , ("digest_abi", "phil_runtime_digest_validate(ptr,ptr)->i1")
        , ("digest_operand_order", "recognized Begin ptr, payload borrow-owner ptr")
        , ("digest_mechanism", "SHA-256 implementation is an external runtime assumption/evidence boundary")
        , ("runtime_symbol_identity", "physical primitive/signature")
        , ("ambient_digest_state", "forbidden")
        , ("external_runtime_gate", "provider signatures and SHA-256 match/mismatch execution are checked independently in CI")
        , ("external_llvm_gate", "canonical target text must be accepted by LLVM 18 in CI")
        ]
      evidenceScope = ValidityScope $
        Map.insert "target" certificationTarget $
        Map.insert "compilation_profile" certificationProfile $
        validityContext
      revisionStatement =
        "The canonical Phase 0 digest-subject Systems -> pre-optimization LLVM pair is certified only for the exact source, target, target text, target profile, and phil-runtime/phase0/digest-validation-v1 ABI bound by this revision; independent Phil translation validation establishes the exact recognized Begin and borrowed payload subject relation, while runtime-provider conformance, SHA-256 implementation behavior, LLVM 18 acceptance, linking, and execution remain external certification gates."
      provisionalRevision = ObligationRevision
        { revisionObligationId = ObligationId "PHIL-LLVM-CERT-004"
        , revisionId = RevisionId ""
        , revisionStatement = revisionStatement
        , revisionStatementDigest = digestText revisionStatement
        , revisionKind = "LLVMDigestValidationTranslationCertification"
        , revisionOrigin = "digest validation ABI v1 / PHIL-LLVM-CERT-004"
        , revisionScope = "llvm.phase0.preopt.digest-validation.translation"
        , revisionRequiredAt = "certification"
        , revisionRepresentation =
            "digest-subject SystemsArtifact -> operand-explicit canonical pre-optimization LLVMArtifact"
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
        [ "phil-llvm-phase0-digest-validation-translation-validation-v1"
        , "source-digest=" <> unDigest sourceDigest
        , "target-digest=" <> unDigest targetDigest
        , "target-text-digest=" <> unDigest targetTextDigest
        , "llvm-language=" <> llvmLanguageVersion moduleValue
        , "llvm-tool-profile=" <> llvmToolVersion moduleValue
        , "target-triple=" <> llvmTargetTriple moduleValue
        , "data-layout=" <> llvmDataLayout moduleValue
        , "runtime-abi-digest=" <> unDigest abiDigest
        , "runtime-abi-profile=" <> llvmRuntimeABIProfile moduleValue
        , "translation-validator=Phil.LLVM.DigestValidation.verifyDigestValidationTranslation"
        , "assurance-checker=Phil.Assurance.Verify.verifyManifest"
        ]
      translationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef
            "artifact:phil:llvm:phase0:digest-validation:translation-validation:v1"
        , artifactDigest = digestText translationArtifactRecord
        }
      evidenceId = EvidenceEntryId
        "evidence.llvm.phase0.digest-validation.translation.validated"
      provisionalEvidence = EvidenceEntry
        { evidenceEntryId = evidenceId
        , evidenceEntryDigest = Digest ""
        , evidenceObligationRevision = certificationRevisionId
        , evidenceAssuranceKind = TranslationValidated
        , evidenceRole = EvidenceRole "translation_validated"
        , evidenceProducer =
            "Phil.LLVM.DigestValidation.verifyDigestValidationTranslation"
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
            , "exact receive payload-owner identity"
            , "exact payload-view borrow-owner identity"
            , "exact two-subject digest operand order"
            , "exact digest success/failure edges"
            , "representation-free borrow lowering without ambient digest state"
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
        [ "phil-llvm-phase0-digest-validation-certification-root-v1"
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
  pure DigestValidationCertificationBundle
    { digestValidationCertificationSystems = systemsBundle
    , digestValidationCertificationLLVM = llvmArtifact
    , digestValidationCertificationArtifact = translationArtifact
    , digestValidationCertificationLedger = ledger
    , digestValidationCertificationManifest = manifest
    , digestValidationCertificationContext = verificationContext
    }

verifyPhase0DigestValidationLLVMCertification
  :: Either DigestValidationCertificationError ()
verifyPhase0DigestValidationLLVMCertification = do
  bundle <- phase0DigestValidationLLVMCertification
  mapLeft DigestValidationCertificationManifestError $
    verifyManifest
      (digestValidationCertificationContext bundle)
      (digestValidationCertificationLedger bundle)
      (digestValidationCertificationManifest bundle)

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
