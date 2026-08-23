{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.HelloPolicyValidationCertification
  ( HelloPolicyValidationCertificationError (..)
  , HelloPolicyValidationCertificationBundle (..)
  , phase0HelloPolicyValidationLLVMCertification
  , verifyPhase0HelloPolicyValidationLLVMCertification
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Assurance.Types
import Phil.Assurance.Verify (ManifestError, verifyManifest)
import Phil.Core.Syntax (ObligationId (..))
import Phil.LLVM.HelloPolicyValidation
import Phil.LLVM.IR
import Phil.Systems.HelloPolicyValidation
import Phil.Systems.Verify (SystemsVerificationContext (..))

data HelloPolicyValidationCertificationError
  = HelloPolicyValidationCertificationSystemsError HelloPolicyValidationError
  | HelloPolicyValidationCertificationTranslationError HelloPolicyValidationLLVMError
  | HelloPolicyValidationCertificationManifestError ManifestError
  deriving (Eq, Show)

data HelloPolicyValidationCertificationBundle = HelloPolicyValidationCertificationBundle
  { helloPolicyValidationCertificationSystems :: HelloPolicyValidationBundle
  , helloPolicyValidationCertificationLLVM :: LLVMArtifact
  , helloPolicyValidationCertificationArtifact :: ArtifactIdentity
  , helloPolicyValidationCertificationLedger :: AssuranceLedger
  , helloPolicyValidationCertificationManifest :: AssuranceManifest
  , helloPolicyValidationCertificationContext :: VerificationContext
  }
  deriving (Eq, Show)

-- PHIL-LLVM-CERT-012
-- Translation-only authority for hello-policy-validation-v1. The provider's
-- HelloPolicy semantics, opaque reason-handle contents/lifetime, fatal-effect
-- behavior, LLVM 18, linking, and native execution remain independent gates.
phase0HelloPolicyValidationLLVMCertification
  :: Either HelloPolicyValidationCertificationError HelloPolicyValidationCertificationBundle
phase0HelloPolicyValidationLLVMCertification = do
  systemsBundle <- mapLeft
    HelloPolicyValidationCertificationSystemsError
    phase0HelloPolicyValidationBundle
  let systemsArtifact = helloPolicyValidationArtifact systemsBundle
      llvmArtifact = lowerSystemsHelloPolicyValidation
        phase0HelloPolicyValidationLLVMTarget
        systemsArtifact
  mapLeft HelloPolicyValidationCertificationTranslationError $
    verifyHelloPolicyValidationTranslation systemsBundle llvmArtifact
  let systemsManifest = systemsAssuranceManifest (helloPolicyValidationContext systemsBundle)
      moduleValue = llvmArtifactModule llvmArtifact
      sourceDigest = llvmContractSourceDigest (llvmArtifactContract llvmArtifact)
      targetDigest = llvmContractTargetDigest (llvmArtifactContract llvmArtifact)
      targetTextDigest = digestText (llvmArtifactText llvmArtifact)
      abiDigest = llvmRuntimeABIDigest moduleValue
      certificationTarget = "preopt-llvm:" <> llvmTargetTriple moduleValue
      sourceCompilationProfile = Text.pack (show (llvmCompilationProfile moduleValue))
      certificationProfile =
        "translation-validation/" <> sourceCompilationProfile <> "/hello-policy-validation-v1"
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
        , ("policy_context", "explicit UploadServer ptr parameter")
        , ("hello_record", "exact recognized Hello ptr")
        , ("validator", "phil_runtime_validate_hello_policy(ptr,ptr,ptr)->i1")
        , ("reason_representation", "opaque provider ptr; no wire encoding")
        , ("failure_effect", "phil_runtime_fail_hello_policy(ptr,ptr)->void followed by terminal component return")
        , ("ambient_state", "forbidden")
        , ("provider_validation_semantics", "external runtime gate")
        , ("provider_reason_lifetime", "external runtime gate")
        , ("provider_failure_semantics", "external runtime gate")
        , ("external_llvm_gate", "canonical target text must be accepted by LLVM 18 in CI")
        ]
      evidenceScope = ValidityScope $
        Map.insert "target" certificationTarget $
        Map.insert "compilation_profile" certificationProfile validityContext
      revisionStatement =
        "The canonical Phase 0 HelloPolicy accepted/rejected(reason) Systems -> pre-optimization LLVM pair is certified only for the exact source, target, target text, target profile, and phil-runtime/phase0/hello-policy-validation-v1 ABI bound by this revision; Phil translation validation establishes explicit policyContext and recognized Hello operands, exact retained HelloPolicy runtime-site control, rejected-arm binding of the exact opaque reason handle, exact transport-and-reason fatal-effect call, preservation of the already-lowered BeginPolicy/version machinery, and absence of ambient policy/Hello/rejection state, while provider validation semantics, opaque reason contents and lifetime, fatal-effect runtime behavior, LLVM 18, linking, and native execution remain external gates."
      provisionalRevision = ObligationRevision
        { revisionObligationId = ObligationId "PHIL-LLVM-CERT-012"
        , revisionId = RevisionId ""
        , revisionStatement = revisionStatement
        , revisionStatementDigest = digestText revisionStatement
        , revisionKind = "LLVMHelloPolicyValidationTranslationCertification"
        , revisionOrigin = "HelloPolicy validation ABI v1 / PHIL-LLVM-CERT-012"
        , revisionScope = "llvm.phase0.preopt.hello-policy-validation.translation"
        , revisionRequiredAt = "certification"
        , revisionRepresentation =
            "HelloPolicy semantic validation choice SystemsArtifact -> explicit validator + opaque reason handle + fatal-effect primitive canonical pre-optimization LLVMArtifact"
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
        [ "phil-llvm-phase0-hello-policy-validation-translation-validation-v1"
        , "source-digest=" <> unDigest sourceDigest
        , "target-digest=" <> unDigest targetDigest
        , "target-text-digest=" <> unDigest targetTextDigest
        , "llvm-language=" <> llvmLanguageVersion moduleValue
        , "llvm-tool-profile=" <> llvmToolVersion moduleValue
        , "target-triple=" <> llvmTargetTriple moduleValue
        , "data-layout=" <> llvmDataLayout moduleValue
        , "runtime-abi-digest=" <> unDigest abiDigest
        , "runtime-abi-profile=" <> llvmRuntimeABIProfile moduleValue
        , "translation-validator=Phil.LLVM.HelloPolicyValidation.verifyHelloPolicyValidationTranslation"
        , "assurance-checker=Phil.Assurance.Verify.verifyManifest"
        ]
      translationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef
            "artifact:phil:llvm:phase0:hello-policy-validation:translation-validation:v1"
        , artifactDigest = digestText translationArtifactRecord
        }
      evidenceId = EvidenceEntryId
        "evidence.llvm.phase0.hello-policy-validation.translation.validated"
      provisionalEvidence = EvidenceEntry
        { evidenceEntryId = evidenceId
        , evidenceEntryDigest = Digest ""
        , evidenceObligationRevision = certificationRevisionId
        , evidenceAssuranceKind = TranslationValidated
        , evidenceRole = EvidenceRole "translation_validated"
        , evidenceProducer = "Phil.LLVM.HelloPolicyValidation.verifyHelloPolicyValidationTranslation"
        , evidenceChecker = "Phil.Assurance.Verify.verifyManifest"
        , evidenceArtifact = Just translationArtifact
        , evidenceInputDigests = [sourceDigest, targetDigest, targetTextDigest, abiDigest]
        , evidenceAssumptions = []
        , evidenceDependsOn = []
        , evidenceValidityScope = evidenceScope
        , evidenceResult = EvidenceAccepted
        , evidenceJustifies =
            [ "policyContext is an explicit UploadServer target parameter rather than ambient runtime state"
            , "recognized Hello is the exact validator record operand"
            , "HelloPolicy validation preserves the exact runtime site and accepted/rejected control"
            , "rejected-arm reason is loaded as an opaque pointer only on rejection"
            , "fatal-effect primitive receives exact server transport and exact rejected reason"
            , "the opaque reason is not encoded as peer protocol data"
            , "BeginPolicy/version physical lowering remains intact"
            , "ambient policy, Hello, and rejection-reason state is absent"
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
        [ "phil-llvm-phase0-hello-policy-validation-certification-root-v1"
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
  pure HelloPolicyValidationCertificationBundle
    { helloPolicyValidationCertificationSystems = systemsBundle
    , helloPolicyValidationCertificationLLVM = llvmArtifact
    , helloPolicyValidationCertificationArtifact = translationArtifact
    , helloPolicyValidationCertificationLedger = ledger
    , helloPolicyValidationCertificationManifest = manifest
    , helloPolicyValidationCertificationContext = verificationContext
    }

verifyPhase0HelloPolicyValidationLLVMCertification
  :: Either HelloPolicyValidationCertificationError ()
verifyPhase0HelloPolicyValidationLLVMCertification = do
  bundle <- phase0HelloPolicyValidationLLVMCertification
  mapLeft HelloPolicyValidationCertificationManifestError $
    verifyManifest
      (helloPolicyValidationCertificationContext bundle)
      (helloPolicyValidationCertificationLedger bundle)
      (helloPolicyValidationCertificationManifest bundle)

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
