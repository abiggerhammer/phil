{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.BeginPolicyChoiceCertification
  ( BeginPolicyChoiceCertificationError (..)
  , BeginPolicyChoiceCertificationBundle (..)
  , phase0BeginPolicyChoiceLLVMCertification
  , verifyPhase0BeginPolicyChoiceLLVMCertification
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Assurance.Types
import Phil.Assurance.Verify (ManifestError, verifyManifest)
import Phil.Core.Syntax (ObligationId (..))
import Phil.LLVM.BeginPolicyChoice
import Phil.LLVM.IR
import Phil.Systems.BeginPolicySessionChoice
import Phil.Systems.Verify (SystemsVerificationContext (..))

data BeginPolicyChoiceCertificationError
  = BeginPolicyChoiceCertificationSystemsError BeginPolicySessionChoiceError
  | BeginPolicyChoiceCertificationTranslationError BeginPolicyChoiceLLVMError
  | BeginPolicyChoiceCertificationManifestError ManifestError
  deriving (Eq, Show)

data BeginPolicyChoiceCertificationBundle = BeginPolicyChoiceCertificationBundle
  { beginPolicyChoiceCertificationSystems :: BeginPolicySessionChoiceBundle
  , beginPolicyChoiceCertificationLLVM :: LLVMArtifact
  , beginPolicyChoiceCertificationArtifact :: ArtifactIdentity
  , beginPolicyChoiceCertificationLedger :: AssuranceLedger
  , beginPolicyChoiceCertificationManifest :: AssuranceManifest
  , beginPolicyChoiceCertificationContext :: VerificationContext
  }
  deriving (Eq, Show)

-- PHIL-LLVM-CERT-011
--
-- Translation-only authority for begin-policy-choice-v1. Correctness of the
-- BeginPolicy validator, the frozen-program observable-equivalence quotient for
-- rejection reasons, concrete byte I/O, malformed-input non-return, physical
-- write success, LLVM 18, linking, and native execution remain independent
-- gates. A proof-bound successor is intentionally left to the Rocq harvest.
phase0BeginPolicyChoiceLLVMCertification
  :: Either BeginPolicyChoiceCertificationError BeginPolicyChoiceCertificationBundle
phase0BeginPolicyChoiceLLVMCertification = do
  systemsBundle <- mapLeft
    BeginPolicyChoiceCertificationSystemsError
    phase0BeginPolicySessionChoiceBundle
  let systemsArtifact = beginPolicySessionChoiceArtifact systemsBundle
      llvmArtifact = lowerSystemsBeginPolicyChoice
        phase0BeginPolicyChoiceLLVMTarget
        systemsArtifact
  mapLeft BeginPolicyChoiceCertificationTranslationError $
    verifyBeginPolicyChoiceTranslation systemsBundle llvmArtifact
  let systemsManifest = systemsAssuranceManifest (beginPolicySessionChoiceContext systemsBundle)
      moduleValue = llvmArtifactModule llvmArtifact
      sourceDigest = llvmContractSourceDigest (llvmArtifactContract llvmArtifact)
      targetDigest = llvmContractTargetDigest (llvmArtifactContract llvmArtifact)
      targetTextDigest = digestText (llvmArtifactText llvmArtifact)
      abiDigest = llvmRuntimeABIDigest moduleValue
      certificationTarget = "preopt-llvm:" <> llvmTargetTriple moduleValue
      sourceCompilationProfile = Text.pack (show (llvmCompilationProfile moduleValue))
      certificationProfile =
        "translation-validation/" <> sourceCompilationProfile <> "/begin-policy-choice-v1"
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
        , ("begin_record", "exact recognized Begin ptr")
        , ("validator", "phil_runtime_validate_begin_policy(ptr,ptr,ptr)->i1")
        , ("reason_representation", "i8 boundary code; canonical observable class 0x01")
        , ("reject_selector", "phil_runtime_select_begin_policy_reject(ptr,i8)->void")
        , ("proceed_selector", "phil_runtime_select_begin_policy_proceed(ptr)->void")
        , ("receiver", "phil_runtime_receive_begin_policy_choice(ptr,ptr)->i1")
        , ("wire_proceed", "0x01")
        , ("wire_reject", "0x00 followed by reason u8; v1 canonical reason 0x01")
        , ("malformed_input", "tag EOF, reserved tag, truncated reject, or reserved reason must not return normally")
        , ("write_failure", "residual runtime assumption")
        , ("outer_framing", "not defined by begin-policy-choice-v1")
        , ("ambient_state", "forbidden")
        , ("provider_validation_semantics", "external runtime gate")
        , ("observable_reason_quotient", "external exact-program gate")
        , ("external_runtime_gate", "validator semantics and concrete encoding checked independently in CI")
        , ("external_llvm_gate", "canonical target text must be accepted by LLVM 18 in CI")
        ]
      evidenceScope = ValidityScope $
        Map.insert "target" certificationTarget $
        Map.insert "compilation_profile" certificationProfile validityContext
      revisionStatement =
        "The canonical Phase 0 BeginPolicy reject(reason)/proceed Systems -> pre-optimization LLVM pair is certified only for the exact source, target, target text, target profile, and phil-runtime/phase0/begin-policy-choice-v1 ABI bound by this revision; Phil translation validation establishes explicit policyContext and recognized Begin validator operands, exact accepted/rejected control, rejected-arm reason materialization, exact transport-bound reject(reason) and proceed selectors, exact client receiver and rejected-arm reason binding, preservation of the already-lowered version choice, and absence of ambient policy/choice/rejection state, while validator semantic correctness, the exact frozen-program quotient that maps every client-unobserved BeginPolicy rejection to canonical reason code 0x01, concrete byte I/O, malformed-input non-return, physical write success, provider conformance, LLVM 18, linking, and native execution remain external gates."
      provisionalRevision = ObligationRevision
        { revisionObligationId = ObligationId "PHIL-LLVM-CERT-011"
        , revisionId = RevisionId ""
        , revisionStatement = revisionStatement
        , revisionStatementDigest = digestText revisionStatement
        , revisionKind = "LLVMBeginPolicyChoiceTranslationCertification"
        , revisionOrigin = "BeginPolicy reject/proceed choice ABI v1 / PHIL-LLVM-CERT-011"
        , revisionScope = "llvm.phase0.preopt.begin-policy-choice.translation"
        , revisionRequiredAt = "certification"
        , revisionRepresentation =
            "BeginPolicy semantic choice SystemsArtifact -> explicit validator + reject/proceed physical primitives canonical pre-optimization LLVMArtifact"
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
        [ "phil-llvm-phase0-begin-policy-choice-translation-validation-v1"
        , "source-digest=" <> unDigest sourceDigest
        , "target-digest=" <> unDigest targetDigest
        , "target-text-digest=" <> unDigest targetTextDigest
        , "llvm-language=" <> llvmLanguageVersion moduleValue
        , "llvm-tool-profile=" <> llvmToolVersion moduleValue
        , "target-triple=" <> llvmTargetTriple moduleValue
        , "data-layout=" <> llvmDataLayout moduleValue
        , "runtime-abi-digest=" <> unDigest abiDigest
        , "runtime-abi-profile=" <> llvmRuntimeABIProfile moduleValue
        , "translation-validator=Phil.LLVM.BeginPolicyChoice.verifyBeginPolicyChoiceTranslation"
        , "assurance-checker=Phil.Assurance.Verify.verifyManifest"
        ]
      translationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef
            "artifact:phil:llvm:phase0:begin-policy-choice:translation-validation:v1"
        , artifactDigest = digestText translationArtifactRecord
        }
      evidenceId = EvidenceEntryId
        "evidence.llvm.phase0.begin-policy-choice.translation.validated"
      provisionalEvidence = EvidenceEntry
        { evidenceEntryId = evidenceId
        , evidenceEntryDigest = Digest ""
        , evidenceObligationRevision = certificationRevisionId
        , evidenceAssuranceKind = TranslationValidated
        , evidenceRole = EvidenceRole "translation_validated"
        , evidenceProducer = "Phil.LLVM.BeginPolicyChoice.verifyBeginPolicyChoiceTranslation"
        , evidenceChecker = "Phil.Assurance.Verify.verifyManifest"
        , evidenceArtifact = Just translationArtifact
        , evidenceInputDigests = [sourceDigest, targetDigest, targetTextDigest, abiDigest]
        , evidenceAssumptions = []
        , evidenceDependsOn = []
        , evidenceValidityScope = evidenceScope
        , evidenceResult = EvidenceAccepted
        , evidenceJustifies =
            [ "policyContext is an explicit UploadServer target parameter rather than ambient runtime state"
            , "recognized Begin is the exact validator record operand"
            , "BeginPolicy validation preserves the exact runtime site and maps accepted/rejected control explicitly"
            , "server rejected-arm reason is loaded only on rejection and passed exactly to the reject selector"
            , "server proceed selector uses exact transport and no payload"
            , "client receiver maps true->proceed and false->reject and binds a distinct reason only on reject"
            , "version/unsupported physical lowering remains intact"
            , "generic BeginPolicy validation/select/receive machinery is eliminated"
            , "ambient policy, choice, transport, and rejection-reason state is absent"
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
        [ "phil-llvm-phase0-begin-policy-choice-certification-root-v1"
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
  pure BeginPolicyChoiceCertificationBundle
    { beginPolicyChoiceCertificationSystems = systemsBundle
    , beginPolicyChoiceCertificationLLVM = llvmArtifact
    , beginPolicyChoiceCertificationArtifact = translationArtifact
    , beginPolicyChoiceCertificationLedger = ledger
    , beginPolicyChoiceCertificationManifest = manifest
    , beginPolicyChoiceCertificationContext = verificationContext
    }

verifyPhase0BeginPolicyChoiceLLVMCertification
  :: Either BeginPolicyChoiceCertificationError ()
verifyPhase0BeginPolicyChoiceLLVMCertification = do
  bundle <- phase0BeginPolicyChoiceLLVMCertification
  mapLeft BeginPolicyChoiceCertificationManifestError $
    verifyManifest
      (beginPolicyChoiceCertificationContext bundle)
      (beginPolicyChoiceCertificationLedger bundle)
      (beginPolicyChoiceCertificationManifest bundle)

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
