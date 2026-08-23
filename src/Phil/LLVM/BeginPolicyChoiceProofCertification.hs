{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.BeginPolicyChoiceProofCertification
  ( systemsBeginPolicyChoiceCertificationSpec
  , llvmBeginPolicyChoiceCertificationSpec
  , BeginPolicyChoiceProofCertificationError (..)
  , BeginPolicyChoiceProofCertificationBundle (..)
  , phase0BeginPolicyChoiceProofCertification
  , verifyPhase0BeginPolicyChoiceProofCertification
  , renderBeginPolicyChoiceProofCertification
  ) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Rocq
import Phil.Assurance.Types
import Phil.Assurance.Verify (ManifestError, verifyManifest)
import Phil.Core.Syntax (ObligationId (..), unObligationId)
import Phil.LLVM.BeginPolicyChoiceCertification
import Phil.LLVM.IR
import Phil.LLVM.VersionSessionChoiceProofBoundCertification
import Phil.Systems.BeginPolicySessionChoice
import Phil.Systems.IR
import Phil.Systems.Verify (SystemsVerificationContext (..))

systemsBeginPolicyChoiceCertificationSpec :: RocqCertificationSpec
systemsBeginPolicyChoiceCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "systems-begin-policy-choice"
  , rocqSpecObligation = ObligationId "PHIL-SYS-BEGIN-POLICY-001"
  , rocqSpecClaim =
      "For the verified Phase 0 BeginPolicy Systems candidate, the established version-choice operand authority is preserved; policyContext is the exact no-producer RuntimeInput and Begin is the exact recognized RuntimeRecord; the exact predecessor BeginPolicy runtime site is retained; local accepted/rejected(reason) validation has exact operands, targets, and rejected-arm reason binding; server reject(reason)/proceed selectors use the exact transport with exact payload discipline; the client offers the exact dual choice with a distinct reject-only reason identity; legacy Bool/generic receive state is absent; and no physical reason representation, wire encoding, runtime ABI, or framing is claimed at Systems level."
  , rocqSpecKind = "Systems BeginPolicy semantic validation and session choice"
  , rocqSpecOrigin =
      "src/Phil/Systems/BeginPolicySessionChoice.hs; proof/Phil/Systems/BeginPolicySessionChoice.v"
  , rocqSpecScope = "Phil.Systems BeginPolicy accepted/rejected(reason) and reject(reason)/proceed choice"
  , rocqSpecRepresentation =
      "normalized explicit validator subjects / branch-local reason / exact session-choice model"
  , rocqSpecSubjects =
      [ "server.policy_context : RuntimeInput[PolicyContext]"
      , "server.begin : RuntimeRecord[Begin]"
      , "server.begin_reject_reason : RuntimeOpaque[ValidationReason[BeginPolicy]]"
      , "client.begin_reject_reason : RuntimeOpaque[ValidationReason[BeginPolicy]]"
      , "server.transport"
      , "client.transport"
      ]
  , rocqSpecTheorems =
      [ "verified_systems_begin_policy_reuses_version_operand_authority"
      , "verified_systems_begin_policy_preserves_exact_validator_subjects_and_site"
      , "verified_systems_begin_policy_preserves_local_accepted_rejected_choice"
      , "verified_systems_begin_policy_preserves_exact_server_selects"
      , "verified_systems_begin_policy_preserves_client_offer_and_endpoint_separation"
      , "verified_systems_begin_policy_eliminates_legacy_state_and_binds_decision"
      , "verified_systems_begin_policy_claims_no_physical_representation"
      , "systems_begin_policy_validator_or_reason_drift_is_rejected"
      , "systems_begin_policy_protocol_or_legacy_drift_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Systems/BeginPolicySessionChoice.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Systems/BeginPolicySessionChoice.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-SYS-BEGIN-POLICY-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-SYS-BEGIN-POLICY-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness plus reviewed correspondence from concrete Haskell ValueId/BlockId/RuntimeSiteRef identities, operation multiplicity, branch-local binders, and lowering-decision identity to the normalized proof model remain explicit trust boundaries. Physical rejection-reason representation and protocol encoding are outside this Systems theorem."
  }

llvmBeginPolicyChoiceCertificationSpec :: RocqCertificationSpec
llvmBeginPolicyChoiceCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "llvm-begin-policy-choice"
  , rocqSpecObligation = ObligationId "PHIL-LLVM-BEGIN-POLICY-001"
  , rocqSpecClaim =
      "For begin-policy-choice-v1, verified lowering preserves the exact explicit policyContext parameter and recognized Begin validator operand, exact retained runtime site, rejected-only reason slot/binding, exact server reject(reason) and proceed selectors, exact client receiver and reject-only reason binding, exact frozen-program reason-use premise authorizing the v1 observable quotient, canonical proceed=0x01 and reject=0x00||0x01 representation, preservation of the already-lowered version-choice predecessor, and absence of unlowered/generic/ambient BeginPolicy state. Validator semantics, quotient adequacy beyond the exact frozen use shape, concrete I/O, malformed-input non-return, physical write success, LLVM correctness, linking, native execution, and outer framing remain external gates."
  , rocqSpecKind = "LLVM BeginPolicy choice ABI v1"
  , rocqSpecOrigin =
      "src/Phil/LLVM/BeginPolicyChoice.hs; docs/phase-0/begin-policy-choice-abi-v1.md; proof/Phil/LLVM/BeginPolicyChoice.v"
  , rocqSpecScope = "Phil.LLVM begin-policy-choice-v1"
  , rocqSpecRepresentation =
      "normalized validator / reason-slot / selector / receiver / exact-program quotient model"
  , rocqSpecSubjects =
      [ "phil_runtime_validate_begin_policy(ptr,ptr,ptr)->i1"
      , "phil_runtime_select_begin_policy_reject(ptr,i8)->void"
      , "phil_runtime_select_begin_policy_proceed(ptr)->void"
      , "phil_runtime_receive_begin_policy_choice(ptr,ptr)->i1"
      , "proceed 0x01"
      , "reject 0x00 0x01"
      ]
  , rocqSpecTheorems =
      [ "verified_llvm_begin_policy_reuses_systems_and_version_authority"
      , "verified_llvm_begin_policy_preserves_target_parameter_and_validator"
      , "verified_llvm_begin_policy_preserves_server_selectors"
      , "verified_llvm_begin_policy_preserves_client_receiver_and_reason_binding"
      , "verified_llvm_begin_policy_binds_exact_program_reason_use_quotient"
      , "verified_llvm_begin_policy_eliminates_unlowered_and_ambient_state"
      , "verified_llvm_begin_policy_keeps_external_runtime_gates_explicit"
      , "llvm_begin_policy_validator_or_selector_drift_is_rejected"
      , "llvm_begin_policy_receiver_reason_or_ambient_drift_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/LLVM/BeginPolicyChoice.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/LLVM/BeginPolicyChoice.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-LLVM-BEGIN-POLICY-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-LLVM-BEGIN-POLICY-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness; reviewed Systems/LLVM-to-normalized-proof correspondence; provider validator semantics; exact-program adequacy of the selected observable reason quotient; concrete byte I/O; malformed/reserved non-return; selector write success; target calling convention; LLVM 18; linking; native execution; and outer framing remain explicit trust boundaries."
  }

data BeginPolicyChoiceProofCertificationError
  = BeginPolicyProofBaseError BeginPolicyChoiceCertificationError
  | BeginPolicyProofWrongProof Text ObligationId ObligationId
  | BeginPolicyProofManifestError Text ManifestError
  | BeginPolicyProofFinalManifestError ManifestError
  deriving (Eq, Show)

data BeginPolicyChoiceProofCertificationBundle = BeginPolicyChoiceProofCertificationBundle
  { beginPolicyProofBase :: BeginPolicyChoiceCertificationBundle
  , beginPolicyProofPredecessor :: VersionSessionChoiceProofBoundCertificationBundle
  , beginPolicyProofArtifact :: ArtifactIdentity
  , beginPolicyProofRecord :: Text
  , beginPolicyProofLedger :: AssuranceLedger
  , beginPolicyProofManifest :: AssuranceManifest
  , beginPolicyProofContext :: VerificationContext
  }
  deriving (Eq, Show)

phase0BeginPolicyChoiceProofCertification
  :: RocqCertificationBundle
  -> RocqCertificationBundle
  -> VersionSessionChoiceProofBoundCertificationBundle
  -> Either BeginPolicyChoiceProofCertificationError BeginPolicyChoiceProofCertificationBundle
phase0BeginPolicyChoiceProofCertification systemsProof llvmProof predecessor = do
  verifyProof "systems-begin-policy" systemsBeginPolicyChoiceCertificationSpec systemsProof
  verifyProof "llvm-begin-policy" llvmBeginPolicyChoiceCertificationSpec llvmProof
  base <- mapLeft BeginPolicyProofBaseError phase0BeginPolicyChoiceLLVMCertification

  let proofBundles = [systemsProof, llvmProof]
      proofLedgers = map rocqBundleLedger proofBundles
      semanticRevisions = Map.unions (map ledgerRevisions proofLedgers)
      semanticEvidence = Map.unions (map ledgerEvidence proofLedgers)
      semanticRevisionIds = Map.keysSet semanticRevisions
      semanticEvidenceIds = Map.keysSet semanticEvidence
      proofArtifacts = map rocqBundleCertificateArtifact proofBundles
      proofDigests = map artifactDigest proofArtifacts
      predecessorArtifact = versionProofBoundArtifact predecessor

      systemsBundle = beginPolicyChoiceCertificationSystems base
      systemsArtifact = beginPolicySessionChoiceArtifact systemsBundle
      systemsManifest = systemsAssuranceManifest (beginPolicySessionChoiceContext systemsBundle)
      llvmArtifact = beginPolicyChoiceCertificationLLVM base
      moduleValue = llvmArtifactModule llvmArtifact
      translationArtifact = beginPolicyChoiceCertificationArtifact base
      sourceDigest = llvmContractSourceDigest (llvmArtifactContract llvmArtifact)
      targetDigest = llvmContractTargetDigest (llvmArtifactContract llvmArtifact)
      targetTextDigest = digestText (llvmArtifactText llvmArtifact)
      abiDigest = llvmRuntimeABIDigest moduleValue
      systemsLoweringRoot = loweringLedgerRoot (systemsArtifactLoweringLedger systemsArtifact)
      certificationTarget = "preopt-llvm:" <> llvmTargetTriple moduleValue
      sourceCompilationProfile = Text.pack (show (llvmCompilationProfile moduleValue))
      certificationProfile =
        "translation-validation/" <> sourceCompilationProfile <> "/begin-policy-choice-v1/proof-bound"
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
        , ("predecessor_certification", unDigest (artifactDigest predecessorArtifact))
        , ("proof_assistant", "Rocq")
        , ("rocq_version", "9.2.0")
        , ("certificate_profile", "proof-assistant-theorem/v1")
        , ("policy_context", "explicit UploadServer ptr parameter")
        , ("begin_record", "exact recognized Begin ptr")
        , ("validator", "phil_runtime_validate_begin_policy(ptr,ptr,ptr)->i1")
        , ("reason_representation", "i8 exact-program observable quotient")
        , ("reject_selector", "phil_runtime_select_begin_policy_reject(ptr,i8)->void")
        , ("proceed_selector", "phil_runtime_select_begin_policy_proceed(ptr)->void")
        , ("receiver", "phil_runtime_receive_begin_policy_choice(ptr,ptr)->i1")
        , ("wire_proceed", "0x01")
        , ("wire_reject", "0x00 followed by canonical reason 0x01")
        , ("external_validator_semantics", "provider gate")
        , ("external_reason_quotient", "exact-program semantic adequacy gate")
        , ("external_runtime_abi", "provider signature and execution gate")
        , ("external_malformed", "EOF/reserved/truncated input must not return normally")
        , ("external_llvm", "LLVM 18 acceptance/link gate")
        , ("residual_write_failure", "source select has no write-failure continuation")
        , ("outer_framing", "not defined by begin-policy-choice-v1")
        ]
      evidenceScope = ValidityScope $
        Map.insert "target" certificationTarget $
        Map.insert "compilation_profile" certificationProfile validityContext
      revisionStatement =
        "The begin-policy-choice-v1 Systems -> canonical pre-optimization LLVM pair may be labeled Certified only when exact source/target/text digests, Systems lowering root, target/runtime-ABI/tool identities, the proof-bound PHIL-LLVM-CERT-010 predecessor certificate, PHIL-SYS-BEGIN-POLICY-001 semantic authority, PHIL-LLVM-BEGIN-POLICY-001 lowering authority, and the exact BeginPolicy translation-validation result are content-bound. Predecessor TranslationValidated evidence is not imported across validity scopes: only the already proof-bound CERT-010 artifact identity is bound. Provider BeginPolicy semantics, adequacy of the exact frozen-program rejection-reason quotient, concrete byte I/O, malformed-input non-return, physical write success, provider ABI conformance, LLVM implementation correctness, linking, native execution, and outer framing remain explicit external gates."
      provisionalRevision = ObligationRevision
        { revisionObligationId = ObligationId "PHIL-LLVM-CERT-011"
        , revisionId = RevisionId ""
        , revisionStatement = revisionStatement
        , revisionStatementDigest = digestText revisionStatement
        , revisionKind = "LLVMBeginPolicyChoiceProofBoundCertification"
        , revisionOrigin = "BeginPolicy reject/proceed choice ABI v1 / proof-bound PHIL-LLVM-CERT-011"
        , revisionScope = "llvm.phase0.preopt.begin-policy-choice.proof-bound"
        , revisionRequiredAt = "certification"
        , revisionRepresentation =
            "BeginPolicy semantic SystemsArtifact -> begin-policy-choice-v1 canonical pre-optimization LLVMArtifact + proof authority"
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
        , revisionAcceptanceRule = AcceptEntry TranslationValidated (EvidenceRole "translation_validated")
        , revisionGeneratedFrom = Set.toAscList semanticRevisionIds
        }
      certificationRevision = provisionalRevision
        { revisionId = deriveRevisionId provisionalRevision }
      certificationRevisionId = revisionId certificationRevision
      translationEvidenceId = EvidenceEntryId
        "evidence.llvm.phase0.begin-policy-choice.proof-bound.translation.validated"
      provisionalEvidence = EvidenceEntry
        { evidenceEntryId = translationEvidenceId
        , evidenceEntryDigest = Digest ""
        , evidenceObligationRevision = certificationRevisionId
        , evidenceAssuranceKind = TranslationValidated
        , evidenceRole = EvidenceRole "translation_validated"
        , evidenceProducer = "Phil.LLVM.BeginPolicyChoice.verifyBeginPolicyChoiceTranslation"
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
            [ "explicit policyContext and exact recognized Begin validator operands"
            , "retained BeginPolicy runtime site and exact accepted/rejected control"
            , "rejected-only server reason materialization and exact reject(reason)/proceed selectors"
            , "exact client receiver and reject-only distinct reason binding"
            , "exact frozen-program server-use=1/client-use=0 reason quotient premise"
            , "canonical proceed=0x01 and reject=0x00||0x01 ABI profile"
            , "preservation of proof-bound version-session-choice predecessor authority"
            , "absence of unlowered, generic, and ambient BeginPolicy state"
            ]
        , evidenceRuntimeMechanism = Nothing
        , evidenceRuntimeResidue = []
        , evidenceCostRefs = []
        }
      translationEvidence = provisionalEvidence
        { evidenceEntryDigest = deriveEvidenceEntryDigest provisionalEvidence }
      certificationRecord = Text.unlines $
        [ "phil-llvm-phase0-begin-policy-choice-certification/v1"
        , "obligation=PHIL-LLVM-CERT-011"
        , "revision=" <> unRevisionId certificationRevisionId
        , "source-digest=" <> unDigest sourceDigest
        , "systems-lowering-root=" <> unDigest systemsLoweringRoot
        , "target-digest=" <> unDigest targetDigest
        , "target-text-digest=" <> unDigest targetTextDigest
        , "runtime-abi-profile=" <> llvmRuntimeABIProfile moduleValue
        , "runtime-abi-digest=" <> unDigest abiDigest
        , "translation-artifact=" <> renderArtifact translationArtifact
        , "predecessor-certification=" <> renderArtifact predecessorArtifact
        ] <> map renderProofArtifact proofBundles <>
        [ "external-validator-semantics=provider gate"
        , "external-reason-quotient=exact-program semantic adequacy gate"
        , "external-runtime-abi=provider signature and execution gate"
        , "external-malformed=EOF/reserved/truncated input non-return gate"
        , "external-llvm=LLVM 18 acceptance/link gate"
        , "residual-write-failure=source select has no write-failure continuation"
        , "residual-outer-framing=not defined by begin-policy-choice-v1"
        ]
      certificationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef "certificate:phil:llvm:PHIL-LLVM-CERT-011:v1"
        , artifactDigest = digestText certificationRecord
        }
      revisions = Map.insert certificationRevisionId certificationRevision semanticRevisions
      evidence = Map.insert translationEvidenceId translationEvidence semanticEvidence
      obligationIds = Set.insert certificationRevisionId semanticRevisionIds
      evidenceIds = Set.insert translationEvidenceId semanticEvidenceIds
      ledger = emptyLedger
        { ledgerRevisions = revisions
        , ledgerEvidence = evidence
        }
      certificationRoot = digestText $ Text.intercalate "|" $
        [ "phil-llvm-phase0-begin-policy-choice-proof-bound-certification-root-v1"
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
      context = emptyVerificationContext
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
      bundle = BeginPolicyChoiceProofCertificationBundle
        { beginPolicyProofBase = base
        , beginPolicyProofPredecessor = predecessor
        , beginPolicyProofArtifact = certificationArtifact
        , beginPolicyProofRecord = certificationRecord
        , beginPolicyProofLedger = ledger
        , beginPolicyProofManifest = manifest
        , beginPolicyProofContext = context
        }

  mapLeft BeginPolicyProofFinalManifestError $ verifyManifest context ledger manifest
  pure bundle

verifyPhase0BeginPolicyChoiceProofCertification
  :: RocqCertificationBundle
  -> RocqCertificationBundle
  -> VersionSessionChoiceProofBoundCertificationBundle
  -> Either BeginPolicyChoiceProofCertificationError ()
verifyPhase0BeginPolicyChoiceProofCertification systemsProof llvmProof predecessor = do
  bundle <- phase0BeginPolicyChoiceProofCertification systemsProof llvmProof predecessor
  mapLeft BeginPolicyProofFinalManifestError $
    verifyManifest
      (beginPolicyProofContext bundle)
      (beginPolicyProofLedger bundle)
      (beginPolicyProofManifest bundle)

renderBeginPolicyChoiceProofCertification :: BeginPolicyChoiceProofCertificationBundle -> Text
renderBeginPolicyChoiceProofCertification = beginPolicyProofRecord

verifyProof
  :: Text
  -> RocqCertificationSpec
  -> RocqCertificationBundle
  -> Either BeginPolicyChoiceProofCertificationError ()
verifyProof label spec bundle = do
  let expected = rocqSpecObligation spec
      actual = rocqCertificateObligation (rocqBundleCertificate bundle)
  unless (actual == expected) $
    Left (BeginPolicyProofWrongProof label expected actual)
  mapLeft (BeginPolicyProofManifestError label) $
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
