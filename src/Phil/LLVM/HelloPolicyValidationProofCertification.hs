{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.HelloPolicyValidationProofCertification
  ( systemsHelloPolicyValidationCertificationSpec
  , llvmHelloPolicyValidationCertificationSpec
  , HelloPolicyValidationProofCertificationError (..)
  , HelloPolicyValidationProofCertificationBundle (..)
  , phase0HelloPolicyValidationProofCertification
  , verifyPhase0HelloPolicyValidationProofCertification
  , renderHelloPolicyValidationProofCertification
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
import Phil.LLVM.BeginPolicyChoiceProofCertification
import Phil.LLVM.HelloPolicyValidationCertification
import Phil.LLVM.IR
import Phil.Systems.HelloPolicyValidation
import Phil.Systems.IR
import Phil.Systems.Verify (SystemsVerificationContext (..))

systemsHelloPolicyValidationCertificationSpec :: RocqCertificationSpec
systemsHelloPolicyValidationCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "systems-hello-policy-validation"
  , rocqSpecObligation = ObligationId "PHIL-SYS-HELLO-POLICY-001"
  , rocqSpecClaim =
      "For the verified Phase 0 HelloPolicy Systems candidate, proof-bound BeginPolicy semantic authority is preserved; policyContext is the exact no-producer RuntimeInput and Hello is the exact recognized RuntimeRecord; the exact predecessor HelloPolicy runtime site is retained; local accepted/rejected(reason) validation has exact operands, targets, and rejected-arm reason binding; the rejected reason has exactly one semantic use, in the exact fail validation HelloPolicy(server.transport, reason) effect followed by the existing fatal class; the lowering decision is exact; and no physical reason representation, runtime ABI, wire encoding, or framing is claimed at Systems level."
  , rocqSpecKind = "Systems HelloPolicy semantic validation and fatal reason flow"
  , rocqSpecOrigin =
      "src/Phil/Systems/HelloPolicyValidation.hs; proof/Phil/Systems/HelloPolicyValidation.v"
  , rocqSpecScope = "Phil.Systems HelloPolicy accepted/rejected(reason) and fatal validation effect"
  , rocqSpecRepresentation =
      "normalized explicit validator subjects / branch-local opaque reason / unique fatal-use model"
  , rocqSpecSubjects =
      [ "server.policy_context : RuntimeInput[PolicyContext]"
      , "server.hello : RuntimeRecord[Hello]"
      , "server.hello_reject_reason : RuntimeOpaque[ValidationReason[HelloPolicy]]"
      , "server.transport"
      ]
  , rocqSpecTheorems =
      [ "verified_systems_hello_policy_reuses_begin_policy_authority"
      , "verified_systems_hello_policy_preserves_exact_validator_subjects_and_site"
      , "verified_systems_hello_policy_preserves_accepted_rejected_reason_choice"
      , "verified_systems_hello_policy_preserves_exact_fatal_reason_flow"
      , "verified_systems_hello_policy_binds_exact_lowering_decision"
      , "verified_systems_hello_policy_claims_no_physical_representation"
      , "systems_hello_policy_validator_or_reason_drift_is_rejected"
      , "systems_hello_policy_failure_flow_drift_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Systems/HelloPolicyValidation.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Systems/HelloPolicyValidation.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-SYS-HELLO-POLICY-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-SYS-HELLO-POLICY-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness plus reviewed correspondence from concrete Haskell ValueId/BlockId/RuntimeSiteRef identities, branch-local binder, exact failure operation, unique semantic reason use, and lowering-decision identity to the normalized proof model remain explicit trust boundaries. Physical validator/reason representation and runtime behavior are outside this Systems theorem."
  }

llvmHelloPolicyValidationCertificationSpec :: RocqCertificationSpec
llvmHelloPolicyValidationCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "llvm-hello-policy-validation"
  , rocqSpecObligation = ObligationId "PHIL-LLVM-HELLO-POLICY-001"
  , rocqSpecClaim =
      "For hello-policy-validation-v1, verified lowering preserves the exact explicit policyContext parameter and recognized Hello validator operand, exact retained runtime site, rejected-only opaque pointer reason slot/binding, exact validator-produced pointer identity into phil_runtime_fail_hello_policy(server.transport, reason), terminal return, and proof-bound BeginPolicy predecessor authority, while introducing no reason wire encoding, peer protocol effect, generic/unlowered HelloPolicy control, or ambient policy/Hello/rejection state. Provider validator semantics, opaque reason contents/lifetime, fatal-effect runtime semantics, LLVM correctness, linking, and native execution remain external gates."
  , rocqSpecKind = "LLVM HelloPolicy validation ABI v1"
  , rocqSpecOrigin =
      "src/Phil/LLVM/HelloPolicyValidation.hs; docs/phase-0/hello-policy-validation-abi-v1.md; proof/Phil/LLVM/HelloPolicyValidation.v"
  , rocqSpecScope = "Phil.LLVM hello-policy-validation-v1"
  , rocqSpecRepresentation =
      "normalized validator / pointer reason-slot / exact fatal-effect identity model"
  , rocqSpecSubjects =
      [ "phil_runtime_validate_hello_policy(ptr,ptr,ptr)->i1"
      , "opaque provider rejection-reason ptr"
      , "phil_runtime_fail_hello_policy(ptr,ptr)->void"
      , "server.transport"
      ]
  , rocqSpecTheorems =
      [ "verified_llvm_hello_policy_reuses_systems_and_begin_policy_authority"
      , "verified_llvm_hello_policy_preserves_target_parameter_and_validator"
      , "verified_llvm_hello_policy_preserves_opaque_reason_identity_to_failure"
      , "verified_llvm_hello_policy_eliminates_wire_generic_and_ambient_state"
      , "verified_llvm_hello_policy_keeps_provider_and_execution_gates_external"
      , "llvm_hello_policy_validator_or_reason_identity_drift_is_rejected"
      , "llvm_hello_policy_failure_or_ambient_drift_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/LLVM/HelloPolicyValidation.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/LLVM/HelloPolicyValidation.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-LLVM-HELLO-POLICY-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-LLVM-HELLO-POLICY-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness; reviewed Systems/LLVM-to-normalized-proof correspondence; provider HelloPolicy semantics; opaque reason contents and provider-owned lifetime through the failure call; fatal-effect runtime behavior; target calling convention; LLVM 18; linking; and native execution remain explicit trust boundaries."
  }

data HelloPolicyValidationProofCertificationError
  = HelloPolicyProofBaseError HelloPolicyValidationCertificationError
  | HelloPolicyProofWrongProof Text ObligationId ObligationId
  | HelloPolicyProofManifestError Text ManifestError
  | HelloPolicyProofFinalManifestError ManifestError
  deriving (Eq, Show)

data HelloPolicyValidationProofCertificationBundle = HelloPolicyValidationProofCertificationBundle
  { helloPolicyProofBase :: HelloPolicyValidationCertificationBundle
  , helloPolicyProofPredecessor :: BeginPolicyChoiceProofCertificationBundle
  , helloPolicyProofArtifact :: ArtifactIdentity
  , helloPolicyProofRecord :: Text
  , helloPolicyProofLedger :: AssuranceLedger
  , helloPolicyProofManifest :: AssuranceManifest
  , helloPolicyProofContext :: VerificationContext
  }
  deriving (Eq, Show)

phase0HelloPolicyValidationProofCertification
  :: RocqCertificationBundle
  -> RocqCertificationBundle
  -> BeginPolicyChoiceProofCertificationBundle
  -> Either HelloPolicyValidationProofCertificationError HelloPolicyValidationProofCertificationBundle
phase0HelloPolicyValidationProofCertification systemsProof llvmProof predecessor = do
  verifyProof "systems-hello-policy" systemsHelloPolicyValidationCertificationSpec systemsProof
  verifyProof "llvm-hello-policy" llvmHelloPolicyValidationCertificationSpec llvmProof
  base <- mapLeft HelloPolicyProofBaseError phase0HelloPolicyValidationLLVMCertification

  let proofBundles = [systemsProof, llvmProof]
      proofLedgers = map rocqBundleLedger proofBundles
      semanticRevisions = Map.unions (map ledgerRevisions proofLedgers)
      semanticEvidence = Map.unions (map ledgerEvidence proofLedgers)
      semanticRevisionIds = Map.keysSet semanticRevisions
      semanticEvidenceIds = Map.keysSet semanticEvidence
      proofArtifacts = map rocqBundleCertificateArtifact proofBundles
      proofDigests = map artifactDigest proofArtifacts
      predecessorArtifact = beginPolicyProofArtifact predecessor

      systemsBundle = helloPolicyValidationCertificationSystems base
      systemsArtifact = helloPolicyValidationArtifact systemsBundle
      systemsManifest = systemsAssuranceManifest (helloPolicyValidationContext systemsBundle)
      llvmArtifact = helloPolicyValidationCertificationLLVM base
      moduleValue = llvmArtifactModule llvmArtifact
      translationArtifact = helloPolicyValidationCertificationArtifact base
      sourceDigest = llvmContractSourceDigest (llvmArtifactContract llvmArtifact)
      targetDigest = llvmContractTargetDigest (llvmArtifactContract llvmArtifact)
      targetTextDigest = digestText (llvmArtifactText llvmArtifact)
      abiDigest = llvmRuntimeABIDigest moduleValue
      systemsLoweringRoot = loweringLedgerRoot (systemsArtifactLoweringLedger systemsArtifact)
      certificationTarget = "preopt-llvm:" <> llvmTargetTriple moduleValue
      sourceCompilationProfile = Text.pack (show (llvmCompilationProfile moduleValue))
      certificationProfile =
        "translation-validation/" <> sourceCompilationProfile <> "/hello-policy-validation-v1/proof-bound"
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
        , ("hello_record", "exact recognized Hello ptr")
        , ("validator", "phil_runtime_validate_hello_policy(ptr,ptr,ptr)->i1")
        , ("reason_representation", "opaque provider ptr; no wire encoding")
        , ("reason_identity", "validator output ptr preserved exactly into fail call")
        , ("failure_effect", "phil_runtime_fail_hello_policy(ptr,ptr)->void followed by terminal component return")
        , ("external_validator_semantics", "provider gate")
        , ("external_reason_contents", "provider gate")
        , ("external_reason_lifetime", "provider gate through fail call")
        , ("external_failure_semantics", "runtime gate")
        , ("external_llvm", "LLVM 18 acceptance/link gate")
        , ("external_native", "native execution gate")
        , ("outer_framing", "not defined by hello-policy-validation-v1")
        ]
      evidenceScope = ValidityScope $
        Map.insert "target" certificationTarget $
        Map.insert "compilation_profile" certificationProfile validityContext
      revisionStatement =
        "The hello-policy-validation-v1 Systems -> canonical pre-optimization LLVM pair may be labeled Certified only when exact source/target/text digests, Systems lowering root, target/runtime-ABI/tool identities, the proof-bound PHIL-LLVM-CERT-011 predecessor certificate, PHIL-SYS-HELLO-POLICY-001 semantic authority, PHIL-LLVM-HELLO-POLICY-001 lowering authority, and the exact HelloPolicy translation-validation result are content-bound. Predecessor TranslationValidated evidence is not imported across validity scopes: only the already proof-bound CERT-011 artifact identity is bound. Provider HelloPolicy semantics, opaque reason contents and lifetime, fatal-effect runtime behavior, provider ABI conformance, LLVM implementation correctness, linking, native execution, and outer framing remain explicit external gates."
      provisionalRevision = ObligationRevision
        { revisionObligationId = ObligationId "PHIL-LLVM-CERT-012"
        , revisionId = RevisionId ""
        , revisionStatement = revisionStatement
        , revisionStatementDigest = digestText revisionStatement
        , revisionKind = "LLVMHelloPolicyValidationProofBoundCertification"
        , revisionOrigin = "HelloPolicy validation ABI v1 / proof-bound PHIL-LLVM-CERT-012"
        , revisionScope = "llvm.phase0.preopt.hello-policy-validation.proof-bound"
        , revisionRequiredAt = "certification"
        , revisionRepresentation =
            "HelloPolicy semantic SystemsArtifact -> hello-policy-validation-v1 canonical pre-optimization LLVMArtifact + proof authority"
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
        "evidence.llvm.phase0.hello-policy-validation.proof-bound.translation.validated"
      provisionalEvidence = EvidenceEntry
        { evidenceEntryId = translationEvidenceId
        , evidenceEntryDigest = Digest ""
        , evidenceObligationRevision = certificationRevisionId
        , evidenceAssuranceKind = TranslationValidated
        , evidenceRole = EvidenceRole "translation_validated"
        , evidenceProducer = "Phil.LLVM.HelloPolicyValidation.verifyHelloPolicyValidationTranslation"
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
            [ "explicit policyContext and exact recognized Hello validator operands"
            , "retained HelloPolicy runtime site and exact accepted/rejected control"
            , "rejected-only opaque provider pointer reason binding"
            , "exact validator-produced reason pointer identity into the fatal-effect primitive"
            , "exact server transport operand and terminal return"
            , "no reason wire encoding or peer protocol meaning"
            , "preservation of proof-bound BeginPolicy predecessor authority"
            , "absence of unlowered, generic, and ambient HelloPolicy state"
            ]
        , evidenceRuntimeMechanism = Nothing
        , evidenceRuntimeResidue = []
        , evidenceCostRefs = []
        }
      translationEvidence = provisionalEvidence
        { evidenceEntryDigest = deriveEvidenceEntryDigest provisionalEvidence }
      certificationRecord = Text.unlines $
        [ "phil-llvm-phase0-hello-policy-validation-certification/v1"
        , "obligation=PHIL-LLVM-CERT-012"
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
        , "external-reason-contents=opaque provider data"
        , "external-reason-lifetime=provider-owned through fail call"
        , "external-failure-semantics=runtime gate"
        , "external-llvm=LLVM 18 acceptance/link gate"
        , "external-native=native execution gate"
        , "residual-outer-framing=not defined by hello-policy-validation-v1"
        ]
      certificationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef "certificate:phil:llvm:PHIL-LLVM-CERT-012:v1"
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
        [ "phil-llvm-phase0-hello-policy-validation-proof-bound-certification-root-v1"
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
      bundle = HelloPolicyValidationProofCertificationBundle
        { helloPolicyProofBase = base
        , helloPolicyProofPredecessor = predecessor
        , helloPolicyProofArtifact = certificationArtifact
        , helloPolicyProofRecord = certificationRecord
        , helloPolicyProofLedger = ledger
        , helloPolicyProofManifest = manifest
        , helloPolicyProofContext = context
        }

  mapLeft HelloPolicyProofFinalManifestError $ verifyManifest context ledger manifest
  pure bundle

verifyPhase0HelloPolicyValidationProofCertification
  :: RocqCertificationBundle
  -> RocqCertificationBundle
  -> BeginPolicyChoiceProofCertificationBundle
  -> Either HelloPolicyValidationProofCertificationError ()
verifyPhase0HelloPolicyValidationProofCertification systemsProof llvmProof predecessor = do
  bundle <- phase0HelloPolicyValidationProofCertification systemsProof llvmProof predecessor
  mapLeft HelloPolicyProofFinalManifestError $
    verifyManifest
      (helloPolicyProofContext bundle)
      (helloPolicyProofLedger bundle)
      (helloPolicyProofManifest bundle)

renderHelloPolicyValidationProofCertification
  :: HelloPolicyValidationProofCertificationBundle
  -> Text
renderHelloPolicyValidationProofCertification = helloPolicyProofRecord

verifyProof
  :: Text
  -> RocqCertificationSpec
  -> RocqCertificationBundle
  -> Either HelloPolicyValidationProofCertificationError ()
verifyProof label spec bundle = do
  let expected = rocqSpecObligation spec
      actual = rocqCertificateObligation (rocqBundleCertificate bundle)
  unless (actual == expected) $
    Left (HelloPolicyProofWrongProof label expected actual)
  mapLeft (HelloPolicyProofManifestError label) $
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
