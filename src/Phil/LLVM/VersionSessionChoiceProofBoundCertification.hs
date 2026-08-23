{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.VersionSessionChoiceProofBoundCertification
  ( VersionSessionChoiceProofBoundCertificationError (..)
  , VersionSessionChoiceProofBoundCertificationBundle (..)
  , phase0VersionSessionChoiceProofBoundCertification
  , verifyPhase0VersionSessionChoiceProofBoundCertification
  , renderVersionSessionChoiceProofBoundCertification
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
import Phil.LLVM.IR
import Phil.LLVM.PayloadCancelChoiceProofCertification
import Phil.LLVM.VersionSessionChoiceCertification
import Phil.LLVM.VersionSessionChoiceLoweringProofCertification
import Phil.LLVM.VersionSessionChoiceProofCertification
import Phil.Systems.IR
import Phil.Systems.VersionChoiceOperands
import Phil.Systems.Verify (SystemsVerificationContext (..))

data VersionSessionChoiceProofBoundCertificationError
  = VersionProofBoundBaseError VersionSessionChoiceCertificationError
  | VersionProofBoundWrongProof Text ObligationId ObligationId
  | VersionProofBoundProofManifestError Text ManifestError
  | VersionProofBoundManifestError ManifestError
  deriving (Eq, Show)

data VersionSessionChoiceProofBoundCertificationBundle =
  VersionSessionChoiceProofBoundCertificationBundle
    { versionProofBoundBase :: VersionSessionChoiceCertificationBundle
    , versionProofBoundPredecessor :: PayloadCancelChoiceProofCertificationBundle
    , versionProofBoundArtifact :: ArtifactIdentity
    , versionProofBoundRecord :: Text
    , versionProofBoundLedger :: AssuranceLedger
    , versionProofBoundManifest :: AssuranceManifest
    , versionProofBoundContext :: VerificationContext
    }
  deriving (Eq, Show)

phase0VersionSessionChoiceProofBoundCertification
  :: RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> PayloadCancelChoiceProofCertificationBundle
  -> Either VersionSessionChoiceProofBoundCertificationError VersionSessionChoiceProofBoundCertificationBundle
phase0VersionSessionChoiceProofBoundCertification
    systemsOperandsProof llvmLoweringProof systemsVersionProof predecessor = do
  verifyProof "systems-version-operands"
    systemsVersionChoiceOperandsCertificationSpec systemsOperandsProof
  verifyProof "llvm-version-lowering"
    llvmVersionSessionChoiceLoweringCertificationSpec llvmLoweringProof
  verifyProof "systems-version-session-choice"
    systemsVersionSessionChoiceCertificationSpec systemsVersionProof

  base <- mapLeft VersionProofBoundBaseError phase0VersionSessionChoiceLLVMCertification

  let -- Only authorities compatible with the final physical artifact are direct
      -- dependencies. The #70 LLVM boundary theorem deliberately says that no
      -- physical version-choice representation exists, so it remains historical
      -- predecessor-stage evidence and is not imported into this validity scope.
      explicitProofBundles =
        [ systemsOperandsProof
        , llvmLoweringProof
        , systemsVersionProof
        ]
      proofLedgers = map rocqBundleLedger explicitProofBundles
      semanticRevisions = Map.unions (map ledgerRevisions proofLedgers)
      semanticEvidence = Map.unions (map ledgerEvidence proofLedgers)
      semanticRevisionIds = Map.keysSet semanticRevisions
      semanticEvidenceIds = Map.keysSet semanticEvidence
      proofArtifacts = map rocqBundleCertificateArtifact explicitProofBundles
      proofDigests = map artifactDigest proofArtifacts
      predecessorArtifact = payloadCancelChoiceProofCertificationArtifact predecessor

      systemsBundle = versionSessionChoiceCertificationSystems base
      systemsArtifact = versionChoiceOperandsArtifact systemsBundle
      systemsManifest = systemsAssuranceManifest (versionChoiceOperandsContext systemsBundle)
      llvmArtifact = versionSessionChoiceCertificationLLVM base
      moduleValue = llvmArtifactModule llvmArtifact
      translationArtifact = versionSessionChoiceCertificationArtifact base
      sourceDigest = llvmContractSourceDigest (llvmArtifactContract llvmArtifact)
      targetDigest = llvmContractTargetDigest (llvmArtifactContract llvmArtifact)
      targetTextDigest = digestText (llvmArtifactText llvmArtifact)
      abiDigest = llvmRuntimeABIDigest moduleValue
      systemsLoweringRoot = loweringLedgerRoot (systemsArtifactLoweringLedger systemsArtifact)
      certificationTarget = "preopt-llvm:" <> llvmTargetTriple moduleValue
      sourceCompilationProfile = Text.pack (show (llvmCompilationProfile moduleValue))
      certificationProfile =
        "translation-validation/" <> sourceCompilationProfile <>
        "/version-session-choice-v1/proof-bound"
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
        , ("server_supported", "exact explicit UploadServer runtime input")
        , ("hello_versions_projection", "exact recognized Hello.versions projection")
        , ("chooser", "phil_runtime_choose_supported(ptr,ptr,ptr)->i1")
        , ("unsupported_selector", "phil_runtime_select_unsupported(ptr)->void")
        , ("version_selector", "phil_runtime_select_version(ptr,i16)->void")
        , ("receiver", "phil_runtime_receive_version_choice(ptr,ptr)->i1")
        , ("client_refinement", "phil_runtime_refine_selected_version(ptr,i16)->i1")
        , ("wire_unsupported", "0x00")
        , ("wire_version", "0x01 followed by UInt16 big-endian")
        , ("outer_framing", "not defined by version-session-choice-v1")
        , ("proof_assistant", "Rocq")
        , ("rocq_version", "9.2.0")
        , ("certificate_profile", "proof-assistant-theorem/v1")
        , ("external_provider_choose_gate", "selected membership/disjointness semantics checked independently")
        , ("external_transport_offered_set_gate", "provider must bind exact prior-Hello offered set per transport")
        , ("external_runtime_abi_gate", "six-symbol provider signature conformance checked independently")
        , ("external_runtime_execution_gate", "chooser/encode/decode/refinement native smoke checked independently")
        , ("external_malformed_gate", "tag EOF, reserved tag and truncated UInt16 must not return normally")
        , ("external_llvm_gate", "canonical target accepted by LLVM 18 and partial linking checked independently")
        , ("residual_write_failure", "source select has no physical write-failure continuation")
        ]
      evidenceScope = ValidityScope $
        Map.insert "target" certificationTarget $
        Map.insert "compilation_profile" certificationProfile validityContext
      revisionStatement =
        "The version-session-choice-v1 Systems -> canonical pre-optimization LLVM pair may be labeled Certified only when exact source/target/text digests, Systems lowering root, target/runtime-ABI/tool identities, compatible proof-bound unsupported/version Systems semantic authority, explicit version-choice operand/provenance proof, concrete LLVM chooser/select/receive/refinement proof, proof-bound payload/cancel predecessor certification, and translation-validation result are content-bound. The #70 pre-lowering LLVM competence-boundary theorem is deliberately not imported because its no-physical-representation claim does not hold for this successor artifact. Proof-bound PHIL-LLVM-CERT-009 is regenerated and digest-bound rather than importing predecessor translation evidence outside its validity scope. Provider choose_supported set semantics, exact transport-local association with versions sent in the prior client Hello, concrete byte I/O, malformed-input non-return, physical write success, provider ABI conformance, LLVM implementation correctness, whole-program linking, and native execution remain explicit external gates."
      provisionalRevision = ObligationRevision
        { revisionObligationId = ObligationId "PHIL-LLVM-CERT-010"
        , revisionId = RevisionId ""
        , revisionStatement = revisionStatement
        , revisionStatementDigest = digestText revisionStatement
        , revisionKind = "LLVMVersionSessionChoiceProofBoundCertification"
        , revisionOrigin = "version/unsupported choice ABI v1 / proof-bound PHIL-LLVM-CERT-010"
        , revisionScope = "llvm.phase0.preopt.version-session-choice.proof-bound"
        , revisionRequiredAt = "certification"
        , revisionRepresentation =
            "explicit version-choice operand SystemsArtifact -> version-session-choice-v1 canonical pre-optimization LLVMArtifact + proof authority"
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
        "evidence.llvm.phase0.version-session-choice.proof-bound.translation.validated"
      provisionalTranslationEvidence = EvidenceEntry
        { evidenceEntryId = translationEvidenceId
        , evidenceEntryDigest = Digest ""
        , evidenceObligationRevision = certificationRevisionId
        , evidenceAssuranceKind = TranslationValidated
        , evidenceRole = EvidenceRole "translation_validated"
        , evidenceProducer = "Phil.LLVM.VersionSessionChoice.verifyVersionSessionChoiceTranslation"
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
            [ "serverSupported is an explicit no-producer Systems runtime input and LLVM parameter"
            , "recognized Hello is materialized after ingress commit and Hello.versions is projected exactly once"
            , "choose_supported receives exact serverSupported and Hello.versions operands and produces branch-local selected UInt16"
            , "server unsupported/version selectors use exact transport and exact selected-version payload"
            , "client receiver binds branch-local selected UInt16 and refinement consumes exact transport plus selected UInt16"
            , "unsupported=0x00 and version=0x01||UInt16BE are bound by the runtime ABI profile"
            , "unlowered poison, generic version calls and ambient supported/selected/transport state are absent"
            , "content-bound reproduction of proof-bound PHIL-LLVM-CERT-009 predecessor authority"
            ]
        , evidenceRuntimeMechanism = Nothing
        , evidenceRuntimeResidue = []
        , evidenceCostRefs = []
        }
      translationEvidence = provisionalTranslationEvidence
        { evidenceEntryDigest = deriveEvidenceEntryDigest provisionalTranslationEvidence }
      certificationRecord = Text.unlines $
        [ "phil-llvm-phase0-version-session-choice-certification/v1"
        , "obligation=PHIL-LLVM-CERT-010"
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
        [ "historical-predecessor-note=PHIL-LLVM-VERSION-SESSION-CHOICE-BOUNDARY-001 is intentionally not a final-artifact dependency"
        , "external-provider-choose-gate=membership/disjointness semantics required"
        , "external-transport-offered-set-gate=exact prior-Hello association required"
        , "external-runtime-abi-gate=six-symbol provider signature conformance required"
        , "external-runtime-execution-gate=chooser/encoding/decoding/refinement native smoke required"
        , "external-malformed-gate=tag EOF, reserved tag and truncated UInt16 must not return normally"
        , "external-llvm-gate=LLVM 18 acceptance and partial linking required"
        , "residual-write-failure=source select has no physical write-failure continuation"
        , "residual-outer-framing=not defined by version-session-choice-v1"
        ]
      certificationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef "certificate:phil:llvm:PHIL-LLVM-CERT-010:v1"
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
        [ "phil-llvm-phase0-version-session-choice-proof-bound-certification-root-v1"
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
      bundle = VersionSessionChoiceProofBoundCertificationBundle
        { versionProofBoundBase = base
        , versionProofBoundPredecessor = predecessor
        , versionProofBoundArtifact = certificationArtifact
        , versionProofBoundRecord = certificationRecord
        , versionProofBoundLedger = ledger
        , versionProofBoundManifest = manifest
        , versionProofBoundContext = verificationContext
        }

  mapLeft VersionProofBoundManifestError $
    verifyManifest verificationContext ledger manifest
  pure bundle

verifyPhase0VersionSessionChoiceProofBoundCertification
  :: RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> PayloadCancelChoiceProofCertificationBundle
  -> Either VersionSessionChoiceProofBoundCertificationError ()
verifyPhase0VersionSessionChoiceProofBoundCertification
    systemsOperandsProof llvmLoweringProof systemsVersionProof predecessor = do
  bundle <- phase0VersionSessionChoiceProofBoundCertification
    systemsOperandsProof llvmLoweringProof systemsVersionProof predecessor
  mapLeft VersionProofBoundManifestError $
    verifyManifest
      (versionProofBoundContext bundle)
      (versionProofBoundLedger bundle)
      (versionProofBoundManifest bundle)

renderVersionSessionChoiceProofBoundCertification :: VersionSessionChoiceProofBoundCertificationBundle -> Text
renderVersionSessionChoiceProofBoundCertification = versionProofBoundRecord

verifyProof
  :: Text
  -> RocqCertificationSpec
  -> RocqCertificationBundle
  -> Either VersionSessionChoiceProofBoundCertificationError ()
verifyProof label spec bundle = do
  let expected = rocqSpecObligation spec
      actual = rocqCertificateObligation (rocqBundleCertificate bundle)
  unless (actual == expected) $
    Left (VersionProofBoundWrongProof label expected actual)
  mapLeft (VersionProofBoundProofManifestError label) $
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
