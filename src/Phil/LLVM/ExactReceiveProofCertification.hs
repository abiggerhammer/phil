{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.ExactReceiveProofCertification
  ( ExactReceiveProofCertificationError (..)
  , ExactReceiveProofCertificationBundle (..)
  , phase0ExactReceiveProofCertification
  , verifyPhase0ExactReceiveProofCertification
  , renderExactReceiveProofCertification
  ) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Rocq
import Phil.Assurance.RocqExactReceive
import Phil.Assurance.RocqRecognizedRecord
import Phil.Assurance.Types
import Phil.Assurance.Verify (ManifestError, verifyManifest)
import Phil.Core.Syntax (ObligationId (..))
import Phil.LLVM.ExactReceiveCertification
import Phil.LLVM.IR
import Phil.Systems.IR
import Phil.Systems.RecognizedRecord
import Phil.Systems.Verify (SystemsVerificationContext (..))

data ExactReceiveProofCertificationError
  = ExactReceiveProofCertificationBaseError ExactReceiveCertificationError
  | ExactReceiveProofCertificationWrongProof Text ObligationId ObligationId
  | ExactReceiveProofCertificationProofManifestError Text ManifestError
  | ExactReceiveProofCertificationManifestError ManifestError
  deriving (Eq, Show)

data ExactReceiveProofCertificationBundle = ExactReceiveProofCertificationBundle
  { exactReceiveProofCertificationBase :: ExactReceiveCertificationBundle
  , exactReceiveProofCertificationArtifact :: ArtifactIdentity
  , exactReceiveProofCertificationRecord :: Text
  , exactReceiveProofCertificationLedger :: AssuranceLedger
  , exactReceiveProofCertificationManifest :: AssuranceManifest
  , exactReceiveProofCertificationContext :: VerificationContext
  }
  deriving (Eq, Show)

phase0ExactReceiveProofCertification
  :: RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> Either ExactReceiveProofCertificationError ExactReceiveProofCertificationBundle
phase0ExactReceiveProofCertification exactProof abiProof symbolProof = do
  verifyProof "llvm-exact-receive" llvmExactReceiveCertificationSpec exactProof
  verifyProof "llvm-recognized-record-abi" llvmRecognizedRecordABICertificationSpec abiProof
  verifyProof "llvm-runtime-symbol-identity" llvmRuntimeSymbolCertificationSpec symbolProof

  base <- mapLeft ExactReceiveProofCertificationBaseError
    phase0ExactReceiveLLVMCertification

  let proofBundles = [exactProof, abiProof, symbolProof]
      proofLedgers = map rocqBundleLedger proofBundles
      proofRevisions = Map.unions (map ledgerRevisions proofLedgers)
      proofEvidence = Map.unions (map ledgerEvidence proofLedgers)
      proofRevisionIds = Map.keysSet proofRevisions
      proofEvidenceIds = Map.keysSet proofEvidence
      proofArtifacts = map rocqBundleCertificateArtifact proofBundles
      proofDigests = map artifactDigest proofArtifacts

      systemsBundle = exactReceiveCertificationSystems base
      systemsArtifact = recognizedRecordArtifact systemsBundle
      systemsManifest = systemsAssuranceManifest (recognizedRecordContext systemsBundle)
      llvmArtifact = exactReceiveCertificationLLVM base
      moduleValue = llvmArtifactModule llvmArtifact
      translationArtifact = exactReceiveCertificationArtifact base
      sourceDigest = llvmContractSourceDigest (llvmArtifactContract llvmArtifact)
      targetDigest = llvmContractTargetDigest (llvmArtifactContract llvmArtifact)
      targetTextDigest = digestText (llvmArtifactText llvmArtifact)
      abiDigest = llvmRuntimeABIDigest moduleValue
      systemsLoweringRoot = loweringLedgerRoot (systemsArtifactLoweringLedger systemsArtifact)
      certificationTarget = "preopt-llvm:" <> llvmTargetTriple moduleValue
      sourceCompilationProfile = Text.pack (show (llvmCompilationProfile moduleValue))
      certificationProfile =
        "translation-validation/" <> sourceCompilationProfile <> "/transport-exact-receive-v1/proof-bound"
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
        , ("transport_representation", "Systems TransportHandle -> component-entry opaque ptr")
        , ("exact_receive_dependency", "transport:ptr, Begin.length:i64 -> {status:i8,payload:ptr}")
        , ("payload_owner_identity", "Systems exactPayloadOwner -> deterministic .owner SSA -> phil_buffer_release(ptr)")
        , ("runtime_symbol_identity", "physical primitive/signature")
        , ("ambient_transport_payload", "forbidden")
        , ("proof_assistant", "Rocq")
        , ("rocq_version", "9.2.0")
        , ("certificate_profile", "proof-assistant-theorem/v1")
        , ("external_llvm_gate", "canonical target text must be accepted by LLVM 18 in CI")
        , ("external_runtime_gate", "ABI signature conformance and executable exact-receive fixture must pass in CI")
        ]
      evidenceScope = ValidityScope $
        Map.insert "target" certificationTarget $
        Map.insert "compilation_profile" certificationProfile validityContext
      revisionStatement =
        "The transport-exact-receive-v1 Systems -> canonical pre-optimization LLVM pair may be labeled Certified only when its exact source/target/text digests, lowering identity/root, target/runtime-ABI/tool identities, exact-receive semantic proof evidence, runtime-symbol separation evidence, and translation-validation result are bound; LLVM 18 accepts the exact target and the ABI-conforming runtime gates pass; and an ADR-010 manifest closes over the selected evidence."
      provisionalRevision = ObligationRevision
        { revisionObligationId = ObligationId "PHIL-LLVM-CERT-003"
        , revisionId = RevisionId ""
        , revisionStatement = revisionStatement
        , revisionStatementDigest = digestText revisionStatement
        , revisionKind = "LLVMTransportExactReceiveProofBoundCertification"
        , revisionOrigin = "transport exact-receive ABI v1 / proof-bound PHIL-LLVM-CERT-003"
        , revisionScope = "llvm.phase0.preopt.transport-exact-receive.proof-bound"
        , revisionRequiredAt = "certification"
        , revisionRepresentation =
            "transport-explicit recognized-record SystemsArtifact -> canonical pre-optimization LLVMArtifact + proof certificates"
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
        "evidence.llvm.phase0.transport-exact-receive.proof-bound.translation.validated"
      provisionalTranslationEvidence = EvidenceEntry
        { evidenceEntryId = translationEvidenceId
        , evidenceEntryDigest = Digest ""
        , evidenceObligationRevision = certificationRevisionId
        , evidenceAssuranceKind = TranslationValidated
        , evidenceRole = EvidenceRole "translation_validated"
        , evidenceProducer = "Phil.LLVM.ExactReceive.verifyExactReceiveTranslation"
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
            [ "exact caller-supplied transport identity"
            , "exact Begin.length U64/i64 identity"
            , "exact returned payload-owner identity"
            , "exact status==1 success discipline"
            , "owner-preserving EarlyEOF and ordinary release"
            , "physical runtime symbol identity"
            , "absence of ambient transport/payload recovery"
            , "proof-bound semantic authority"
            ]
        , evidenceRuntimeMechanism = Nothing
        , evidenceRuntimeResidue = []
        , evidenceCostRefs = []
        }
      translationEvidence = provisionalTranslationEvidence
        { evidenceEntryDigest = deriveEvidenceEntryDigest provisionalTranslationEvidence }
      certificationRecord = Text.unlines $
        [ "phil-llvm-phase0-transport-exact-receive-certification/v1"
        , "obligation=PHIL-LLVM-CERT-003"
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
        , "external-runtime-gate=ABI signature conformance and executable exact-receive fixture required"
        ]
      certificationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef "certificate:phil:llvm:PHIL-LLVM-CERT-003:v1"
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
        [ "phil-llvm-phase0-transport-exact-receive-proof-bound-certification-root-v1"
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
      bundle = ExactReceiveProofCertificationBundle
        { exactReceiveProofCertificationBase = base
        , exactReceiveProofCertificationArtifact = certificationArtifact
        , exactReceiveProofCertificationRecord = certificationRecord
        , exactReceiveProofCertificationLedger = ledger
        , exactReceiveProofCertificationManifest = manifest
        , exactReceiveProofCertificationContext = verificationContext
        }

  mapLeft ExactReceiveProofCertificationManifestError $
    verifyManifest verificationContext ledger manifest
  pure bundle

verifyPhase0ExactReceiveProofCertification
  :: RocqCertificationBundle
  -> RocqCertificationBundle
  -> RocqCertificationBundle
  -> Either ExactReceiveProofCertificationError ()
verifyPhase0ExactReceiveProofCertification exactProof abiProof symbolProof = do
  bundle <- phase0ExactReceiveProofCertification exactProof abiProof symbolProof
  mapLeft ExactReceiveProofCertificationManifestError $
    verifyManifest
      (exactReceiveProofCertificationContext bundle)
      (exactReceiveProofCertificationLedger bundle)
      (exactReceiveProofCertificationManifest bundle)

renderExactReceiveProofCertification
  :: ExactReceiveProofCertificationBundle
  -> Text
renderExactReceiveProofCertification = exactReceiveProofCertificationRecord

verifyProof
  :: Text
  -> RocqCertificationSpec
  -> RocqCertificationBundle
  -> Either ExactReceiveProofCertificationError ()
verifyProof label spec bundle = do
  let expected = rocqSpecObligation spec
      actual = rocqCertificateObligation (rocqBundleCertificate bundle)
  unless (actual == expected) $
    Left (ExactReceiveProofCertificationWrongProof label expected actual)
  mapLeft (ExactReceiveProofCertificationProofManifestError label) $
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
