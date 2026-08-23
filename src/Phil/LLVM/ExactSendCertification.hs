{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.ExactSendCertification
  ( ExactSendCertificationError (..)
  , ExactSendCertificationBundle (..)
  , phase0ExactSendLLVMCertification
  , verifyPhase0ExactSendLLVMCertification
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Assurance.Types
import Phil.Assurance.Verify (ManifestError, verifyManifest)
import Phil.Core.Syntax (ObligationId (..))
import Phil.LLVM.ExactSend
import Phil.LLVM.IR
import Phil.Systems.HelloPolicyValidation
import Phil.Systems.Verify (SystemsVerificationContext (..))

data ExactSendCertificationError
  = ExactSendCertificationSystemsError HelloPolicyValidationError
  | ExactSendCertificationTranslationError ExactSendLLVMError
  | ExactSendCertificationManifestError ManifestError
  deriving (Eq, Show)

data ExactSendCertificationBundle = ExactSendCertificationBundle
  { exactSendCertificationSystems :: HelloPolicyValidationBundle
  , exactSendCertificationLLVM :: LLVMArtifact
  , exactSendCertificationArtifact :: ArtifactIdentity
  , exactSendCertificationLedger :: AssuranceLedger
  , exactSendCertificationManifest :: AssuranceManifest
  , exactSendCertificationContext :: VerificationContext
  }
  deriving (Eq, Show)

-- PHIL-LLVM-CERT-013
-- Translation-only authority for transport-exact-send-v1. Provider send
-- completion/non-return behavior, opaque-buffer implementation, LLVM 18,
-- linking, and native execution remain independent gates.
phase0ExactSendLLVMCertification
  :: Either ExactSendCertificationError ExactSendCertificationBundle
phase0ExactSendLLVMCertification = do
  systemsBundle <- mapLeft ExactSendCertificationSystemsError phase0HelloPolicyValidationBundle
  let systemsArtifact = helloPolicyValidationArtifact systemsBundle
      llvmArtifact = lowerSystemsExactSend phase0ExactSendLLVMTarget systemsArtifact
  mapLeft ExactSendCertificationTranslationError $
    verifyExactSendTranslation systemsBundle llvmArtifact
  let systemsManifest = systemsAssuranceManifest (helloPolicyValidationContext systemsBundle)
      moduleValue = llvmArtifactModule llvmArtifact
      sourceDigest = llvmContractSourceDigest (llvmArtifactContract llvmArtifact)
      targetDigest = llvmContractTargetDigest (llvmArtifactContract llvmArtifact)
      targetTextDigest = digestText (llvmArtifactText llvmArtifact)
      abiDigest = llvmRuntimeABIDigest moduleValue
      certificationTarget = "preopt-llvm:" <> llvmTargetTriple moduleValue
      sourceCompilationProfile = Text.pack (show (llvmCompilationProfile moduleValue))
      certificationProfile =
        "translation-validation/" <> sourceCompilationProfile <> "/transport-exact-send-v1"
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
        , ("client_transport", "existing UploadClient ptr parameter")
        , ("client_payload_source", "client.payload : OwnedBuffer")
        , ("client_payload_target", "client.payload.owner : explicit ptr parameter")
        , ("client_payload_relation", "client.payload -> client.payload.owner")
        , ("send", "phil_runtime_send_exact(ptr,ptr)->void")
        , ("send_failure", "must not return normally; source has no failure edge")
        , ("payload_ownership", "consumed on normal return")
        , ("payload_copy", "none required by translation")
        , ("ambient_state", "forbidden")
        , ("provider_send_semantics", "external runtime gate")
        , ("external_llvm_gate", "canonical target text must be accepted by LLVM 18 in CI")
        ]
      evidenceScope = ValidityScope $
        Map.insert "target" certificationTarget $
        Map.insert "compilation_profile" certificationProfile validityContext
      revisionStatement =
        "The canonical Phase 0 exact-send Systems -> pre-optimization LLVM pair is certified only for the exact source, target, target text, target profile, and phil-runtime/phase0/transport-exact-send-v1 ABI bound by this revision; Phil translation validation establishes the exact client transport source identity, the explicit source client.payload -> target client.payload.owner owned-buffer relation, preservation of the exact send runtime site, one explicit phil_runtime_send_exact(ptr,ptr) call, preservation of the already-lowered HelloPolicy/BeginPolicy/version machinery, and absence of ambient or generic exact-send state, while provider whole-send completion/non-return behavior, opaque payload-handle implementation, OS/socket buffering, physical I/O, LLVM 18, linking, and native execution remain external gates."
      provisionalRevision = ObligationRevision
        { revisionObligationId = ObligationId "PHIL-LLVM-CERT-013"
        , revisionId = RevisionId ""
        , revisionStatement = revisionStatement
        , revisionStatementDigest = digestText revisionStatement
        , revisionKind = "LLVMExactSendTranslationCertification"
        , revisionOrigin = "transport exact-send ABI v1 / PHIL-LLVM-CERT-013"
        , revisionScope = "llvm.phase0.preopt.transport-exact-send.translation"
        , revisionRequiredAt = "certification"
        , revisionRepresentation =
            "exact-send Systems runtime site -> explicit transport + opaque owned-buffer runtime primitive canonical pre-optimization LLVMArtifact"
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
        [ "phil-llvm-phase0-transport-exact-send-translation-validation-v1"
        , "source-digest=" <> unDigest sourceDigest
        , "target-digest=" <> unDigest targetDigest
        , "target-text-digest=" <> unDigest targetTextDigest
        , "llvm-language=" <> llvmLanguageVersion moduleValue
        , "llvm-tool-profile=" <> llvmToolVersion moduleValue
        , "target-triple=" <> llvmTargetTriple moduleValue
        , "data-layout=" <> llvmDataLayout moduleValue
        , "runtime-abi-digest=" <> unDigest abiDigest
        , "runtime-abi-profile=" <> llvmRuntimeABIProfile moduleValue
        , "translation-validator=Phil.LLVM.ExactSend.verifyExactSendTranslation"
        , "assurance-checker=Phil.Assurance.Verify.verifyManifest"
        ]
      translationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef
            "artifact:phil:llvm:phase0:transport-exact-send:translation-validation:v1"
        , artifactDigest = digestText translationArtifactRecord
        }
      evidenceId = EvidenceEntryId "evidence.llvm.phase0.transport-exact-send.translation.validated"
      provisionalEvidence = EvidenceEntry
        { evidenceEntryId = evidenceId
        , evidenceEntryDigest = Digest ""
        , evidenceObligationRevision = certificationRevisionId
        , evidenceAssuranceKind = TranslationValidated
        , evidenceRole = EvidenceRole "translation_validated"
        , evidenceProducer = "Phil.LLVM.ExactSend.verifyExactSendTranslation"
        , evidenceChecker = "Phil.Assurance.Verify.verifyManifest"
        , evidenceArtifact = Just translationArtifact
        , evidenceInputDigests = [sourceDigest, targetDigest, targetTextDigest, abiDigest]
        , evidenceAssumptions = []
        , evidenceDependsOn = []
        , evidenceValidityScope = evidenceScope
        , evidenceResult = EvidenceAccepted
        , evidenceJustifies =
            [ "UploadClient carries the exact source transport as an explicit pointer parameter"
            , "source client.payload is represented by the explicit target parameter client.payload.owner"
            , "the source-to-target payload relation is checked explicitly rather than inferred from spelling"
            , "the exact payload-send runtime site is retained in LLVM"
            , "send_exact lowers to exactly one phil_runtime_send_exact call with exact transport and mapped payload identities"
            , "no payload-copy operation is introduced by translation"
            , "the prior HelloPolicy/BeginPolicy/version physical lowering remains intact"
            , "ambient transport/payload state and generic exact-send symbols are absent"
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
        [ "phil-llvm-phase0-transport-exact-send-certification-root-v1"
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
  pure ExactSendCertificationBundle
    { exactSendCertificationSystems = systemsBundle
    , exactSendCertificationLLVM = llvmArtifact
    , exactSendCertificationArtifact = translationArtifact
    , exactSendCertificationLedger = ledger
    , exactSendCertificationManifest = manifest
    , exactSendCertificationContext = verificationContext
    }

verifyPhase0ExactSendLLVMCertification
  :: Either ExactSendCertificationError ()
verifyPhase0ExactSendLLVMCertification = do
  bundle <- phase0ExactSendLLVMCertification
  mapLeft ExactSendCertificationManifestError $
    verifyManifest
      (exactSendCertificationContext bundle)
      (exactSendCertificationLedger bundle)
      (exactSendCertificationManifest bundle)

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
