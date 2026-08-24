{-# LANGUAGE OverloadedStrings #-}

module Phil.Phase0UploadProjectionProofCertification
  ( phase0UploadProjectionCertificationSpec
  , Phase0UploadProjectionProofCertificationError (..)
  , Phase0UploadProjectionProofCertificationBundle (..)
  , phase0UploadProjectionProofCertification
  , verifyPhase0UploadProjectionProofCertification
  , renderPhase0UploadProjectionProofCertification
  ) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance
import Phil.Core.Syntax (ObligationId (..), unObligationId)
import Phil.LLVM
import Phil.Phase0UploadProjection
import Phil.Systems

phase0UploadProjectionCertificationSpec :: RocqCertificationSpec
phase0UploadProjectionCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "surface-systems-phase0-upload-projection"
  , rocqSpecObligation = ObligationId "PHIL-SURF-SYS-UPLOAD-PROJ-001"
  , rocqSpecClaim =
      "For the frozen Phase 0 UploadClient/UploadServer source template, successful projection requires the exact normalized client and server semantic traces; independently commits to the exact client and server source digests before labeled source-pair composition; rebinds both the canonical base Systems artifact and the verified StorageFailure successor to that exact source-pair authority without changing either Systems program; uniformly rebinds and rederives lowering-decision digests, lowering-ledger roots, assurance manifests, and verification contexts; re-verifies Systems structure and scalar dataflow after rebinding; translation-validates the rebound final Systems artifact through control-codec-v1; rejects semantic/program/source-binding drift; and makes no generic .phil-to-Systems lowering claim."
  , rocqSpecKind = "Phase 0 template-directed Surface-to-Systems source projection"
  , rocqSpecOrigin =
      "phase0-projection/src/Phil/Phase0UploadProjection.hs; docs/phase-0/source-to-systems-projection-v1.md; proof/Phil/Surface/Phase0UploadProjection.v"
  , rocqSpecScope =
      "frozen examples/upload/client.phil + examples/upload/server.phil template-directed projection"
  , rocqSpecRepresentation =
      "exact checked semantic traces + independently digested labeled source pair + source-rebound canonical base/final Systems artifacts and derived lowering/assurance identities"
  , rocqSpecSubjects =
      [ "exact UploadClient normalized semantic trace"
      , "exact UploadServer normalized semantic trace"
      , "independent client.phil digest"
      , "independent server.phil digest"
      , "labeled phil-source-pair/phase0-upload/v1 composition"
      , "unchanged canonical Phase 0 base Systems program"
      , "unchanged StorageFailure successor Systems program"
      , "uniform source binding of stage contracts and lowering decisions"
      , "rederived lowering decision digests and ledger roots"
      , "rederived assurance manifests and verification contexts"
      , "source-bound control-codec-v1 translation validation"
      ]
  , rocqSpecTheorems =
      [ "verified_phase0_upload_projection_requires_exact_frozen_traces"
      , "verified_phase0_upload_projection_binds_labeled_independent_source_digests"
      , "verified_phase0_upload_projection_preserves_both_systems_programs"
      , "verified_phase0_upload_projection_rebinds_source_authority_uniformly"
      , "verified_phase0_upload_projection_rederives_identity_metadata"
      , "verified_phase0_upload_projection_rechecks_rebound_systems_authority"
      , "verified_phase0_upload_projection_reaches_control_codec_target"
      , "verified_phase0_upload_projection_claims_no_generic_lowerer"
      , "phase0_upload_projection_client_semantic_drift_is_rejected"
      , "phase0_upload_projection_server_semantic_drift_is_rejected"
      , "phase0_upload_projection_program_drift_is_rejected"
      , "phase0_upload_projection_source_binding_drift_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Surface/Phase0UploadProjection.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Surface/Phase0UploadProjection.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-SURF-SYS-UPLOAD-PROJ-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-SURF-SYS-UPLOAD-PROJ-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness; reviewed Haskell-to-normalized-proof correspondence; Megaparsec parsing; the Haskell Surface checker and semantic-trace traversal; SHA-256 collision resistance and implementation correctness; Text/UTF-8 handling; template selection code; and the generic .phil-to-Systems compiler remain explicit trust boundaries or out of scope. This theorem is authoritative only for the frozen Phase 0 upload template."
  }

data Phase0UploadProjectionProofCertificationError
  = Phase0UploadProjectionProofProjectionError Phase0UploadProjectionError
  | Phase0UploadProjectionProofBaselineError StorageFailureError
  | Phase0UploadProjectionProofTranslationError LLVMVerificationError
  | Phase0UploadProjectionProofWrongProof ObligationId ObligationId
  | Phase0UploadProjectionProofManifestError Text ManifestError
  | Phase0UploadProjectionProofFinalManifestError ManifestError
  deriving (Eq, Show)

data Phase0UploadProjectionProofCertificationBundle =
  Phase0UploadProjectionProofCertificationBundle
    { projectionProofProjection :: Phase0UploadProjection
    , projectionProofLLVM :: LLVMArtifact
    , projectionProofArtifact :: ArtifactIdentity
    , projectionProofRecord :: Text
    , projectionProofLedger :: AssuranceLedger
    , projectionProofManifest :: AssuranceManifest
    , projectionProofContext :: VerificationContext
    }
  deriving (Eq, Show)

proofBoundCert017 :: ArtifactIdentity
proofBoundCert017 = ArtifactIdentity
  { artifactReference = ArtifactRef "certificate:phil:llvm:PHIL-LLVM-CERT-017:v1"
  , artifactDigest = Digest "790d18d2353b703b67f9c93e96492331c767308bbdcee68f898bbc4fc2ce3623"
  }

phase0UploadProjectionProofCertification
  :: RocqCertificationBundle
  -> Text
  -> Text
  -> Text
  -> Either
      Phase0UploadProjectionProofCertificationError
      Phase0UploadProjectionProofCertificationBundle
phase0UploadProjectionProofCertification proofBundle projectionImplementationSource clientSource serverSource = do
  verifyProof phase0UploadProjectionCertificationSpec proofBundle
  projection <- mapLeft Phase0UploadProjectionProofProjectionError $
    projectPhase0UploadSources clientSource serverSource
  mapLeft Phase0UploadProjectionProofProjectionError $
    verifyPhase0UploadProjection projection
  baseline <- mapLeft Phase0UploadProjectionProofBaselineError phase0StorageFailureBundle

  let finalArtifact = phase0ProjectionFinalArtifact projection
      finalContext = phase0ProjectionFinalContext projection
      llvmArtifact = lowerSystemsControlCodec phase0ControlCodecLLVMTarget finalArtifact
      llvmContext =
        (phase0ControlCodecLLVMVerificationContext baseline)
          { llvmSystemsContext = finalContext }
  mapLeft Phase0UploadProjectionProofTranslationError $
    verifyLLVMEmissionWith lowerSystemsControlCodec llvmContext finalArtifact llvmArtifact

  let proofLedger = rocqBundleLedger proofBundle
      proofRevisionId = rocqCertificateRevision (rocqBundleCertificate proofBundle)
      proofArtifact = rocqBundleCertificateArtifact proofBundle
      proofDigest = artifactDigest proofArtifact
      sourcePairDigest = phase0ProjectionSourceDigest projection
      clientSourceDigest = digestText clientSource
      serverSourceDigest = digestText serverSource
      projectionImplementationDigest = digestText projectionImplementationSource
      systemsDigest = systemsArtifactDigest finalArtifact
      systemsProgramIdentity = systemsProgramDigest (systemsArtifactProgram finalArtifact)
      systemsLoweringRoot = loweringLedgerRoot (systemsArtifactLoweringLedger finalArtifact)
      systemsManifest = systemsAssuranceManifest finalContext
      stageContract = systemsArtifactStageContract finalArtifact
      moduleValue = llvmArtifactModule llvmArtifact
      llvmSourceDigest = llvmContractSourceDigest (llvmArtifactContract llvmArtifact)
      targetDigest = llvmContractTargetDigest (llvmArtifactContract llvmArtifact)
      targetTextDigest = digestText (llvmArtifactText llvmArtifact)
      abiDigest = llvmRuntimeABIDigest moduleValue
      certificationTarget = "preopt-llvm:" <> llvmTargetTriple moduleValue
      sourceCompilationProfile = Text.pack (show (llvmCompilationProfile moduleValue))
      certificationProfile =
        "translation-validation/" <> sourceCompilationProfile <>
        "/phase0-upload-source-bound/control-codec-v1/proof-bound"
      validityContext = Map.fromList
        [ ("source_projection", "surface-to-systems/phase0-upload/v1")
        , ("source_pair_digest", unDigest sourcePairDigest)
        , ("client_source_digest", unDigest clientSourceDigest)
        , ("server_source_digest", unDigest serverSourceDigest)
        , ("projection_implementation_digest", unDigest projectionImplementationDigest)
        , ("projected_systems_digest", unDigest systemsDigest)
        , ("projected_systems_program_digest", unDigest systemsProgramIdentity)
        , ("systems_lowering_ledger_root", unDigest systemsLoweringRoot)
        , ("llvm_source_contract_digest", unDigest llvmSourceDigest)
        , ("target_digest", unDigest targetDigest)
        , ("target_text_digest", unDigest targetTextDigest)
        , ("llvm_language", llvmLanguageVersion moduleValue)
        , ("llvm_tool_profile", llvmToolVersion moduleValue)
        , ("target_triple", llvmTargetTriple moduleValue)
        , ("data_layout", llvmDataLayout moduleValue)
        , ("runtime_abi_digest", unDigest abiDigest)
        , ("runtime_abi_profile", llvmRuntimeABIProfile moduleValue)
        , ("systems_compilation_profile", sourceCompilationProfile)
        , ("predecessor_cert017", unDigest (artifactDigest proofBoundCert017))
        , ("projection_proof_certificate", unDigest proofDigest)
        , ("proof_assistant", "Rocq")
        , ("rocq_version", "9.2.0")
        , ("certificate_profile", "proof-assistant-theorem/v1")
        , ("template_scope", "frozen-phase0-upload-client+server")
        , ("generic_source_lowerer", "not claimed")
        ]
      evidenceScope = ValidityScope $
        Map.insert "target" certificationTarget $
        Map.insert "compilation_profile" certificationProfile validityContext
      revisionStatement =
        "The frozen Phase 0 UploadClient/UploadServer source pair may be labeled as the Certified source authority for the control-codec-v1 backend chain only when the exact client/server source digests and labeled source-pair digest, source-projection implementation identity, rebound final Systems artifact/program identity, rederived Systems lowering root, target/text/runtime-ABI/tool identities, proof-bound PHIL-LLVM-CERT-017 physical predecessor artifact, PHIL-SURF-SYS-UPLOAD-PROJ-001 proof authority, and a fresh verifyLLVMEmissionWith result over the rebound Systems context are content-bound. CERT-017's prior TranslationValidated evidence is not imported across the changed Systems/source validity scope. The claim is limited to the frozen Phase 0 upload template and does not establish a generic .phil-to-Systems compiler, operating-system I/O, or the final integrated native upload demonstrator."
      provisionalRevision = ObligationRevision
        { revisionObligationId = ObligationId "PHIL-LLVM-CERT-018"
        , revisionId = RevisionId ""
        , revisionStatement = revisionStatement
        , revisionStatementDigest = digestText revisionStatement
        , revisionKind = "LLVMPhase0SourceBoundProjectionCertification"
        , revisionOrigin = "source-to-systems projection v1 / proof-bound PHIL-LLVM-CERT-018"
        , revisionScope = "llvm.phase0.preopt.control-codec.source-bound.proof-bound"
        , revisionRequiredAt = "certification"
        , revisionRepresentation =
            "exact frozen .phil source pair -> template-directed rebound StorageFailure SystemsArtifact -> control-codec-v1 canonical pre-optimization LLVMArtifact + projection proof authority"
        , revisionSubjectIds =
            [ "source-pair:" <> unDigest sourcePairDigest
            , "client-source:" <> unDigest clientSourceDigest
            , "server-source:" <> unDigest serverSourceDigest
            , "projection-implementation:" <> unDigest projectionImplementationDigest
            , "systems:" <> unDigest systemsDigest
            , "systems-program:" <> unDigest systemsProgramIdentity
            , "systems-lowering-root:" <> unDigest systemsLoweringRoot
            , "llvm-source-contract:" <> unDigest llvmSourceDigest
            , "llvm:" <> unDigest targetDigest
            , "llvm-text:" <> unDigest targetTextDigest
            , "runtime-abi:" <> unDigest abiDigest
            , "predecessor-cert017:" <> unDigest (artifactDigest proofBoundCert017)
            , "projection-proof-certificate:" <> unDigest proofDigest
            ]
        , revisionContextIds =
            [ "stage-contract:" <> stageContractId stageContract
            , "language:" <> llvmLanguageVersion moduleValue
            , "tool-profile:" <> llvmToolVersion moduleValue
            , "target:" <> llvmTargetTriple moduleValue
            , "layout:" <> llvmDataLayout moduleValue
            , "runtime-abi-profile:" <> llvmRuntimeABIProfile moduleValue
            , "compilation-profile:" <> sourceCompilationProfile
            , "template:frozen-phase0-upload-client+server"
            , "rocq:9.2.0"
            ]
        , revisionAcceptanceRule =
            AcceptEntry TranslationValidated (EvidenceRole "translation_validated")
        , revisionGeneratedFrom = [proofRevisionId]
        }
      certificationRevision = provisionalRevision
        { revisionId = deriveRevisionId provisionalRevision }
      certificationRevisionId = revisionId certificationRevision
      translationArtifactRecord = Text.unlines
        [ "phil-llvm-phase0-source-bound-control-codec-translation-validation/v1"
        , "source-projection=surface-to-systems/phase0-upload/v1"
        , "source-pair-digest=" <> unDigest sourcePairDigest
        , "client-source-digest=" <> unDigest clientSourceDigest
        , "server-source-digest=" <> unDigest serverSourceDigest
        , "projection-implementation-digest=" <> unDigest projectionImplementationDigest
        , "projected-systems-digest=" <> unDigest systemsDigest
        , "projected-systems-program-digest=" <> unDigest systemsProgramIdentity
        , "systems-lowering-root=" <> unDigest systemsLoweringRoot
        , "llvm-source-contract-digest=" <> unDigest llvmSourceDigest
        , "target-digest=" <> unDigest targetDigest
        , "target-text-digest=" <> unDigest targetTextDigest
        , "runtime-abi-profile=" <> llvmRuntimeABIProfile moduleValue
        , "runtime-abi-digest=" <> unDigest abiDigest
        , "predecessor-cert017=" <> unDigest (artifactDigest proofBoundCert017)
        , "projection-proof-certificate=" <> unDigest proofDigest
        , "translation-validator=Phil.LLVM.Verify.verifyLLVMEmissionWith(lowerSystemsControlCodec,projected-context)"
        ]
      translationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef
            "artifact:phil:llvm:phase0:source-bound-control-codec:translation-validation:v1"
        , artifactDigest = digestText translationArtifactRecord
        }
      evidenceId = EvidenceEntryId
        "evidence.llvm.phase0.source-bound-control-codec.proof-bound.translation.validated"
      provisionalEvidence = EvidenceEntry
        { evidenceEntryId = evidenceId
        , evidenceEntryDigest = Digest ""
        , evidenceObligationRevision = certificationRevisionId
        , evidenceAssuranceKind = TranslationValidated
        , evidenceRole = EvidenceRole "translation_validated"
        , evidenceProducer =
            "Phil.Phase0UploadProjection.projectPhase0UploadSources + Phil.LLVM.Verify.verifyLLVMEmissionWith"
        , evidenceChecker = "Phil.Assurance.Verify.verifyManifest"
        , evidenceArtifact = Just translationArtifact
        , evidenceInputDigests =
            [ sourcePairDigest
            , clientSourceDigest
            , serverSourceDigest
            , projectionImplementationDigest
            , systemsDigest
            , systemsProgramIdentity
            , systemsLoweringRoot
            , llvmSourceDigest
            , targetDigest
            , targetTextDigest
            , abiDigest
            , artifactDigest proofBoundCert017
            , proofDigest
            ]
        , evidenceAssumptions = []
        , evidenceDependsOn = [DependsOnObligation proofRevisionId]
        , evidenceValidityScope = evidenceScope
        , evidenceResult = EvidenceAccepted
        , evidenceJustifies =
            [ "the exact frozen client/server sources are content-bound independently and as a labeled pair"
            , "the source-bound final Systems program is exactly the verified StorageFailure successor program"
            , "all rebound Systems lowering decisions carry the exact source-pair authority and rederived identities"
            , "the rebound Systems artifact and scalar dataflow verify under its rederived assurance context"
            , "the exact source-bound final Systems artifact translation-validates through control-codec-v1"
            , "proof-bound CERT-017 supplies predecessor physical/profile authority without transferring its old TranslationValidated source scope"
            , "generic source lowering, operating-system I/O and the integrated native upload demonstrator remain outside this claim"
            ]
        , evidenceRuntimeMechanism = Nothing
        , evidenceRuntimeResidue = []
        , evidenceCostRefs = []
        }
      translationEvidence = provisionalEvidence
        { evidenceEntryDigest = deriveEvidenceEntryDigest provisionalEvidence }
      certificationRecord = Text.unlines
        [ "phil-llvm-phase0-source-bound-control-codec-certification/v1"
        , "obligation=PHIL-LLVM-CERT-018"
        , "revision=" <> unRevisionId certificationRevisionId
        , "source-projection=surface-to-systems/phase0-upload/v1"
        , "source-pair-digest=" <> unDigest sourcePairDigest
        , "client-source-digest=" <> unDigest clientSourceDigest
        , "server-source-digest=" <> unDigest serverSourceDigest
        , "projection-implementation-digest=" <> unDigest projectionImplementationDigest
        , "projected-systems-digest=" <> unDigest systemsDigest
        , "projected-systems-program-digest=" <> unDigest systemsProgramIdentity
        , "systems-lowering-root=" <> unDigest systemsLoweringRoot
        , "llvm-source-contract-digest=" <> unDigest llvmSourceDigest
        , "target-digest=" <> unDigest targetDigest
        , "target-text-digest=" <> unDigest targetTextDigest
        , "runtime-abi-profile=" <> llvmRuntimeABIProfile moduleValue
        , "runtime-abi-digest=" <> unDigest abiDigest
        , "translation-artifact=" <> renderArtifact translationArtifact
        , "predecessor-cert017=" <> renderArtifact proofBoundCert017
        , "projection-proof="
            <> unObligationId (rocqCertificateObligation (rocqBundleCertificate proofBundle))
            <> ";artifact=" <> unArtifactRef (artifactReference proofArtifact)
            <> ";sha256=" <> unDigest proofDigest
        , "scope=frozen Phase 0 upload template only"
        , "generic-source-lowering=not claimed"
        , "integrated-native-upload=outside this certification scope"
        ]
      certificationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef "certificate:phil:llvm:PHIL-LLVM-CERT-018:v1"
        , artifactDigest = digestText certificationRecord
        }
      revisions = Map.insert certificationRevisionId certificationRevision
        (ledgerRevisions proofLedger)
      evidence = Map.insert evidenceId translationEvidence (ledgerEvidence proofLedger)
      obligationIds = Set.insert certificationRevisionId (Map.keysSet revisions)
      evidenceIds = Set.insert evidenceId (Map.keysSet evidence)
      ledger = emptyLedger
        { ledgerRevisions = revisions
        , ledgerEvidence = evidence
        }
      certificationRoot = digestText $ Text.intercalate "|"
        [ "phil-llvm-phase0-source-bound-control-codec-proof-bound-certification-root-v1"
        , unDigest sourcePairDigest
        , unDigest clientSourceDigest
        , unDigest serverSourceDigest
        , unDigest projectionImplementationDigest
        , unDigest systemsDigest
        , unDigest systemsLoweringRoot
        , unDigest llvmSourceDigest
        , unDigest targetDigest
        , unDigest targetTextDigest
        , unDigest abiDigest
        , unDigest (artifactDigest proofBoundCert017)
        , unDigest proofDigest
        ]
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
      explicitArtifacts =
        [ translationArtifact
        , certificationArtifact
        , proofBoundCert017
        , proofArtifact
        ]
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
      result = Phase0UploadProjectionProofCertificationBundle
        { projectionProofProjection = projection
        , projectionProofLLVM = llvmArtifact
        , projectionProofArtifact = certificationArtifact
        , projectionProofRecord = certificationRecord
        , projectionProofLedger = ledger
        , projectionProofManifest = manifest
        , projectionProofContext = context
        }

  mapLeft Phase0UploadProjectionProofFinalManifestError $
    verifyManifest context ledger manifest
  pure result

verifyPhase0UploadProjectionProofCertification
  :: RocqCertificationBundle
  -> Text
  -> Text
  -> Text
  -> Either Phase0UploadProjectionProofCertificationError ()
verifyPhase0UploadProjectionProofCertification proofBundle projectionImplementationSource clientSource serverSource = do
  bundle <- phase0UploadProjectionProofCertification
    proofBundle projectionImplementationSource clientSource serverSource
  mapLeft Phase0UploadProjectionProofFinalManifestError $
    verifyManifest
      (projectionProofContext bundle)
      (projectionProofLedger bundle)
      (projectionProofManifest bundle)

renderPhase0UploadProjectionProofCertification
  :: Phase0UploadProjectionProofCertificationBundle
  -> Text
renderPhase0UploadProjectionProofCertification = projectionProofRecord

verifyProof
  :: RocqCertificationSpec
  -> RocqCertificationBundle
  -> Either Phase0UploadProjectionProofCertificationError ()
verifyProof spec bundle = do
  let expected = rocqSpecObligation spec
      actual = rocqCertificateObligation (rocqBundleCertificate bundle)
  unless (actual == expected) $
    Left (Phase0UploadProjectionProofWrongProof expected actual)
  mapLeft (Phase0UploadProjectionProofManifestError "phase0-upload-source-projection") $
    verifyManifest
      (rocqBundleVerificationContext bundle)
      (rocqBundleLedger bundle)
      (rocqBundleManifest bundle)

renderArtifact :: ArtifactIdentity -> Text
renderArtifact artifact =
  unArtifactRef (artifactReference artifact) <> ";sha256=" <> unDigest (artifactDigest artifact)

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
