{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.ByteString as ByteString
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TextEncoding
import Phil.Assurance
import Phil.Core.Syntax (ObligationId (..))
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [sourcePath, compiledPath, outputPath] ->
      certifyWith phase1ProviderLineageTargetCertificationSpec
        sourcePath compiledPath outputPath
    _ -> do
      hPutStrLn stderr
        "usage: Phase1ProviderLineageTargetCertificationMain SOURCE.v COMPILED.vo OUTPUT.cert"
      exitFailure

phase1ProviderLineageTargetCertificationSpec :: RocqCertificationSpec
phase1ProviderLineageTargetCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "phase1-provider-lineage-target"
  , rocqSpecObligation = ObligationId "PHIL-PROV-LINEAGE-TARGET-001"
  , rocqSpecClaim =
      "A semantic provider qualification may be reused across distinct target profiles only when both target-realization evidence bundles bind the exact semantic claim, required interface, and implementation and each carries target-specific translation evidence. Concrete provider admission applies to a selected ArchitectureRealization only when the admission is accepted and the admission, claim, target evidence, provider occurrence, architecture instance and realization, interface, implementation, target profile, artifact, and runtime ABI all match exactly; exported symbol names are nonsemantic metadata."
  , rocqSpecKind = "Provider cross-target semantic reuse and concrete admission applicability"
  , rocqSpecOrigin =
      "src/Phil/Core/ProviderQualificationTargetReuse.hs; src/Phil/Core/ProviderQualificationApplicability.hs; test/Phase1ProviderQualificationTargetReuseMain.hs; test/Phase1ProviderQualificationApplicabilityMain.hs; proof/Phil/Core/ProviderQualificationLineageTarget.v"
  , rocqSpecScope =
      "Phase 1 PROV-013 cross-target semantic qualification reuse plus PROV-014 exact concrete admission applicability"
  , rocqSpecRepresentation =
      "normalized exact semantic claim/interface/implementation identities, target realization evidence, accepted admission identity, provider requirement occurrence, ArchitectureInstance/ArchitectureRealization identity, target profile, artifact, runtime ABI, and nonsemantic exported-symbol metadata"
  , rocqSpecSubjects =
      [ "ProviderQualificationClaim"
      , "ProviderTargetRealizationEvidence"
      , "TargetEvidenceMatches"
      , "CrossTargetSemanticReuse"
      , "CheckedProviderQualificationAdmission"
      , "ProviderConcreteAdmissionApplicability"
      , "SelectedProviderRealization"
      , "AdmissionApplicable"
      ]
  , rocqSpecTheorems =
      [ "target_evidence_binds_exact_claim_revision"
      , "target_evidence_binds_exact_required_interface"
      , "target_evidence_binds_exact_semantic_implementation"
      , "target_evidence_requires_translation_evidence"
      , "cross_target_reuse_requires_semantic_layer"
      , "cross_target_reuse_requires_semantic_subject"
      , "cross_target_reuse_preserves_exact_claim_revision"
      , "cross_target_reuse_preserves_exact_interface"
      , "cross_target_reuse_preserves_exact_implementation"
      , "cross_target_reuse_requires_fresh_translation_bindings"
      , "cross_target_reuse_requires_distinct_profiles"
      , "same_target_is_not_cross_target_reuse"
      , "concrete_claim_cannot_masquerade_as_semantic_reuse"
      , "missing_new_target_translation_evidence_rejects"
      , "target_specific_assumption_is_downstream_of_semantic_match"
      , "applicability_requires_admitted_qualification"
      , "applicability_binds_exact_admission_and_claim"
      , "applicability_binds_exact_target_evidence"
      , "applicability_binds_exact_interface_implementation_target"
      , "applicability_binds_exact_artifact_and_abi"
      , "selected_realization_binds_exact_lineage"
      , "selected_realization_binds_exact_architecture"
      , "selected_realization_binds_exact_provider_target"
      , "selected_realization_binds_exact_artifact_abi"
      , "rejected_admission_cannot_justify_realization"
      , "exported_symbol_rename_is_nonsemantic_to_applicability"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Core/ProviderQualificationLineageTarget.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Core/ProviderQualificationLineageTarget.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-PROV-LINEAGE-TARGET-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-PROV-LINEAGE-TARGET-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "This theorem family certifies the normalized PROV-013/014 semantic core, not concrete canonical SemanticForm serialization, content-addressed revision digest construction, Set/Map canonicalization, or exact Haskell diagnostic ordering. Reviewed correspondence from concrete Text and revision wrappers into the normalized identities remains a trust boundary. Truth and completeness of target translation-validation evidence, artifact identity, target-profile and runtime-ABI facts, target assumptions, and realization-relation evidence remain explicit evidence/TCB facts rather than being proven here. ArchitectureRealization construction, Systems/StageContract preservation, provider replacement, backend correctness, and deployment/runtime enforcement remain separate obligations."
  }

certifyWith :: RocqCertificationSpec -> FilePath -> FilePath -> FilePath -> IO ()
certifyWith spec sourcePath compiledPath outputPath = do
  sourceBytes <- ByteString.readFile sourcePath
  compiledBytes <- ByteString.readFile compiledPath
  case certifyRocqProof spec sourceBytes compiledBytes of
    Left err -> do
      hPutStrLn stderr ("Rocq certification failed: " <> show err)
      exitFailure
    Right bundle -> do
      let certificate = rocqBundleCertificate bundle
          artifact = rocqBundleCertificateArtifact bundle
          ObligationId obligation = rocqCertificateObligation certificate
      ByteString.writeFile outputPath
        (TextEncoding.encodeUtf8 (renderRocqProofCertificate certificate))
      putStrLn
        ("certified " <> Text.unpack obligation <>
          " as ProofAssistantTheorem evidence")
      putStrLn
        ("certificate artifact: " <>
          Text.unpack (unArtifactRef (artifactReference artifact)))
      putStrLn
        ("certificate sha256: " <>
          Text.unpack (unDigest (artifactDigest artifact)))
