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
      certifyWith phase1ProviderEvidenceCertificationSpec
        sourcePath compiledPath outputPath
    _ -> do
      hPutStrLn stderr
        "usage: Phase1ProviderEvidenceCertificationMain SOURCE.v COMPILED.vo OUTPUT.cert"
      exitFailure

phase1ProviderEvidenceCertificationSpec :: RocqCertificationSpec
phase1ProviderEvidenceCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "phase1-provider-evidence-competence"
  , rocqSpecObligation = ObligationId "PHIL-PROV-EVIDENCE-001"
  , rocqSpecClaim =
      "An evidence-producing provider operation is competent only when the operation is already present in an accepted provider semantic qualification; the claim exactly matches the required proposition family, semantic parameters, stable evidence subject, and validity contract; and its observation-to-subject mapping is admissible. Direct mapping is valid only for the exact stable observation, checked observation mappings bind the exact observation and exact stable subject, scoped borrows cannot masquerade as direct stable subjects, and runtime coincidence is never sufficient subject evidence. Persistent proposition identity contains the exact required family, parameters, and stable subject and is independent of temporary observation identity."
  , rocqSpecKind = "Provider evidence-producer stable-subject competence"
  , rocqSpecOrigin =
      "src/Phil/Core/ProviderEvidenceQualification.hs::{instantiateProviderEvidenceProposition,checkProviderEvidenceProducerCompetence}; test/Phase1ProviderEvidenceQualificationMain.hs; src/Phil/Examples/Steve/ProviderQualifications.hs; test/Phase1SteveProviderQualificationMain.hs; proof/Phil/Core/ProviderQualification.v; proof/Phil/Core/ProviderEvidenceQualification.v"
  , rocqSpecScope =
      "Phase 1 PROV-010 evidence-producer competence layered on the certified PROV-001--005 provider semantic qualification"
  , rocqSpecRepresentation =
      "normalized exact provider operation identity, proposition family and parameter list, stable evidence subject, observation identity/scope, mapping class, validity contract, and persistent proposition tuple"
  , rocqSpecSubjects =
      [ "ProviderEvidenceObservation"
      , "EvidenceSubjectMapping"
      , "ProviderEvidenceProducerRequirement"
      , "ProviderEvidenceProducerCompetenceClaim"
      , "ProviderEvidenceProposition"
      ]
  , rocqSpecTheorems =
      [ "competent_evidence_operation_has_explicit_provider_correspondence"
      , "competence_requires_exact_evidence_operation"
      , "competence_requires_exact_proposition_family"
      , "competence_requires_exact_proposition_parameters"
      , "competence_requires_exact_stable_subject"
      , "competence_requires_exact_validity_contract"
      , "direct_mapping_requires_exact_stable_observation"
      , "scoped_borrow_cannot_use_direct_stable_mapping"
      , "checked_mapping_binds_exact_observation"
      , "checked_mapping_binds_exact_stable_subject"
      , "runtime_coincidence_never_establishes_subject_competence"
      , "mismatched_stable_subject_rejects_competence"
      , "competent_claim_materializes_exact_required_proposition"
      , "temporary_observation_identity_is_nonsemantic_to_proposition"
      , "competent_evidence_retains_exact_provider_lineage"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Core/ProviderEvidenceQualification.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Core/ProviderEvidenceQualification.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-PROV-EVIDENCE-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-PROV-EVIDENCE-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "PHIL-PROV-QUAL-001 supplies the imported exact provider-operation qualification substrate. The normalized proof treats proposition parameters, stable evidence subjects, observation keys/scopes, mapping revisions, validity contracts, and runtime-coincidence reasons as exact semantic identities; reviewed correspondence from concrete Text, LoanScopeKey, RefTerm/Proposition construction, Haskell Map membership, and exact diagnostics remains a trust boundary. The proof establishes competence shape and stable-subject binding, not truth of the proposition family, cryptographic correctness, truth of an externally supplied observation-to-subject mapping, or universal correctness of arbitrary observation mechanisms. The broader PHIL-DATA-SUBJECT-001 consume/reconstruct evidence-transport obligation remains separate and is not silently discharged by this provider-specific theorem. Qualification evidence/admission lineage, Systems/StageContract preservation, target ABI realization, and final syntax remain outside this bounded theorem family."
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
