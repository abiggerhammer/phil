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
      certifyWith phase1ProviderReplacementCertificationSpec
        sourcePath compiledPath outputPath
    _ -> do
      hPutStrLn stderr
        "usage: Phase1ProviderReplacementCertificationMain SOURCE.v COMPILED.vo OUTPUT.cert"
      exitFailure

phase1ProviderReplacementCertificationSpec :: RocqCertificationSpec
phase1ProviderReplacementCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "phase1-provider-replacement"
  , rocqSpecObligation = ObligationId "PHIL-PROV-REPLACE-001"
  , rocqSpecClaim =
      "Provider replacement is independently requalified rather than inherited: predecessor and replacement admissions are separately accepted, the exact public provider interface, provider occurrence, and ArchitectureInstance remain fixed, while provider subject, ArchitectureRealization, claim revision, evidence revision, and admission revision change. Evidence references shared between the two qualifications require an explicit reuse justification bound to the exact reference and both exact claim revisions under a nonempty validity scope; unscoped or spurious reuse is rejected."
  , rocqSpecKind = "Independent provider replacement and explicit cross-claim evidence reuse"
  , rocqSpecOrigin =
      "src/Phil/Core/ProviderReplacementQualification.hs; test/Phase1ProviderReplacementQualificationMain.hs; docs/phase-1/provider-replacement-qualification-v1.md; proof/Phil/Core/ProviderReplacementQualification.v"
  , rocqSpecScope =
      "Phase 1 PROV-015 independent provider replacement, lineage noninheritance, and explicit evidence-reuse scope"
  , rocqSpecRepresentation =
      "normalized admitted predecessor/replacement subjects with exact provider interface, occurrence, ArchitectureInstance/ArchitectureRealization, claim/evidence/admission revisions, evidence-reference membership, and exact cross-claim reuse witnesses"
  , rocqSpecSubjects =
      [ "ProviderReplacementSide"
      , "ProviderReplacementEvidenceReuse"
      , "SharedEvidence"
      , "ValidEvidenceReuse"
      , "ValidProviderReplacement"
      ]
  , rocqSpecTheorems =
      [ "prior_side_is_independently_admitted"
      , "replacement_side_is_independently_admitted"
      , "replacement_preserves_public_interface"
      , "replacement_preserves_provider_occurrence"
      , "replacement_preserves_architecture_instance"
      , "replacement_requires_distinct_subject"
      , "replacement_requires_new_realization_revision"
      , "replacement_requires_new_claim_lineage"
      , "replacement_requires_new_evidence_lineage"
      , "replacement_requires_new_admission_lineage"
      , "same_subject_cannot_be_replacement"
      , "unchanged_realization_cannot_be_replacement"
      , "inherited_claim_lineage_cannot_be_replacement"
      , "inherited_evidence_lineage_cannot_be_replacement"
      , "inherited_admission_lineage_cannot_be_replacement"
      , "rejected_replacement_cannot_be_selected"
      , "shared_evidence_requires_explicit_reuse"
      , "shared_evidence_without_reuse_rejects"
      , "reuse_requires_nonempty_validity_scope"
      , "reuse_binds_exact_claim_pair"
      , "reuse_justification_names_actually_shared_evidence"
      , "unexpected_reuse_justification_cannot_validate"
      , "qualification_layer_is_not_a_replacement_invariant"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Core/ProviderReplacementQualification.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Core/ProviderReplacementQualification.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-PROV-REPLACE-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-PROV-REPLACE-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "This theorem family certifies the normalized PROV-015 replacement semantics, not concrete canonical SemanticForm serialization, content-addressed claim/evidence/admission revision construction, Text/Map/Set canonicalization, evidence-reference enumeration, or exact Haskell diagnostic ordering. The truth and adequacy of a declared cross-claim evidence validity scope remain explicit evidence/admission facts rather than being proven here. Provider semantic correctness, ABI/confinement/translation/runtime evidence, actual ArchitectureRealization construction, Systems/StageContract preservation, backend correctness, deployment enforcement, live hot swap, private-state migration, handle continuity, and in-flight operation migration remain separate obligations. Qualification layer is deliberately not preserved: independently admitted semantic, concrete, or opaque subjects may replace one another when the other exact replacement invariants hold."
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
