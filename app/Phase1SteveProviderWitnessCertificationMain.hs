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
      certifyWith phase1SteveProviderWitnessCertificationSpec
        sourcePath compiledPath outputPath
    _ -> do
      hPutStrLn stderr
        "usage: Phase1SteveProviderWitnessCertificationMain SOURCE.v COMPILED.vo OUTPUT.cert"
      exitFailure

phase1SteveProviderWitnessCertificationSpec :: RocqCertificationSpec
phase1SteveProviderWitnessCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "phase1-steve-provider-witness"
  , rocqSpecObligation = ObligationId "PHIL-PROV-STEVE-WITNESS-001"
  , rocqSpecClaim =
      "The concrete Phase 1 Steve provider witness closes the bounded qualification facts exercised by PROV-016: both DigestProvider[SHA256] and BlobProvider are admitted through one generic artifact schema; DigestMatches retains its stable-id parameter and stable owner subject while the scoped borrow remains an observation; digest and blob candidate bytes remain borrowed rather than consumed; BlobProvider materializes state, no-replace law, lifecycle, and authority layers; a second installed event violates the normalized no-replace law; partial publication is client-visible forbidden; overwrite/delete backing authority remains explicitly dispositioned; evidence disposition domains exactly match declared obligations; and qualification conditions remain explicit in evidence and admission. The SHA-256 profile is an explicit condition, not a cryptographic-correctness theorem."
  , rocqSpecKind = "Concrete Steve provider qualification witness"
  , rocqSpecOrigin =
      "src/Phil/Examples/Steve/ProviderQualifications.hs; test/Phase1SteveProviderQualificationMain.hs; docs/phase-1/steve-provider-qualifications-v1.md; proof/Phil/Core/SteveProviderQualificationWitness.v"
  , rocqSpecScope =
      "Bounded Phase 1 PROV-016 DigestProvider[SHA256] and BlobProvider witness closure"
  , rocqSpecRepresentation =
      "normalized generic Steve provider artifact closure, typed stable-id/evidence-subject/scoped-borrow roles, borrow residues, BlobProvider layer-presence flags, bounded no-replace and lifecycle negative states, explicit backing-authority dispositions, exact obligation-domain equality, and explicit condition propagation"
  , rocqSpecSubjects =
      [ "SteveProviderArtifact"
      , "QualificationClosure"
      , "DigestProviderWitness"
      , "BlobProviderWitness"
      , "SteveProviderQualificationWitness"
      , "BorrowPreserved"
      ]
  , rocqSpecTheorems =
      [ "both_steve_providers_are_admitted"
      , "digest_matches_retains_stable_owner_subject"
      , "digest_scoped_borrow_maps_to_stable_subject"
      , "digest_candidate_bytes_remain_borrowed"
      , "blob_installed_outcome_preserves_candidate_borrow"
      , "blob_already_exists_outcome_preserves_candidate_borrow"
      , "blob_storage_failure_outcome_preserves_candidate_borrow"
      , "blob_whole_provider_layers_are_present"
      , "blob_second_installed_event_violates_no_replace"
      , "blob_partial_publication_is_forbidden"
      , "blob_overwrite_authority_is_explicitly_dispositioned"
      , "blob_delete_authority_is_explicitly_dispositioned"
      , "digest_obligation_manifest_closes_exactly"
      , "blob_obligation_manifest_closes_exactly"
      , "digest_conditions_remain_explicit_in_evidence"
      , "digest_conditions_remain_explicit_in_admission"
      , "blob_conditions_remain_explicit_in_evidence"
      , "blob_conditions_remain_explicit_in_admission"
      , "digest_sha256_profile_remains_an_explicit_condition"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Core/SteveProviderQualificationWitness.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Core/SteveProviderQualificationWitness.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-PROV-STEVE-WITNESS-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-PROV-STEVE-WITNESS-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "This theorem family certifies the normalized PROV-016 witness facts, not SHA-256 cryptographic correctness, concrete filesystem/object-store behavior, crash/interference truth, universal completeness of BlobProvider state/law/lifecycle models, canonical SemanticForm serialization, content-addressed identity construction, concrete Text/Map/Set enumeration, or exact Haskell diagnostics. The concrete Steve materializer-to-normalized-proof correspondence is checked by the PROV-016 corpus. Complete ArchitectureInstance/ArchitectureRealization construction, Systems/StageContract integration, lowering/backend correctness, deployment enforcement, and generic consume/reconstruct data-subject transport remain separate obligations. Aggregate PHIL-PROV-STEVE-001 therefore remains open while its aggregate authority/data-subject dependency is open."
  }

certifyWith :: RocqCertificationSpec -> FilePath -> FilePath -> FilePath -> IO ()
certifyWith spec sourcePath compiledPath outputPath = do
  sourceBytes <- ByteString.readFile sourcePath
  compiledBytes <- ByteString.readFile compiledPath
  case packageTrustedRocqProof spec sourceBytes compiledBytes of
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
