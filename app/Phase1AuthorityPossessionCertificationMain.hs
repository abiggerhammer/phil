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
      certifyWith phase1AuthorityPossessionCertificationSpec
        sourcePath compiledPath outputPath
    _ -> do
      hPutStrLn stderr
        "usage: Phase1AuthorityPossessionCertificationMain SOURCE.v COMPILED.vo OUTPUT.cert"
      exitFailure

phase1AuthorityPossessionCertificationSpec :: RocqCertificationSpec
phase1AuthorityPossessionCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "phase1-authority-possession"
  , rocqSpecObligation = ObligationId "PHIL-AUTH-POSSESS-001"
  , rocqSpecClaim =
      "An authority-bearing operation is authorized only by an actually possessed capability whose authority contract, semantic subject, and operation permission exactly satisfy the requirement. Imports, effect permissions, runtime handles, backend symbols, and ambient registry entries do not create semantic authority. Authority-bearing values obey ordinary unrestricted/affine/linear structural copy/drop rules, and unrestricted copying preserves the exact authority contract, subject, and operation set. Authority exercise itself does not imply capability consumption."
  , rocqSpecKind = "Explicit semantic authority possession"
  , rocqSpecOrigin =
      "src/Phil/Core/Authority.hs::{checkAuthorityExercise,copyAuthorityCapability,dropAuthorityCapability}; test/Phase1AuthorityPossessionMain.hs; proof/Phil/Core/GenericStructural.v; proof/Phil/Core/AuthorityPossession.v"
  , rocqSpecScope =
      "Phase 1 pure-Phil authority possession and structural capability handling after exact capability-occurrence lookup"
  , rocqSpecRepresentation =
      "normalized exact contract/subject/operation match, explicit possession-source classification, and certified structural mode algebra"
  , rocqSpecSubjects =
      [ "AuthorityRequirement"
      , "AuthorityCapability"
      , "AuthorityExerciseSource"
      , "Mode"
      , "semantic authority contract/subject/operation"
      ]
  , rocqSpecTheorems =
      [ "exact_possessed_capability_authorizes_operation"
      , "authority_exercise_requires_exact_contract"
      , "authority_exercise_requires_exact_subject"
      , "undeclared_authority_operation_rejects"
      , "imported_declaration_is_not_possession"
      , "effect_permission_is_not_possession"
      , "runtime_handle_is_not_possession"
      , "backend_symbol_is_not_possession"
      , "ambient_registry_entry_is_not_possession"
      , "non_possession_source_never_authorizes"
      , "runtime_identity_cannot_repair_semantic_subject_mismatch"
      , "unrestricted_authority_may_be_copied"
      , "affine_authority_may_not_be_copied"
      , "linear_authority_may_not_be_copied"
      , "unrestricted_authority_may_be_dropped"
      , "affine_authority_may_be_dropped"
      , "linear_authority_may_not_be_dropped"
      , "unrestricted_copy_preserves_contract_subject_and_operations"
      , "exercise_permission_does_not_consume_possession"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Core/AuthorityPossession.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Core/AuthorityPossession.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-AUTH-POSSESS-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-AUTH-POSSESS-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "PHIL-GEN-STRUCT-001 supplies the imported structural mode algebra. Rocq kernel/toolchain correctness and reviewed correspondence from Phil.Core.Authority's concrete CapabilityOccurrenceKey/Text, AuthorityState Map lookup, operation Set membership, duplicate/stale occurrence diagnostics, and fresh-occurrence copy update to the normalized proof model remain explicit trust boundaries. Operation-specific consuming/resource transitions, attenuation, closure/provider confinement, foreign ambient-authority evidence, final syntax, and Systems lowering are outside this theorem family."
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
