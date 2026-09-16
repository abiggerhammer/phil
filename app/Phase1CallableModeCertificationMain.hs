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
      certifyWith phase1CallableModeCertificationSpec sourcePath compiledPath outputPath
    _ -> do
      hPutStrLn stderr
        "usage: Phase1CallableModeCertificationMain SOURCE.v COMPILED.vo OUTPUT.cert"
      exitFailure

phase1CallableModeCertificationSpec :: RocqCertificationSpec
phase1CallableModeCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "phase1-callable-mode"
  , rocqSpecObligation = ObligationId "PHIL-CALL-MODE-001"
  , rocqSpecClaim =
      "Closure capture ownership reuses Phil's structural mode algebra: unrestricted captures require no structural move privilege; affine and linear capture occurrences must move into the sealed closure environment, are recorded as moved restricted predecessors, and the same restricted semantic occurrence cannot be captured twice. Closure structural mode is the least upper bound of captured modes under unrestricted < affine < linear and is independent of capture enumeration order."
  , rocqSpecKind = "Callable capture ownership and closure structural mode"
  , rocqSpecOrigin =
      "src/Phil/Core/Callable.hs::{checkClosureCaptures,closureStructuralMode}; test/Phase1CallableCaptureEffectsMain.hs; proof/Phil/Core/GenericStructural.v; proof/Phil/Core/CallableMode.v"
  , rocqSpecScope =
      "Phase 1 CALL-001 through CALL-003 closure capture ownership and structural mode only"
  , rocqSpecRepresentation =
      "normalized semantic capture occurrence atoms, copy/move transfer, imported structural Mode, pairwise restricted-occurrence uniqueness, and least-upper-bound mode aggregation"
  , rocqSpecSubjects =
      [ "CaptureOccurrenceKey"
      , "CaptureTransfer"
      , "ClosureCapture"
      , "ClosureCaptureSummary"
      , "Mode"
      ]
  , rocqSpecTheorems =
      [ "empty_closure_is_unrestricted"
      , "unrestricted_capture_may_copy"
      , "unrestricted_capture_may_move"
      , "accepted_affine_capture_must_move"
      , "accepted_linear_capture_must_move"
      , "affine_move_is_recorded_as_restricted_transfer"
      , "linear_move_is_recorded_as_restricted_transfer"
      , "affine_copy_is_rejected"
      , "linear_copy_is_rejected"
      , "duplicate_affine_occurrence_is_rejected"
      , "duplicate_linear_occurrence_is_rejected"
      , "distinct_occurrences_do_not_conflict"
      , "join_mode_is_commutative"
      , "join_mode_is_associative"
      , "join_mode_contains_left"
      , "join_mode_contains_right"
      , "join_mode_is_least_upper_bound"
      , "single_affine_capture_makes_affine_closure"
      , "single_linear_capture_makes_linear_closure"
      , "linear_capture_dominates_mixed_closure_mode"
      , "three_capture_mode_is_order_independent"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Core/CallableMode.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Core/CallableMode.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-CALL-MODE-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-CALL-MODE-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "PHIL-GEN-STRUCT-001 supplies the imported structural Mode algebra. Rocq kernel/toolchain correctness and reviewed correspondence from concrete CaptureOccurrenceKey/Text identity, Haskell Map/Set normalization, duplicate/restricted diagnostic ordering, and list traversal to the normalized model remain explicit trust boundaries. Source capture discovery, body/resource analysis, callable lifecycle transitions, scoped-loan escape, authority/evidence capture semantics, final syntax, and concrete target closure-environment representation remain outside this theorem family."
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
