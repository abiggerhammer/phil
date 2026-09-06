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
      certifyWith certificationSpec sourcePath compiledPath outputPath
    _ -> do
      hPutStrLn stderr "usage: CERTIFIER SOURCE.v COMPILED.vo OUTPUT.cert"
      exitFailure

certificationSpec :: RocqCertificationSpec
certificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "phase1-process-join"
  , rocqSpecObligation = ObligationId "PHIL-PROC-JOIN-001"
  , rocqSpecClaim =
      "Every successful process branch join has a nonempty input branch set, preserves flattened path multiplicity, preserves every Return/Closed/Failed path exactly, and normalizes every Continue path to the one successfully joined ResourceContext while preserving its non-resource checker-state payload."
  , rocqSpecKind = "Process branch control projection and path-sensitive resource normalization"
  , rocqSpecOrigin =
      "src/Phil/Core/Process.hs::{joinBranches,normalizeContinue}; test/ProcessMain.hs; proof/Phil/Core/ContextJoin.v; proof/Phil/Core/ProcessJoin.v; proof/Phil/Core/ProcessJoinCertification.v"
  , rocqSpecScope =
      "Phase 1 process-flow branch join control partition and continuing-context normalization"
  , rocqSpecRepresentation =
      "flattened process-path lists, exact Phil Control constructors, proof-model ResourceContext, and opaque non-resource CheckState payload"
  , rocqSpecSubjects =
      [ "ProcessFlow"
      , "FlowPath"
      , "Control"
      , "CheckState.resourceContext"
      , "joinBranches"
      , "normalizeContinue"
      ]
  , rocqSpecTheorems =
      [ "certified_process_join_nonempty_branch_set"
      , "certified_process_join_preserves_path_count"
      , "certified_process_join_preserves_noncontinuing"
      , "certified_process_join_normalizes_every_continue"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Core/ProcessJoinCertification.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Core/ProcessJoinCertification.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-PROC-JOIN-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-PROC-JOIN-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "The certified wrapper reuses the landed ProcessJoin.v theorem family directly and introduces no second process-join relation. PHIL-CTX-JOIN-001 supplies the ResourceContext join relation consumed by that model. The non-resource portion of CheckState is intentionally opaque: the theorem family establishes that normalization preserves that payload while changing only the resource context of Continue paths. Rocq kernel/toolchain correctness and reviewed correspondence from concrete Control payloads, Haskell CheckState record updates, list concat/filter/map behavior, exact ProcessError diagnostics, return/terminal prechecks, and branch enumeration remain explicit trust boundaries. Sequencing before the join, complete terminal resource disposal, source syntax, Systems lowering, and runtime control transfer remain outside this theorem family."
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
      putStrLn ("certified " <> Text.unpack obligation <> " as ProofAssistantTheorem evidence")
      putStrLn ("certificate artifact: " <> Text.unpack (unArtifactRef (artifactReference artifact)))
      putStrLn ("certificate sha256: " <> Text.unpack (unDigest (artifactDigest artifact)))
